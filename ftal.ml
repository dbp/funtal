open Core_kernel.Std

let replace rm r w = (r, w) :: List.Assoc.remove rm r

let rec list_replace i l x =
  if i < 0 then raise (Failure "list_replace: don't pass negative indices!") else
    match (i, l) with
    | (0, _::xs) -> x::xs
    | (_, y::xs) -> y::(list_replace (i-1) xs x)
    | (_, []) -> raise (Failure "list_replace: index larger than list")

let list_index l x =
  let rec f i l =
    match l with
    | [] -> None
    | x'::_ when x' = x -> Some i
    | _::xs -> f (i+1) xs
  in f 0 l

module Debug = struct

  let log cls msg =
    try
      let _ = Sys.getenv "DEBUG" in
      let t = Unix.localtime (Unix.time ()) in
      let open Unix in
      let (hr, min, sec, day, month, year) = (t.tm_hour, t.tm_min, t.tm_sec, t.tm_mday, t.tm_mon, t.tm_year) in
      let pref = Printf.sprintf "%04d-%02d-%02d %02d:%02d:%02d (%s): " (1900 + year) (month + 1) day hr min sec cls in
      let msg_indented = Str.global_replace (Str.regexp "\n") ("\n" ^ String.init (String.length pref) (fun _ -> ' ')) msg in
      print_endline (pref ^ msg_indented)
    with Not_found -> ()

end

module rec FTAL : sig

  val tytrans : F.t -> TAL.t
  val ft : F.t -> TAL.w -> TAL.mem -> (TAL.mem * F.exp)
  val tf : F.t -> F.exp -> TAL.mem -> (TAL.mem * TAL.w)

  type e = FC of F.exp | TC of TAL.component
  val show_e : e -> string

  type t = FT of F.t | TT of TAL.t
  val show : t -> string

  exception TypeError of string * e

  type context = TAL.psi * TAL.delta * F.gamma * TAL.chi * TAL.q * TAL.sigma

  val default_context : TAL.q -> context

  val tc : context -> e -> t * TAL.sigma

  type substitution = FTerm of string * F.exp
                    | FType of string * F.t
                    | TType of string * TAL.t
                    | SType of string * TAL.sigma
                    | EMarker of string * TAL.q

  type rebinding = SBinding of string * string
                 | FBinding of string * string
                 | TBinding of string * string
                 | EBinding of string * string

  val gen_sym : ?pref:string -> unit -> string


end = struct

  let gen_sym =
    let count = ref 0 in
    fun ?(pref="g") () -> let v = !count in count := v + 1; String.concat [pref; string_of_int v]

  let rec tytrans t =
    match t with
      F.TVar s -> TAL.TVar s
    | F.TUnit -> TAL.TUnit
    | F.TInt -> TAL.TInt
    | F.TRec (a,t) -> TAL.TRec (a, tytrans t)
    | F.TTuple ts -> TAL.TBox (TAL.PTuple (List.map ~f:tytrans ts))
    | F.TArrow (ps,t1) ->
      let zeta = gen_sym ~pref:"z" () in
      let epsilon = gen_sym ~pref:"e" () in
      TAL.TBox (TAL.PBlock ([TAL.DZeta zeta; TAL.DEpsilon epsilon],
                            [("ra", TAL.TBox (TAL.PBlock ([],
                                                          [("r1", tytrans t1)],
                                                          (TAL.SAbstract ([], zeta)),
                                                          (TAL.QEpsilon epsilon))))],
                            TAL.SAbstract (List.map ~f:tytrans ps, zeta),
                            (TAL.QR "ra")))
    | F.TArrowMod (ps, sin, sout, rt) ->
      let zeta = gen_sym ~pref:"z" () in
      let epsilon = gen_sym ~pref:"e" () in
      TAL.(TBox (PBlock ([DZeta zeta; DEpsilon epsilon],
                         [("ra", TBox (PBlock ([],
                                               [("r1", tytrans rt)],
                                               SAbstract (sout, zeta),
                                               (QEpsilon epsilon))))],
                         SAbstract (List.append
                                      (List.map ~f:tytrans ps)
                                      sin,
                                    zeta),
                         (QR "ra"))))

  let rec ft t w m =
    let (hm,rm,sm) = m in
    match (t, w) with
    | (F.TUnit, TAL.WUnit) -> (m, F.EUnit)
    | (F.TInt, TAL.WInt n) -> (m, F.EInt n)
    | (F.TTuple ts, TAL.WLoc l) ->
      begin match List.Assoc.find_exn hm l with
        | TAL.HTuple ws ->
          let (m', vs) =
            List.fold_left
              ~f:(fun (mx, b) (t,w) -> let (m'',v) = ft t w mx in (m'', v::b))
              ~init:(m, [])
              (List.zip_exn ts ws) in
          (m', F.ETuple vs)
        | _ -> raise (Failure "ft: can't convert tuple if loc isn't pointing to tuple")
      end
    | (F.TRec (a, t), TAL.WFold (a',t',w)) when tytrans (F.TRec (a,t)) = TAL.TRec (a', t') ->
      let (m', v) = ft (F.type_sub (FTAL.FType (a, F.TRec (a, t))) t) w m in
      (m', F.EFold (a, t, v))
    | (F.TArrow (ts,t1), TAL.WLoc l) ->
      let z1 = gen_sym ~pref:"z" () in
      let z2 = gen_sym ~pref:"z" () in
      let lend = gen_sym ~pref:"lend" () in
      let hend =
        TAL.HCode ([TAL.DZeta z1],
                   [("r1", tytrans t1)],
                   (TAL.SAbstract ([], z1)),
                   (TAL.QEnd (tytrans t1, TAL.SAbstract ([], z1))),
                   [TAL.Ihalt (tytrans t1, TAL.SAbstract ([], z1), "r1")]) in
      let ps = List.map ~f:(fun t -> (gen_sym ~pref:"arg" (), t)) ts in
      let v = F.ELam
          (ps, F.EBoundary
             (t1, None, (TAL.(List.concat
                          [[Iprotect ([], z2)];
                           (List.concat (List.map ~f:(fun (x,xt) ->
                                [Iimport ("r1", SAbstract ([], z2), xt, F.EVar x);
                                 Isalloc 1;
                                 Isst (0, "r1")]) ps));
                           [Imv ("ra", UApp (UW (WLoc lend), [OS (SAbstract ([], z2))]));
                            Ijmp (UApp (UW w, [OS (SAbstract ([], z2));
                                               OQ (QEnd (tytrans t1, SAbstract ([], z2)))]))]],
                        []))))
      in (((lend, hend)::hm,rm,sm), v)
    | (F.TArrowMod (ts,sin,sout,t1), TAL.WLoc l) ->
      let lend = gen_sym ~pref:"lend" () in
      let z1 = gen_sym ~pref:"z" () in
      let z2 = gen_sym ~pref:"z" () in
      let hend =
        TAL.HCode ([TAL.DZeta z1],
                   [("r1", tytrans t1)],
                   TAL.SAbstract (sin, z1),
                   (TAL.QEnd (tytrans t1, TAL.SAbstract (sout, z1))),
                   [TAL.Ihalt (tytrans t1, TAL.SAbstract (sout, z1), "r1")]) in
      let ps = List.map ~f:(fun t -> (gen_sym ~pref:"arg" (), t)) ts in
      let v = F.ELamMod
          (ps, sin, sout, F.EBoundary
             (t1, None, (TAL.(List.concat
                          [(List.concat (List.map ~f:(fun (x,xt) ->
                               [Iprotect (sin, z2);
                                Iimport ("r1", SAbstract (sin, z2), xt, F.EVar x);
                                Isalloc 1;
                                Isst (0, "r1")]) ps));
                           [Imv ("ra", UApp (UW (WLoc lend),
                                             [OS (SAbstract (sout, z2))]));
                            Ijmp (UApp (UW w, [OS (SAbstract (sin, z2));
                                               OQ (QEnd (tytrans t1, SAbstract (sout, z2)))]))]],
                        []))))
      in (((lend, hend)::hm,rm,sm), v)
    | _ -> raise (Failure "ft: can't convert")

  let rec tf t v m =
    let (hm,rm,sm) = m in
    match (t, v) with
    | (F.TUnit, F.EUnit) -> (m, TAL.WUnit)
    | (F.TInt, F.EInt n) -> (m, TAL.WInt n)
    | (F.TTuple ts, F.ETuple es) ->
      let ((hm',rm',sm'), ws) = List.fold_left
          ~f:(fun (mx, b) (t,v) -> let (m'', w) = tf t v mx in (m'', w::b))
          ~init:(m, [])
          (List.zip_exn ts es) in
      let l = gen_sym ~pref:"loc" () in
      (((l,TAL.HTuple ws)::hm',rm',sm'), TAL.WLoc l)
    | (F.TRec (a,t), F.EFold (a',t',e)) when (a',t') = (a,t) ->
      let (m', w) = tf (F.type_sub (FTAL.FType (a, F.TRec (a,t))) t) e m in
      (m', TAL.WFold (a,tytrans t,w))
    | (F.TArrow (ts,t1), F.ELam (ps,body)) ->
      let l = gen_sym ~pref:"lf" () in
      let e = gen_sym ~pref:"e" () in
      let z1 = gen_sym ~pref:"z" () in
      let s' = TAL.SAbstract (List.map ~f:tytrans ts, z1) in
      let s = TAL.(SAbstract ((TBox (PBlock ([], [("r1", tytrans t1)],
                                             SAbstract ([], z1), QEpsilon e))) ::
                              List.map ~f:tytrans ts, z1)) in
      let body_wrapped =
        let n = List.length ts in
        F.EApp (F.ELam (ps,body),
                List.mapi ~f:(fun i t' ->
                    F.EBoundary (t', Some s, ([TAL.Isld ("r1", n-i);
                                               TAL.Ihalt (tytrans t1, s, "r1")], [])))
                  (List.map ~f:snd ps))
      in
      let instrs = TAL.([Isalloc 1; Isst (0, "ra");
                         Iimport ("r1", SAbstract ([], z1), t1, body_wrapped);
                         Isld ("ra",0); Isfree (List.length ts + 1); Iret ("ra", "r1")]) in
      let h =
        TAL.(HCode
               ([DZeta z1; DEpsilon e],
                [("ra", TBox (PBlock ([], [("r1", tytrans t1)], SAbstract ([], z1), QEpsilon e)))],
                s',
                QR "ra",
                instrs))
      in
      (((l,h)::hm,rm,sm), TAL.WLoc l)

    | (F.TArrowMod (ts,sin,sout,t1), F.ELamMod (ps,sin',sout',body))
      when sin = sin && sout = sout' ->
      let l = gen_sym ~pref:"lf" () in
      let e = gen_sym ~pref:"e" () in
      let z1 = gen_sym ~pref:"z" () in
      let s' = TAL.SAbstract (List.map ~f:tytrans ts, z1) in
      let s = TAL.(SAbstract ((TBox (PBlock ([], [("r1", tytrans t1)],
                                             SAbstract ([], z1), QEpsilon e))) ::
                              List.map ~f:tytrans ts, z1)) in

      let body_wrapped =
        let n = List.length ts in
        F.EApp (F.ELamMod (ps,sin,sout,body),
                List.mapi ~f:(fun i t' ->
                    F.EBoundary (t', Some s, ([TAL.Isld ("r1", n-i);
                                               TAL.Ihalt (tytrans t1, s, "r1")], [])))
                  (List.map ~f:snd ps))
      in
      let instrs = TAL.([Isalloc 1; Isst (0, "ra"); Iimport ("r1", SAbstract ([], z1), t1, body_wrapped);
                         Isld ("ra",0); Isfree (List.length ts + 1); Iret ("ra", "r1")]) in
      let h =
        TAL.(HCode
               ([DZeta z1; DEpsilon e],
                [("ra", TBox (PBlock ([], [("r1", tytrans t1)], SAbstract ([], z1), QEpsilon e)))],
                s',
                QR "ra",
                instrs))
      in
      (((l,h)::hm,rm,sm), TAL.WLoc l)
    | _ -> raise (Failure "tf: can't convert")



  type e = FC of F.exp | TC of TAL.component
  [@@deriving show]

  type t = FT of F.t | TT of TAL.t
  [@@deriving show]


  type substitution = FTerm of string * F.exp
                    | FType of string * F.t
                    | TType of string * TAL.t
                    | SType of string * TAL.sigma
                    | EMarker of string * TAL.q

  type rebinding = SBinding of string * string
                 | FBinding of string * string
                 | TBinding of string * string
                 | EBinding of string * string

  exception TypeError of string * e
  exception TypeErrorU of string * TAL.u
  exception TypeErrorW of string * TAL.w

  type context = TAL.psi * TAL.delta * F.gamma * TAL.chi * TAL.q * TAL.sigma

  let default_context q = ([],[],[],[],q,TAL.SConcrete [])

  let get_env (_,_,g,_,_,_) = g
  let set_env (p,d,_,c,q,s) g = (p,d,g,c,q,s)

  let get_ret (_,_,_,_,q,_) = q
  let set_ret (p,d,g,c,_,s) q = (p,d,g,c,q,s)

  let get_stack (_,_,_,_,_,s) = s
  let set_stack (p,d,g,c,q,_) s = (p,d,g,c,q,s)

  let get_reg (_,_,_,c,_,_) = c
  let set_reg (p,d,g,_,q,s) c = (p,d,g,c,q,s)

  let get_heap (p,_,_,_,_,_) = p
  let set_heap (_,d,g,c,q,s) p = (p,d,g,c,q,s)


  let rec tc (context:context) e = match e with
    | FC exp -> begin
        let tc' e = tc context (FC e) in
        let show_type = show in
        let open F in
        match exp, get_ret context with
        | EVar i, TAL.QOut -> begin match List.Assoc.find (get_env context) i with
            | Some v -> (FT v, get_stack context)
            | None -> raise (TypeError ("Variable not in scope", e))
          end
        | EUnit, TAL.QOut  -> (FT TUnit, get_stack context)
        | EInt _, TAL.QOut -> (FT TInt, get_stack context)
        | EBinop (e1,_,e2), TAL.QOut ->
          begin match tc' e1 with
            | (FT TInt, s1) -> begin match tc (set_stack context s1) (FC e2) with
                | (FT TInt, s2) -> (FT TInt, s2)
                | _ -> raise (TypeError ("Second argument to binop not integer", e))
              end
            | _ -> raise (TypeError ("First argument to binop not integer", e))
          end
        | EIf0 (c,e1,e2), TAL.QOut ->
          begin match tc' c with
            | FT TInt, s1 -> begin match tc (set_stack context s1) (FC e1) with
                | FT t1, s2 -> begin match tc (set_stack context s2) (FC e2) with
                    | FT t2, s3 -> if t_eq t1 t2 && s2 = s3 then (FT t1, s2) else
                        raise (TypeError ("If branches not same type", e))
                    | _ -> raise (TypeError ("If else branch not F expression", e))
                  end
                | _ -> raise (TypeError ("If then branch not F expression", e))
              end
            | _ -> raise (TypeError ("If condition not an integer", e))
          end
        | ELam (ps,b), TAL.QOut ->
          let zeta = TAL.SAbstract ([], gen_sym ~pref:"z" ()) in
          begin match tc (set_stack (set_env context (List.append ps (get_env context))) zeta)
                        (FC b) with
          | (FT t, zeta') when zeta = zeta' -> (FT (TArrow (List.map ~f:snd ps, t)), get_stack context)
          | (FT _, _) -> raise (TypeError ("Function body does not preserve stack", e))
          | _ -> raise (TypeError ("Function body not F code", e))
          end
        | ELamMod (ps,sin,sout,b), TAL.QOut ->
          let z = gen_sym ~pref:"z" () in
          let zeta = TAL.SAbstract (sin, z) in
          let zeta_out = TAL.SAbstract (sout, z) in
          begin match tc (set_stack (set_env context (List.append ps (get_env context))) zeta)
                        (FC b) with
          | (FT t, zeta') when zeta_out = zeta' -> (FT (TArrow (List.map ~f:snd ps, t)), get_stack context)
          | (FT _, _) -> raise (TypeError ("Function body manipulates stack in illegal way", e))
          | _ -> raise (TypeError ("Function body not F code", e))
          end
        | EApp (f,args), TAL.QOut -> begin match tc' f with
            | FT (TArrow (ps, rv)), s ->
              let _ = Debug.log "tc app" ("f: " ^ show_type (fst (tc' f))) in
              let _ = Debug.log "tc app" ("args: " ^ (String.concat ~sep:";\n" (List.map ~f:(fun e -> show_type (fst (tc' e))) args))) in
              if List.length ps <> List.length args then
                raise (TypeError ("Applying function to wrong number of args", e))
              else
                (FT rv, List.fold_left ~f:(fun s0 (t,e) -> match tc (set_stack context s0) (FC e) with
                     | FT t', s1 when t_eq t t' -> s1
                     | _ -> raise (TypeError ("Argument to application did not have correct type", FC e))) ~init:s (List.zip_exn ps args))
            | t ->
              let _ = Debug.log "tc gamma" (F.show_gamma (get_env context)) in
              let _ = Debug.log "tc apply non-function" (F.show_exp f ^ " : " ^ show_type (fst t)) in
              raise (TypeError ("Applying non-function", e))
          end
        | EFold (a,t,e), TAL.QOut ->
          begin match tc' e with
            | FT t', s -> if F.t_eq t' (F.type_sub (FTAL.FType (a, TRec (a,t))) t) then (FT (TRec (a,t)), s)
              else
                let _ = Debug.log "tc fold" (show t' ^ " <>\n" ^ show (F.type_sub (FTAL.FType (a, TRec (a,t))) t)) in
                raise (TypeError ("Type of fold doesn't match declared type", FC e))
            | _ -> raise (TypeError ("Body of fold isn't F expression", FC e))
          end
        | EUnfold e, TAL.QOut -> begin match tc' e with
            | FT (TRec (a,t)), s -> (FT (F.type_sub (FTAL.FType (a, TRec (a,t))) t), s)
            | _ -> raise (TypeError ("Unfolding a non recursive type", FC e))
          end
        | ETuple es, TAL.QOut ->
          begin match List.fold_left ~f:(fun (l,s0) e -> match tc (set_stack context s0) (FC e) with
              | FT t', s1 -> (List.append l [t'], s1)
              | _ -> raise (TypeError ("Tuple element isn't an F expression", FC e))) ~init:([], get_stack context) es with
          | l,s -> (FT (TTuple l), s)
          end
        | EPi (n,e'), TAL.QOut -> begin match tc' e' with
            | FT (TTuple l), s when List.length l > n -> (FT (List.nth_exn l n), s)
            | _ -> raise (TypeError ("Applying pi to non-tuple, or with too high index", e))
          end
        | EBoundary (t,s,c), TAL.QOut ->
          let s' = Option.value ~default:(get_stack context) s in
          begin match tc (set_ret context (TAL.QEnd (tytrans t, s'))) (TC c) with
            | TT t0, s0 when TAL.t_eq t0 (tytrans t) && s0 = s' -> (FT t, s0)
            | _ -> raise (TypeError ("Boundary with contents not matching type", e))
          end
        | _ -> raise (TypeError ("F expression with invalid return marker", e))
      end
    | TC (instrs,h) ->
      (* let tc' e = tc context (FC e) in *)
      (* let show_type = show in *)
      let open TAL in
      match instrs, get_ret context with
      | Iaop (op, rd, rs, u)::is, QR r when rd = r ->
        raise (TypeError ("Iaop writing to register that is current return marker", e))
      | Iaop (op, rd, rs, u)::is, _ ->
        begin match List.Assoc.find (get_reg context) rs, tc_u context u with
          | None, _ -> raise (TypeError ("Iaop with unbound source register", e))
          | Some t, _ when t <> TInt -> raise (TypeError ("Iaop with non-integer as source", e))
          | _, t when t <> TInt -> raise (TypeError ("Iaop with non-integer as target", e))
          | _ ->
            tc (set_reg context (List.Assoc.add (get_reg context) rd TInt)) (TC (is, h))
        end
      | Imv (rd,u)::is, QR r when rd = r ->
        raise (TypeError ("Imv writing to register that is current return marker", e))
      | Imv (rd,u)::is, _ ->
        tc (set_reg context (List.Assoc.add (get_reg context) rd (tc_u context u))) (TC (is,h))
      | Iimport (rd,s,t,f)::is, QR r when rd = r ->
        raise (TypeError ("Iimport writing to register that is current return marker", e))
      | Iimport (rd,s,t,f)::is, _ ->
        (* TODO(dbp 2017-02-16): Need to hide tail. *)
        if tc (set_ret context QOut) (FC f) = (FT t,s)
        then tc (set_stack (set_reg context (List.Assoc.add (get_reg context) rd (tytrans t))) s) (TC (is,h))
        else raise (TypeError ("Iimport given F expression of the wrong type", e))
      | [Ihalt (t,s,r)], QEnd (t',s') when t' <> t || s <> s' ->
        raise (TypeError ("Halt instruction annotations don't match return marker", e))
      | [Ihalt (t,s,r)], QEnd _ when s <> get_stack context ->
        raise (TypeError ("Halt instruction annotations don't match current stack", e))
      | [Ihalt (t,s,r)], QEnd _ ->
        if List.Assoc.find (get_reg context) r = Some t
        then (TT t,s)
        else raise (TypeError ("Halting with wrong type in return register", e))
      | [Ihalt _], _ ->
        raise (TypeError ("Halting without end return marker", e))
      | Isalloc n ::is, _ ->
        tc (set_stack context (List.fold_left ~f:(fun s _ -> stack_cons TUnit s) ~init:(get_stack context) (List.init ~f:(fun x -> x) n))) (TC (is,h))


      | _ -> raise (TypeError ("Don't know how to type-check", e))

        (* | Ibnz of reg * u *)
        (* | Ild of reg * reg * int *)
        (* | Ist of reg * int * reg *)
        (* | Iralloc of reg * int *)
        (* | Iballoc of reg * int *)
        (* | Iunpack of string * reg * u *)
        (* | Iunfold of reg * u *)
        (* | Isfree of int *)
        (* | Isld of reg * int *)
        (* | Isst of int * reg *)
        (* | Ijmp of u *)
        (* | Icall of u * sigma * q *)
        (* | Iret of reg * reg *)
        (* | Iprotect of sigma_prefix * string *)
        (* | Iimport of reg * sigma * F.t * F.exp *)

  and tc_u context u = let open TAL in match u with
    | UW w -> tc_w context w
    | UR r -> begin match List.Assoc.find (get_reg context) r with
        | None -> raise (TypeErrorU ("Unbound register", u))
        | Some t -> t
      end
    | UPack (t, u, s, t') ->
      if tc_u context u = type_sub (TType (s,t')) t
      then TExists (s,t')
      else raise (TypeErrorU ("Ill-typed existential", u))
    | UFold (s,t,u) ->
      if tc_u context u = type_sub (TType (s, TRec (s, t))) t
      then TRec (s,t)
      else raise (TypeErrorU ("Ill-typed fold", u))
    | UApp (u, os) ->
      begin match tc_u context u with
        | TBox (PBlock (d,c,s,q)) ->
          let (ds,dr) = List.split_n d (List.length os) in
          List.fold_left ~f:(fun t' p -> type_sub p t') ~init:(TBox (PBlock (dr,c,s,q))) (type_zip ds os)
        | _ -> raise (TypeErrorU ("Can't apply non-block to types", u))
      end

  and tc_w context w = let open TAL in match w with
    | WUnit -> TUnit
    | WInt _ -> TInt
    | WLoc l ->
      begin match List.Assoc.find (get_heap context) l with
        | None -> raise (TypeErrorW ("Unbound location", w))
        | Some t -> TBox t
      end
    | WPack (t, w, s, t') ->
      if tc_w context w = type_sub (TType (s,t')) t
      then TExists (s,t')
      else raise (TypeErrorW ("Ill-typed existential", w))
    | WFold (s,t,w) ->
      if tc_w context w = type_sub (TType (s, TRec (s, t))) t
      then TAL.TRec (s,t)
      else raise (TypeErrorW ("Ill-typed fold", w))
    | WApp (w, os) ->
      begin match tc_w context w with
        | TBox (PBlock (d,c,s,q)) ->
          let (ds,dr) = List.split_n d (List.length os) in
          List.fold_left ~f:(fun t' p -> type_sub p t') ~init:(TBox (PBlock (dr,c,s,q))) (type_zip ds os)
        | _ -> raise (TypeErrorW ("Can't apply non-block to types", w))
      end

end
and F : sig

  type t =
    TVar of string
    | TUnit
    | TInt
    | TArrow of t list * t
    | TArrowMod of t list * TAL.sigma_prefix * TAL.sigma_prefix * t
    | TRec of string * t
    | TTuple of t list
  val show : t -> string
  val pp : Format.formatter -> t -> unit
  val t_eq : t -> t -> bool

  type binop = BPlus | BMinus | BTimes
  val show_binop : binop -> string

  type exp =
      EVar of string
    | EUnit
    | EInt of int
    | EBinop of exp * binop * exp
    | EIf0 of exp * exp * exp
    | ELam of (string * t) list * exp
    | ELamMod of (string * t) list * TAL.sigma_prefix * TAL.sigma_prefix * exp
    | EApp of exp * exp list
    | EFold of string * t * exp
    | EUnfold of exp
    | ETuple of exp list
    | EPi of int * exp
    | EBoundary of t * TAL.sigma option * TAL.component
  val show_exp : exp -> string
  val pp_exp : Format.formatter -> exp -> unit

  type context =
      CHole
    | CBinop1 of context * binop * exp
    | CBinop2 of exp * binop * context
    | CIf0 of context * exp * exp
    | CApp1 of context * exp list
    | CAppn of exp * exp list * context * exp list
    | CFold of string * t * context
    | CUnfold of context
    | CTuple of exp list * context * exp list
    | CPi of int * context
    | CBoundary of t * TAL.sigma option * TAL.context
  val show_context : context -> string
  val pp_context : Format.formatter -> context -> unit

  val value : exp -> bool

  val sub : FTAL.substitution -> exp -> exp
  val type_sub : FTAL.substitution -> t -> t

  type ft = F of exp | TC of TAL.component | TI of TAL.instr list
  val show_ft : ft -> string

  val plug : context -> ft -> exp

  val decomp : exp -> (context * F.ft) option

  val step : TAL.mem * exp -> TAL.mem * exp

  val stepn : int -> TAL.mem * exp -> TAL.mem * exp

  type gamma = (string * F.t) list
  val show_gamma : gamma -> string

end = struct

  type t =
    TVar of string
    | TUnit
    | TInt
    | TArrow of t list * t
    | TArrowMod of t list * TAL.sigma_prefix * TAL.sigma_prefix * t
    | TRec of string * t
    | TTuple of t list
  [@@deriving show]

  type binop = BPlus | BMinus | BTimes
  [@@deriving show]

  type exp =
      EVar of string
    | EUnit
    | EInt of int
    | EBinop of exp * binop * exp
    | EIf0 of exp * exp * exp
    | ELam of (string * t) list * exp
    | ELamMod of (string * t) list * TAL.sigma_prefix * TAL.sigma_prefix * exp
    | EApp of exp * exp list
    | EFold of string * t * exp
    | EUnfold of exp
    | ETuple of exp list
    | EPi of int * exp
    | EBoundary of t * TAL.sigma option * TAL.component
  [@@deriving show]

  let rec value e =
    match e with
    | EUnit -> true
    | EInt _ -> true
    | ELam _ -> true
    | ELamMod _ -> true
    | EFold _ -> true
    | ETuple es -> List.for_all ~f:value es
    | _ -> false

  type context =
      CHole
    | CBinop1 of context * binop * exp
    | CBinop2 of exp * binop * context
    | CIf0 of context * exp * exp
    | CApp1 of context * exp list
    | CAppn of exp * exp list * context * exp list
    | CFold of string * t * context
    | CUnfold of context
    | CTuple of exp list * context * exp list
    | CPi of int * context
    | CBoundary of t * TAL.sigma option * TAL.context
  [@@deriving show]

  type env = (string * t) list

  let rec type_sub p typ = match typ with
    | TVar a -> begin match p with
        | FTAL.FType (a', t) when a = a' -> t
        | _ -> typ
      end
    | TArrow (params,ret) ->
      TArrow (List.map ~f:(type_sub p) params, type_sub p ret)
    | TArrowMod (params, sin, sout, ret) ->
      TArrowMod (List.map ~f:(type_sub p) params, List.map ~f:(TAL.type_sub p) sin, List.map ~f:(TAL.type_sub p) sout, type_sub p ret)
    | TRec (a, t) -> begin match p with
        | FTAL.FType (a', t) when a = a' -> typ
        | _ -> TRec (a, type_sub p t)
      end
    | TTuple ts -> TTuple (List.map ~f:(type_sub p) ts)
    | _ -> typ

  let rec type_rebind bind t = match t with
    | TArrow (params,ret) -> TArrow (List.map ~f:(type_rebind bind) params, type_rebind bind ret)
    | TArrowMod (params,sin,sout,ret) ->
      TArrowMod (List.map ~f:(type_rebind bind) params,
                 List.map ~f:(TAL.type_rebind bind) sin,
                 List.map ~f:(TAL.type_rebind bind) sout,
                 type_rebind bind ret)
    | TRec (a, t) -> begin match bind with
        | FTAL.FBinding (a1, a2) when a = a1 ->
          TRec (a2, type_sub (FTAL.FType (a, F.TVar a2)) t)
        | _ -> TRec (a, type_rebind bind t)
      end
    | TTuple ts -> TTuple (List.map ~f:(type_rebind bind) ts)
    | TVar a -> begin match bind with
        | FTAL.FBinding (a1,a2) when a = a1 -> TVar a2
        | _ -> t
      end
    | _ -> t


  let rec t_eq t1 t2 = match t1, t2 with
    | TVar v1, TVar v2 -> v1 = v2
    | TUnit, TUnit -> true
    | TInt, TInt -> true
    | TArrow (ps1, r1), TArrow (ps2, r2) ->
      List.for_all2_exn ~f:t_eq ps1 ps2 &&
      t_eq r1 r2
    | TArrowMod (ps1, sin1, sout1, r1), TArrowMod (ps2, sin2, sout2, r2) ->
      List.for_all2_exn ~f:t_eq ps1 ps2 &&
      List.for_all2_exn ~f:TAL.t_eq sin1 sin2 &&
      List.for_all2_exn ~f:TAL.t_eq sout1 sout2 &&
      t_eq r1 r2
    | TRec (s1, b1), TRec (s2, b2) ->
      t_eq b1 (type_rebind (FTAL.FBinding (s2, s1)) b2)
    | TTuple ts, TTuple ts1 -> List.for_all2_exn ~f:t_eq ts ts1
    | _ -> false


  let rec sub p e =
    match e with
    | EVar x -> begin match p with
        | FTAL.FTerm (x', e') when x = x' -> e'
        | _ -> e
      end
    | EUnit -> e
    | EInt _ -> e
    | EBinop (e1, b, e2) -> EBinop (sub p e1, b, sub p e2)
    | EIf0 (e1, e2, e3) -> EIf0 (sub p e1, sub p e2, sub p e3)
    | ELam (args, body) ->
      begin match p with
        | FTAL.FTerm (x', e') when List.Assoc.mem args x' -> e
        | _ -> ELam (args, sub p body)
      end
    | ELamMod (args, sin, sout, body) ->
      begin match p with
        | FTAL.FTerm (x', e') when List.Assoc.mem args x' -> e
        | _ -> ELamMod (args, sin, sout, sub p body)
      end
    | EApp (e1, eargs) ->
      EApp (sub p e1, List.map ~f:(sub p) eargs)
    | EFold (s, t, e1) ->
      begin match p with
        | FTAL.FType (a, t') when a = s -> e
        | _ -> EFold (s, t, sub p e1)
      end
    | EUnfold e1 -> EUnfold (sub p e1)
    | ETuple es -> ETuple (List.map ~f:(sub p) es)
    | EPi (n, e1) -> EPi (n, sub p e1)
    | EBoundary (t, s, comp) -> EBoundary (type_sub p t, Option.(s >>| TAL.stack_sub p), TAL.sub p comp)

  let step_prim (m, e) =
    match e with
    | EBinop (EInt n1, BPlus, EInt n2) -> (m, EInt (n1 + n2))
    | EBinop (EInt n1, BMinus, EInt n2) -> (m, EInt (n1 - n2))
    | EBinop (EInt n1, BTimes, EInt n2) -> (m, EInt (n1 * n2))
    | EIf0 (EInt 0, e2, e3) -> (m, e2)
    | EIf0 (EInt _, e2, e3) -> (m, e3)
    | EApp (ELam (ps, body), eargs) when List.(length ps = length eargs) ->
      (m, List.fold_left ~f:(fun e p -> sub p e) ~init:body (List.map2_exn ~f:(fun (x,_) e -> FTAL.FTerm (x,e)) ps eargs))
    | EApp (ELamMod (ps, sin, sout, body), eargs) when List.(length ps = length eargs) ->
      (m, List.fold_left ~f:(fun e p -> sub p e) ~init:body (List.map2_exn ~f:(fun (x,_) e -> FTAL.FTerm (x,e)) ps eargs))
    | EUnfold (EFold (_,_,eb)) -> (m, eb)
    | EPi (n, (ETuple vs)) when List.length vs > n -> (m, List.nth_exn vs n)
    (* NOTE(dbp 2016-10-13): FTAL.tytrans t = t' should hold as well,
       but tytrans gen_syms so we need some sort of alpha equivalence (or
       to just fix how we do names). *)
    | EBoundary (t, s, ([TAL.Ihalt (t',s',r)],[]))->
      let (hm,rm,sm) = m in
      FTAL.ft t (List.Assoc.find_exn rm r) m
    | _ -> (m, e)

  let split_at f l =
    let rec split_at' f acc l =
      match l with
      | []    -> (acc, None, [])
      | x::xs -> if f x then (List.rev acc, Some x, xs) else split_at' f (x::acc) xs
    in split_at' f [] l

  let is_some = function | None -> false
                         | Some _ -> true

  type ft = F of exp | TC of TAL.component | TI of TAL.instr list
  [@@deriving show]

  let rec decomp e =
    match e with
    | EVar _ -> None
    | EUnit -> None
    | EInt _ -> None
    | ELam _ -> None
    | EFold _ -> None

    | EBinop (e1, b, e2) when not (value e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CBinop1 (ctxt, b, e2), e'))
    | EBinop (e1, b, e2) when value e1 && not (value e2) ->
      decomp_cont e2 (fun ctxt e' -> Some (CBinop2 (e1, b, ctxt), e'))
    | EBinop (e1, b, e2) when value e1 && value e2 -> Some (CHole, F e)

    | EIf0 (e1, e2, e3) when not (value e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CIf0 (ctxt, e2, e3), e'))
    | EIf0 (e1, e2, e3) when value e1 ->
      Some (CHole, F e)

    | EApp (e1, eargs) when not (value e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CApp1 (ctxt, eargs), e'))
    | EApp (e1, eargs) when value e1 && List.exists ~f:(fun x -> not (value x)) eargs ->
      decomp_list eargs (fun bef ctxt aft e' -> Some (CAppn (e1, bef, ctxt, aft), e'))
    | EApp (e1, eargs) -> Some (CHole, F e)

    | EUnfold e1 when value e1 -> Some (CHole, F e)
    | EUnfold e1 -> decomp_cont e1 (fun ctxt e' -> Some (CUnfold ctxt, e'))

    | ETuple es ->
      decomp_list es (fun bef ctxt aft e' -> Some (CTuple (bef, ctxt, aft), e'))

    | EPi (n, e1) when value e1 -> Some (CHole, F e)
    | EPi (n, e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CPi (n, ctxt), e'))

    | EBoundary (t, s, comp) ->
      begin match TAL.decomp comp with
          None -> Some (CHole, F e)
        | Some (ctxt, e') -> Some (CBoundary (t, s, ctxt), e')
      end

    | _ -> None
  and decomp_cont e f =
    match decomp e with
    | None -> None
    | Some (ctxt, e') -> f ctxt e'
  and decomp_list es f =
    match split_at
                (fun x -> is_some (snd x))
                (List.map ~f:(fun ea -> (ea, decomp ea)) es) with
    | (bef, Some (_, Some (ctxt, e')), aft) ->
      f (List.map ~f:fst bef) ctxt (List.map ~f:fst aft) e'
    | _ -> None

  let un_f = function
    | F e -> e
    | TI is -> raise (Failure "trying to plug an instruction list into an f context")
    | TC is -> raise (Failure "trying to plug a tal component into an f context")

  let rec plug ctxt e =
    match ctxt with
    | CHole -> un_f e
    | CBinop1 (ctxt', b, e1) -> EBinop (plug ctxt' e, b, e1)
    | CBinop2 (e1, b, ctxt') -> EBinop (e1, b, plug ctxt' e)
    | CIf0 (ctxt', e1, e2) -> EIf0 (plug ctxt' e, e1, e2)
    | CApp1 (ctxt', es) -> EApp (plug ctxt' e, es)
    | CAppn (ef, bef, ctxt', aft) -> EApp (ef, List.concat [bef; [plug ctxt' e]; aft])
    | CFold (s, t, ctxt') -> EFold (s, t, plug ctxt' e)
    | CUnfold ctxt' -> EUnfold (plug ctxt' e)
    | CTuple (bef, ctxt', aft) -> ETuple (List.concat [bef; [plug ctxt' e]; aft])
    | CPi (n, ctxt') -> EPi (n, plug ctxt' e)
    | CBoundary (t,s,talctxt) -> EBoundary (t, s, TAL.plug talctxt e)

  let step (m, e) =
    let (h,r,s) = m in
    match decomp e with
    | Some (ctxt, F e') ->
      let _ = Debug.log "decomp F ctxt" (F.show_context ctxt) in
      let _ = Debug.log "decomp F exp" (F.show_exp e') in
      let (m', e'') = step_prim (m, e') in
      let _ = Debug.log "stepped F exp" (F.show_exp e'') in
      (m', plug ctxt (F e''))
    | Some (ctxt, TI is) ->
      let () = Debug.log "decomp TI ctxt" (F.show_context ctxt) in
      let _ = Debug.log "decomp TI instrs" (String.concat ~sep:"; " (List.map ~f:(fun i -> TAL.show_instr i) is)) in
      let _ = Debug.log "decomp TI regs" (TAL.show_regm r) in
      let _ = Debug.log "decomp TI stack" (TAL.show_stackm s) in
      let (m', is') = TAL.reduce (m, is) in
      let (h',r',s') = m' in
      let _ = Debug.log "stepped TI instrs" (String.concat ~sep:"; " (List.map ~f:(fun i -> TAL.show_instr i) is')) in
      let _ = Debug.log "stepped TI regs" (TAL.show_regm r') in
      let _ = Debug.log "stepped TI stack" (TAL.show_stackm s') in
      let _ = Debug.log "stepped TI heap" (TAL.show_heapm h') in
      (m', plug ctxt (TI is'))
    | Some (ctxt, TC (is,h)) ->
      let m' = TAL.load m h in
      (m', plug ctxt (TC (is, [])))
    | None -> (m, e)

  let rec stepn n e =
    let () = Debug.log "step" (string_of_int n) in
    match n with
    | 0 -> e
    | n -> stepn (n - 1) (step e)


  type gamma = (string * F.t) list
  [@@deriving show]

end
and TAL : sig

  type reg = string
  type loc = string

  type delta_elem =
      DAlpha of string
    | DZeta of string
    | DEpsilon of string
  val show_delta_elem : delta_elem -> string

  type delta = delta_elem list

  type t =
      TVar of string
    | TUnit
    | TInt
    | TExists of string * t
    | TRec of string * t
    | TTupleRef of t list
    | TBox of psi_elem

  and sigma =
      SAbstract of sigma_prefix * string
    | SConcrete of sigma_prefix

  and sigma_prefix = t list

  and q =
      QR of reg
    | QI of int
    | QEpsilon of string
    | QEnd of t * sigma
    | QOut

  and psi_elem =
      PBlock of delta * chi * sigma * q
    | PTuple of t list

  and psi = (loc * psi_elem) list

  and chi = (reg * t) list

  val stack_cons : t -> sigma -> sigma

  val show : t -> string
  val pp : Format.formatter -> t -> unit
  val t_eq : t -> t -> bool
  val show_sigma : sigma -> string
  val pp_sigma : Format.formatter -> sigma -> unit
  val show_sigma_prefix : sigma_prefix -> string
  val pp_sigma_prefix : Format.formatter -> sigma_prefix -> unit
  val show_q : q -> string
  val pp_q : Format.formatter -> q -> unit
  val show_psi : psi -> string
  val pp_psi : Format.formatter -> psi -> unit

  type omega =
      OT of t
    | OS of sigma
    | OQ of q
  val show_omega : omega -> string

  type w =
      WUnit
    | WInt of int
    | WLoc of loc
    | WPack of t * w * string * t
    | WFold of string * t * w
    | WApp of w * omega list
  val show_w : w -> string

  type u =
      UW of w
    | UR of reg
    | UPack of t * u * string * t
    | UFold of string * t * u
    | UApp of u * omega list
  val show_u : u -> string

  type aop = Add | Sub | Mult
  val show_aop : aop -> string

  type instr =
      Iaop of aop * reg * reg * u
    | Ibnz of reg * u
    | Ild of reg * reg * int
    | Ist of reg * int * reg
    | Iralloc of reg * int
    | Iballoc of reg * int
    | Imv of reg * u
    | Iunpack of string * reg * u
    | Iunfold of reg * u
    | Isalloc of int
    | Isfree of int
    | Isld of reg * int
    | Isst of int * reg
    | Ijmp of u
    | Icall of u * sigma * q
    | Iret of reg * reg
    | Ihalt of t * sigma * reg
    | Iprotect of sigma_prefix * string
    | Iimport of reg * sigma * F.t * F.exp
  val show_instr : instr -> string
  val pp_instr : Format.formatter -> instr -> unit

  type h =
      HCode of delta * chi * sigma * q * instr list
    | HTuple of w list
  val show_h : h -> string

  type heapm = (loc * h) list
  val show_heapm : heapm -> string

  type regm = (reg * w) list
  val show_regm : regm -> string

  type stackm = w list
  val show_stackm : stackm -> string

  type mem = heapm * regm * stackm

  val load : mem -> heapm -> mem

  type component = instr list * heapm
  val show_component : component -> string
  val pp_component : Format.formatter -> component -> unit

  type context =
      CComponentEmpty of contextI
    | CComponentHeap of contextC

  and contextI =
      CHoleI
    | CImportI of reg * sigma * F.t * F.context * instr list

  and contextC =
      CHoleC

  val show_context : context -> string
  val pp_context : Format.formatter -> context -> unit
  val show_contextI : contextI -> string
  val show_contextC : contextC -> string

  val sub : FTAL.substitution -> component -> component

  val type_sub : FTAL.substitution -> t -> t

  val stack_sub : FTAL.substitution -> sigma -> sigma

  val omega_sub : FTAL.substitution -> omega -> omega

  val retmarker_sub : FTAL.substitution -> q -> q

  val type_rebind : FTAL.rebinding -> t -> t

  val type_zip : delta -> omega list -> FTAL.substitution list

  val plug : context -> F.ft -> component

  val reduce : mem * instr list -> mem * instr list

  val decomp : component -> (context * F.ft) option

end = struct

  type reg = string
  [@@deriving show]
  type loc = string
  [@@deriving show]

  type delta_elem =
      DAlpha of string
    | DZeta of string
    | DEpsilon of string
  [@@deriving show]

  type delta = delta_elem list
  [@@deriving show]

  type t =
      TVar of string
    | TUnit
    | TInt
    | TExists of string * t
    | TRec of string * t
    | TTupleRef of t list
    | TBox of psi_elem
  [@@deriving show]

  and sigma =
      SAbstract of sigma_prefix * string
    | SConcrete of sigma_prefix
  [@@deriving show]

  and sigma_prefix = t list
      [@@deriving show]

  and q =
      QR of reg
    | QI of int
    | QEpsilon of string
    | QEnd of t * sigma
    | QOut
  [@@deriving show]

  and psi_elem =
      PBlock of delta * chi * sigma * q
    | PTuple of t list
  [@@deriving show]

  and psi = (loc * psi_elem) list

  and chi = (reg * t) list

  type omega =
      OT of t
    | OS of sigma
    | OQ of q
  [@@deriving show]

  type omega_list = omega list
  [@@deriving show]

  type w =
      WUnit
    | WInt of int
    | WLoc of loc
    | WPack of t * w * string * t
    | WFold of string * t * w
    | WApp of w * omega list
  [@@deriving show]

  type u =
      UW of w
    | UR of reg
    | UPack of t * u * string * t
    | UFold of string * t * u
    | UApp of u * omega list
  [@@deriving show]

  type aop = Add | Sub | Mult
  [@@deriving show]

  type instr =
      Iaop of aop * reg * reg * u
    | Ibnz of reg * u
    | Ild of reg * reg * int
    | Ist of reg * int * reg
    | Iralloc of reg * int
    | Iballoc of reg * int
    | Imv of reg * u
    | Iunpack of string * reg * u
    | Iunfold of reg * u
    | Isalloc of int
    | Isfree of int
    | Isld of reg * int
    | Isst of int * reg
    | Ijmp of u
    | Icall of u * sigma * q
    | Iret of reg * reg
    | Ihalt of t * sigma * reg
    | Iprotect of sigma_prefix * string
    | Iimport of reg * sigma * F.t * F.exp
  [@@deriving show]

  type h =
      HCode of delta * chi * sigma * q * instr list
    | HTuple of w list
  [@@deriving show]

  type heapm = (loc * h) list
  [@@deriving show]
  type regm = (reg * w) list
  [@@deriving show]
  type stackm = w list
  [@@deriving show]
  type mem = heapm * regm * stackm

  let stack_cons t s = match s with
    | SConcrete l -> SConcrete (t::l)
    | SAbstract (l,a) -> SAbstract (t::l,a)

  let load (h,r,s) h' =
    (* NOTE(dbp 2016-09-08): We should do renaming, but relying, for now, on the fact
       that we always gensym new location names, so not renaming should be safe. *)
    (List.append h' h, r, s)

  type component = instr list * heapm
  [@@deriving show]

  type context =
      CComponentEmpty of contextI
    | CComponentHeap of contextC
  [@@deriving show]

  and contextI =
      CHoleI
    | CImportI of reg * sigma * F.t * F.context * instr list
  [@@deriving show]

  and contextC =
      CHoleC
  [@@deriving show]


  let un_ti = function
    | F.TI is -> is
    | F.TC c -> raise (Failure "trying to put a t component into t instruction hole")
    | F.F e -> raise (Failure "trying to put an f expression into t instruction hole")

  let un_tc = function
    | F.TC c -> c
    | F.TI _ -> raise (Failure "trying to put a t instruction list into t component hole")
    | F.F _ -> raise (Failure "trying to put an f expression into t instruction hole")


  let plug ctxt e =
    match ctxt with
    | CComponentEmpty ctxt' ->
      begin match ctxt' with
        | CHoleI -> (un_ti e, [])
        | CImportI (r,s,t,ctxt',is) -> (Iimport (r,s,t,F.plug ctxt' e)::is, [])
      end
    | CComponentHeap CHoleC -> un_tc e

  let rec sub p (is, hm) =
    (List.map ~f:(instr_sub p) is,
     List.map ~f:(fun (l,h) ->
         match h with
         | HCode (d,c,s,q,is) -> (l, HCode (d,c,s,q, List.map ~f:(instr_sub p) is))
         | _ -> (l,h)
       ) hm)

  and instr_sub p i = match i with
    | Iaop (op, r1, r2, u) -> Iaop (op, r1, r2, u_sub p u)
    | Ibnz (r,u) -> Ibnz (r, u_sub p u)
    | Imv (r,u) -> Imv (r, u_sub p u)
    | Iunpack (a,r,u) -> Iunpack (a,r,u_sub p u)
    | Iunfold (r,u) -> Iunfold (r, u_sub p u)
    | Ijmp u -> Ijmp (u_sub p u)
    | Icall (u,s,q) -> Icall (u_sub p u, stack_sub p s, retmarker_sub p q)
    | Ihalt (t,s,r) -> Ihalt (type_sub p t, stack_sub p s, r)
    | Iimport (r,s,t,e) -> Iimport (r,s,t,F.sub p e)
    | _ -> i

  and u_sub p u = match u with
    | UW w -> UW (w_sub p w)
    | UR r -> u
    | UPack (t',ubody,a,t) -> begin match p with
        | FTAL.TType (a', _) when a = a' ->
          UPack (type_sub p t', ubody, a, t)
        | _ -> UPack (type_sub p t', u_sub p ubody, a, type_sub p t)
      end
    | UFold (a, t, ubody) -> begin match p with
        | FTAL.TType (a', _) when a = a' -> u
        | _ -> UFold (a, type_sub p t, u_sub p ubody)
      end
    | UApp (ubody, os) -> UApp (u_sub p ubody, List.map ~f:(omega_sub p) os)

  and w_sub p w = match w with
    | WPack (t',wbody,a,t) -> begin match p with
        | FTAL.TType (a', _) when a = a' ->
          WPack (type_sub p t', wbody, a, t)
        | _ -> WPack (type_sub p t', w_sub p wbody, a, type_sub p t)
      end
    | WFold (a,t,wbody) -> begin match p with
        | FTAL.TType (a', _) when a = a' -> w
        | _ -> WFold (a, type_sub p t, w_sub p wbody)
      end
    | WApp (wbody, os) -> WApp (w_sub p wbody, List.map ~f:(omega_sub p) os)
    | _ -> w

  and psi_sub (p:FTAL.substitution) t = match t with
    | PBlock (d, x, s, q) ->
      begin match p with
        | FTAL.TType (a, t') when List.mem d (DAlpha a) -> t
        | FTAL.SType (a, s') when List.mem d (DZeta a) -> t
        | _ -> PBlock (d, List.map ~f:(fun (x,t') -> (x, type_sub p t')) x,
                       stack_sub p s, retmarker_sub p q)
      end
    | PTuple ts -> PTuple (List.map ~f:(type_sub p) ts)

  and retmarker_sub p t = match t with
    | QEpsilon a -> begin match p with
        | FTAL.EMarker (a', q) when a = a' -> q
        | _ -> t
      end
    | QEnd (t',s) -> QEnd (type_sub p t', stack_sub p s)
    | _ -> t

  and type_sub p t = match t with
    | TVar a -> begin match p with
        | FTAL.TType (a', t') when a = a' -> t'
        | _ -> t
      end
    | TExists (a,tbody) -> begin match p with
        | FTAL.TType (a', _) when a = a' -> t
        | _ -> TExists (a, type_sub p tbody)
      end
    | TRec (a,tbody) -> begin match p with
        | FTAL.TType (a', _) when a = a' -> t
        | _ -> TRec (a, type_sub p tbody)
      end
    | TTupleRef ts -> TTupleRef (List.map ~f:(type_sub p) ts)
    | TBox ps -> TBox (psi_sub p ps)
    | _ -> t

  and stack_sub p s = match s with
    | SAbstract (pref, z) -> begin match p with
        | FTAL.SType (z', s') when z = z' -> begin match s' with
            | SConcrete rest ->
              SConcrete (List.append (List.map ~f:(type_sub p) pref) rest)
            | SAbstract (some, var) ->
              SAbstract (List.append (List.map ~f:(type_sub p) pref) some, var)
          end
        | _ -> s
      end
    | SConcrete ts -> SConcrete (List.map ~f:(type_sub p) ts)

  and omega_sub p o = match o with
    | OT t -> OT (type_sub p t)
    | OS s -> OS (stack_sub p s)
    | OQ q -> OQ (retmarker_sub p q)


  let rec type_rebind bind t = match t with
    | TVar a -> begin match bind with
        | FTAL.TBinding (a1,a2) when a = a1 -> TVar a2
        | _ -> t
      end
    | TExists (a, b) -> begin match bind with
        | FTAL.TBinding (a1,a2) when a = a1 ->
          TExists (a2, type_sub (FTAL.TType (a1, TAL.TVar a2)) b)
        | _ -> TExists (a, type_rebind bind b)
      end
    | TRec (a, b) -> begin match bind with
        | FTAL.TBinding (a1,a2) when a = a1 ->
          TRec (a2, type_sub (FTAL.TType (a1, TAL.TVar a2)) b)
        | _ -> TRec (a, type_rebind bind b)
      end
    | TTupleRef ts ->
      TTupleRef (List.map ~f:(type_rebind bind) ts)
    | TBox (PBlock (d1, c1, s1, q1)) ->
      let (d2, s) = begin match bind with
        | FTAL.TBinding (a1, a2) ->
          begin match list_index d1 (DAlpha a1) with
            | None -> (d1, None)
            | Some idx ->
              (list_replace idx d1 (DAlpha a2), Some (FTAL.TType (a1, TVar a2)))
          end
        | FTAL.SBinding (z1, z2) ->
          begin match list_index d1 (DZeta z1) with
            | None -> (d1, None)
            | Some idx ->
              (list_replace idx d1 (DZeta z2), Some (FTAL.SType (z1, SAbstract ([], z2))))
          end
        | FTAL.EBinding (e1, e2) ->
          begin match list_index d1 (DEpsilon e1) with
            | None -> (d1, None)
            | Some idx ->
              (list_replace idx d1 (DEpsilon e2), Some (FTAL.EMarker (e1, QEpsilon e2)))
          end
        | _ -> (d1, None)
      end in
      begin match s with
        | None -> t
        | Some s ->
          TBox (PBlock (d2,
                        List.map ~f:(fun (r, t) ->
                            (r, type_sub s t))
                          c1,
                        stack_sub s s1,
                        retmarker_sub s q1))
      end
    | TBox (PTuple ts) ->
      TBox (PTuple (List.map ~f:(type_rebind bind) ts))
    | _ -> t

  and stack_rebind bind s = match s with
    | SAbstract (pref, z) -> begin match bind with
        | FTAL.SBinding (z1,z2) when z1 = z -> SAbstract (pref, z2)
        | _ -> s
      end
    | SConcrete ts -> SConcrete (List.map ~f:(type_rebind bind) ts)


  and retmarker_rebind bind q = match q with
    | QEpsilon e -> begin match bind with
        | FTAL.EBinding (e1,e2) when e = e1 ->
          QEpsilon e2
        | _ -> q
      end
    | QEnd (t,s) -> QEnd (type_rebind bind t,
                          stack_rebind bind s)
    | _ -> q


  let option_cons o1 o2 = match o1,o2 with
    | None, _ -> None
    | _, None -> None
    | Some x, Some xs -> Some (x::xs)

  let rec delta_rebindings d1 d2 =
    match d1,d2 with
    | DAlpha a1::d1', DAlpha a2::d2' ->
      option_cons
        (if a1 = a2 then None
         else Some (FTAL.TBinding (a1,a2)))
        (delta_rebindings d1' d2')
    | DZeta a1::d1', DZeta a2::d2'->
      option_cons
        (if a1 = a2 then None
         else Some (FTAL.SBinding (a1,a2)))
        (delta_rebindings d1' d2')
    | DEpsilon a1::d1', DEpsilon a2::d2' when a1 <> a2 ->
      option_cons
        (if a1 = a2 then None
         else Some (FTAL.EBinding (a1,a2)))
        (delta_rebindings d1' d2')
    | [], [] -> Some []
    | _ -> None


  let rec t_eq t1 t2 = match t1, t2 with
    | TVar v1, TVar v2 -> v1 = v2
    | TUnit, TUnit -> true
    | TInt, TInt -> true
    | TExists (a1, b1), TExists (a2, b2) ->
      t_eq b1 (type_rebind (FTAL.TBinding (a2, a1)) b2)
    | TRec (a1, b1), TRec (a2, b2) ->
      t_eq b1 (type_rebind (FTAL.TBinding (a2, a1)) b2)
    | TTupleRef ts1, TTupleRef ts2 ->
      List.for_all2_exn ~f:t_eq ts1 ts2
    | TBox (PBlock (d1, c1, s1, q1)), TBox (PBlock (d2, c2, s2, q2)) ->
      begin match delta_rebindings d1 d2 with
        | None -> false
        | Some binds ->
          let c1 = List.sort (fun (a,_) (b,_) -> compare a b) c1 in
          let c2 = List.sort (fun (a,_) (b,_) -> compare a b) c2 in
          List.length c1 = List.length c2 &&
          List.for_all2_exn ~f:(fun (r1, t1) (r2, t2) ->
              r1 = r2 && t_eq t1 (List.fold_left
                                    ~f:(fun t' b -> type_rebind b t')
                                    ~init:t2 binds)) c1 c2 &&
          s_eq s1 (List.fold_left ~f:(fun s b -> stack_rebind b s) ~init:s2 binds) &&
          q_eq q1 (List.fold_left ~f:(fun q b -> retmarker_rebind b q) ~init:q2 binds)
      end
    | TBox (PTuple ts1), TBox (PTuple ts2) ->
      List.for_all2_exn ~f:t_eq ts1 ts2
    | _ -> false

  and s_eq s1 s2 = match s1,s2 with
    | SAbstract (pr1, z1), SAbstract (pr2, z2) -> List.for_all2_exn ~f: t_eq pr1 pr2 && z1 = z2
    | SConcrete ts1, SConcrete ts2 ->
      List.for_all2_exn ~f: t_eq ts1 ts2
    | _ -> false

  and q_eq q1 q2 = match q1, q2 with
    | QR r1, QR r2 -> r1 = r2
    | QI i1, QI i2 -> i1 = i2
    | QEpsilon e1, QEpsilon e2 -> e1 = e2
    | QEnd (t1, s1), QEnd (t2, s2) ->
      t_eq t1 t2 && s_eq s1 s2
    | QOut, QOut -> true
    | _ -> false




  let decomp (is, m) =
    match m with
    | [] ->
      begin match is with
        | [] -> None
        | Ihalt (_,_,_) :: _ -> None
        | Iimport (r,s,t,e) :: rest ->
          begin match F.decomp e with
            | None -> if F.value e then Some (CComponentEmpty CHoleI, F.TI is) else None
            | Some (ctxt, e') -> Some (CComponentEmpty (CImportI (r, s, t, ctxt, rest)), e')
          end
        | _ -> Some (CComponentEmpty CHoleI, F.TI is)
      end
    | _ -> Some (CComponentHeap CHoleC, F.TC (is, m))

  let rec ru r = function
    | UApp (u, o) -> WApp (ru r u, o)
    | UPack (t1, u, s, t2) -> WPack (t1, ru r u, s, t2)
    | UFold (s, t, u) -> WFold (s, t, ru r u)
    | UW w -> w
    | UR rn -> List.Assoc.find_exn r rn

  let delta op w1 w2 =
    match (op, w1, w2) with
    | (Add, WInt n1, WInt n2) -> WInt (n1 + n2)
    | (Sub, WInt n1, WInt n2) -> WInt (n1 - n2)
    | (Mult, WInt n1, WInt n2) -> WInt (n1 * n2)
    | _ -> raise (Failure "delta given args that don't make any sense")



  let type_zip delt os =
    List.map2_exn ~f:(fun d o -> match d,o with
        | DAlpha a, OT t -> FTAL.TType (a,t)
        | DZeta z, OS s -> FTAL.SType (z,s)
        | DEpsilon e, OQ q -> FTAL.EMarker (e,q)
        | _ ->
          raise (Failure ("Trying to instantiate wrong type of type variables: "
                          ^ show_delta delt ^ " and " ^ show_omega_list os)))
      delt os


  let instrs_sub delt os is =
    let subs = type_zip delt os in
    List.rev (List.fold_left ~f:(fun acc i -> (List.fold_left ~f:(fun t' p -> instr_sub p i) ~init:i subs)::acc) ~init:[] is)

  let reduce (c : mem * instr list) =
    match c with
    | ((hm,rm,sm), Iaop (op, rd, rs, u)::is) ->
      ((hm, replace rm rd (delta op (List.Assoc.find_exn rm rs) (ru rm u)), sm), is)
    | ((hm,rm,sm), Ibnz (r,u)::is) ->
      begin match List.Assoc.find_exn rm r with
        | WInt 0 -> ((hm,rm,sm), is)
        | WInt _ ->
          let hc os l =
            match List.Assoc.find_exn hm l with
            | HCode (delt,ch,s,qr,is) ->
              instrs_sub delt os is
            | _ -> raise (Failure "branching to non-code")
          in
          begin match ru rm u with
            | WLoc l -> ((hm,rm,sm), hc [] l)
            | WApp (WLoc l, os) -> ((hm,rm,sm), hc os l)
            | _ -> raise (Failure "branching to non-loc")
          end
        | _ -> c
      end
    | ((hm,rm,sm), Ild (rd,rs,i)::is) ->
      begin match List.Assoc.find_exn rm rs with
        | WLoc l ->
          begin match List.Assoc.find_exn hm l with
            | HTuple ws when List.length ws > i ->
              ((hm, replace rm rd (List.nth_exn ws i), sm), is)
            | HTuple _ -> raise (Failure "ld: tuple index out of bounds")
            | _ -> raise (Failure "ld: trying to load from non-tuple")
          end
        | _ -> raise (Failure "ld: trying to load from non-location")
      end
    | ((hm,rm,sm), Ist (rd,i,rs)::is) ->
      begin match List.Assoc.find_exn rm rd with
        | WLoc l ->
          begin match List.Assoc.find_exn hm l with
            | HTuple ws when List.length ws > i ->
              (((replace hm l (HTuple (list_replace i ws (List.Assoc.find_exn rm rs)))), rm, sm), is)
            | HTuple _ -> raise (Failure "st: tuple index out of bounds")
            | _ -> raise (Failure "st: trying to store to non-tuple")
          end
        | _ -> raise (Failure "st: trying to store to non-location")
      end
    | ((hm,rm,sm), Iralloc (rd,n)::is) when List.length sm >= n ->
      let l = FTAL.gen_sym () in (((l, HTuple (List.take sm n)) :: hm, replace rm rd (WLoc l), List.drop sm n), is)
    | ((hm,rm,sm), Iballoc (rd,n)::is) when List.length sm >= n ->
      let l = FTAL.gen_sym () in (((l, HTuple (List.take sm n)) :: hm, replace rm rd (WLoc l), List.drop sm n), is)
    | ((hm,rm,sm), Imv (rd,u)::is) ->
      ((hm, replace rm rd (ru rm u), sm), is)
    | ((hm,rm,sm), Iunpack (a,rd,u)::is) ->
      begin match ru rm u with
        | WPack (t1,w,a,t2) -> ((hm, replace rm rd w, sm), instrs_sub [DAlpha a] [OT t1] is)
        | _ -> raise (Failure "unpack: trying to unpack non-pack")
      end
    | ((hm,rm,sm), Iunfold (rd, u)::is) ->
      begin match ru rm u with
        | WFold (a,t,w) -> ((hm, replace rm rd w, sm), is)
        | _ -> raise (Failure "unfold: trying to unpack non-pack")
      end
    | ((hm,rm,sm), Isalloc n::is) ->
      ((hm,rm,List.append (List.init ~f:(fun _ -> WUnit) n) sm), is)
    | ((hm,rm,sm), Isfree n::is) when List.length sm >= n ->
      ((hm,rm,List.drop sm n), is)
    | ((hm,rm,sm), Isld (rd,i)::is) when List.length sm > i ->
      ((hm, replace rm rd (List.nth_exn sm i), sm), is)
    | ((hm,rm,sm), Isst (i,rs)::is) when List.length sm > i ->
      ((hm,rm,list_replace i sm (List.Assoc.find_exn rm rs)), is)
    | ((hm,rm,sm), Ijmp u::is) ->
      let hc os l =
        match List.Assoc.find_exn hm l with
        | HCode (delt,ch,s,qr,is) -> instrs_sub delt os is
        | _ -> raise (Failure "jumping to non-code")
      in
      begin match ru rm u with
        | WLoc l -> ((hm,rm,sm), hc [] l)
        | WApp (WLoc l, os) -> ((hm,rm,sm), hc os l)
        | _ -> raise (Failure "jmp: trying to jump to non-location")
      end
    | ((hm,rm,sm), Icall (u,s,q)::is) ->
      let hc os l =
        match List.Assoc.find_exn hm l with
        | HCode (delt,ch,s,qr,is) ->
          instrs_sub delt (List.append os [OS s; OQ q]) is
        | _ -> raise (Failure "calling to non-code")
      in
      begin match ru rm u with
        | WLoc l -> ((hm,rm,sm), hc [] l)
        | WApp (WLoc l, os) -> ((hm,rm,sm), hc os l)
        | _ -> raise (Failure "call: trying to jump to non-location")
      end
    | ((hm,rm,sm), Iret (rloc,_)::is) ->
      let hc os l =
        match List.Assoc.find_exn hm l with
        | HCode (delt,ch,s,qr,is) -> instrs_sub delt os is
        | _ -> raise (Failure "returning to non-code")
      in
      begin match List.Assoc.find_exn rm rloc with
        | WLoc l -> ((hm,rm,sm), hc [] l)
        | WApp (WLoc l, os) -> ((hm,rm,sm), hc os l)
        | _ -> raise (Failure "ret: trying to return to non-location")
      end
    | ((hm,rm,sm), Iimport (r,s,t,v)::is) ->
      let (m, w) = FTAL.tf t v (hm,rm,sm) in
      (m, Imv (r, UW w)::is)
    | ((hm,rm,sm), Iprotect (_,_)::is) ->
      ((hm,rm,sm), is)
    | _ -> c

end
