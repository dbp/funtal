open Utils

type l = { line : int; col : int }
         [@@deriving show]
let cpos {Lexing.pos_fname; pos_lnum; pos_cnum; pos_bol} =
  let line = pos_lnum in
  let col = pos_cnum - pos_bol in
  {line = line; col = col}

let dummy_loc = { line = -1; col = -1 }

module rec FTAL : sig

  val tytrans : F.t -> TAL.t
  val ft : F.t -> TAL.w -> TAL.mem -> (TAL.mem * F.exp)
  val tf : F.t -> F.exp -> TAL.mem -> (TAL.mem * TAL.w)

  type e = FC of F.exp | TC of TAL.component
  val show_e : e -> string

  type t = FT of F.t | TT of TAL.t
  val show : t -> string

  exception TypeError of string * l

  type context = TAL.psi * TAL.delta * F.gamma * TAL.chi * TAL.q * TAL.sigma
  val get_reg : context -> TAL.chi
  val get_stack : context -> TAL.sigma
  val set_heap : context -> TAL.psi -> context

  val default_context : TAL.q -> context

  val tc : context -> e -> t * TAL.sigma
  val tc_is : context -> TAL.instr list -> unit
  val tc_w : context -> TAL.w -> TAL.t
  val tc_u : context -> TAL.u -> TAL.t
  val tc_h : context -> l -> TAL.mut -> TAL.h -> TAL.psi_elem
  val tc_h_shallow : context -> l -> TAL.mut -> TAL.h -> TAL.psi_elem

  type substitution = FTerm of string * F.exp
                    | FType of string * F.t
                    | TType of string * TAL.t
                    | SType of string * TAL.sigma
                    | EMarker of string * TAL.q
                    | SAbs of TAL.sigma * string

  val show_substitution : substitution -> string

  val gen_sym : ?pref:string -> unit -> string


end = struct

  let gen_sym =
    let count = ref 0 in
    fun ?(pref="g") () -> let v = !count in count := v + 1; String.concat "" [pref; string_of_int v]

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

  let rec ft t w (m : TAL.mem) =
    let (hm,rm,sm) = m in
    match (t, w) with
    | (F.TUnit, TAL.WUnit l) -> (m, F.EUnit l)
    | (F.TInt, TAL.WInt (l, n)) -> (m, F.EInt (l, n))
    | (F.TTuple ts, TAL.WLoc (loc, heaploc)) ->
      begin match List.Assoc.find_exn hm heaploc with
        | (_, TAL.HTuple ws) ->
          let (m', vs) =
            List.fold_left
              ~f:(fun (mx, b) (t,w) -> let (m'',v) = ft t w mx in (m'', v::b))
              ~init:(m, [])
              (List.zip_exn ts ws) in
          (m', F.ETuple (loc, vs))
        | _ -> raise (Failure "ft: can't convert tuple if loc isn't pointing to tuple")
      end
    | (F.TRec (a, t), TAL.WFold (l, a',t',w)) when tytrans (F.TRec (a,t)) = TAL.TRec (a', t') ->
      let (m', v) = ft (F.type_sub (FTAL.FType (a, F.TRec (a, t))) t) w m in
      (m', F.EFold (l, a, t, v))
    | (F.TArrow (ts,t1), TAL.WLoc (l', l)) ->
      let z1 = gen_sym ~pref:"z" () in
      let z2 = gen_sym ~pref:"z" () in
      let z3 = gen_sym ~pref:"z" () in
      let lend = gen_sym ~pref:"lend" () in
      let hend =
        TAL.(HCode ([DZeta z1],
                    [("r1", tytrans t1)],
                    (SAbstract ([], z1)),
                    (QEnd (tytrans t1, SAbstract ([], z1))),
                    [Ihalt (l', tytrans t1, SAbstract ([], z1), "r1")])) in
      let ps = List.map ~f:(fun t -> (gen_sym ~pref:"arg" (), t)) ts in
      let v = F.ELam
          (l', ps, F.EBoundary
             (l', t1, None, (TAL.(l', List.concat
                          [[Iprotect (l', [], z2)];
                           (List.concat (List.map ~f:(fun (x,xt) ->
                                [Iimport (l', "r1", z3, SAbstract ([], z2), xt, F.EVar (l', x));
                                 Isalloc (l', 1);
                                 Isst (l', 0, "r1")]) ps));
                           [Imv (l', "ra", UApp (l', UW (l', WLoc (l', lend)), [OS (SAbstract ([], z2))]));
                            Icall (l', UW (l', w),
                                   SAbstract ([], z2),
                                   QEnd (tytrans t1, SAbstract ([], z2)))]],
                        []))))
      in (((lend, (TAL.Box, hend))::hm,rm,sm), v)
    | (F.TArrowMod (ts,sin,sout,t1), TAL.WLoc (l', l)) ->
      let lend = gen_sym ~pref:"lend" () in
      let z1 = gen_sym ~pref:"z" () in
      let z2 = gen_sym ~pref:"z" () in
      let z3 = gen_sym ~pref:"z" () in
      let hend =
        TAL.(HCode ([DZeta z1],
                   [("r1", tytrans t1)],
                   SAbstract (sin, z1),
                   (QEnd (tytrans t1, SAbstract (sout, z1))),
                   [Ihalt (l', tytrans t1, SAbstract (sout, z1), "r1")])) in
      let ps = List.map ~f:(fun t -> (gen_sym ~pref:"arg" (), t)) ts in
      let v = F.ELamMod
          (l', ps, sin, sout, F.EBoundary
             (l', t1, None, (TAL.(l', List.concat
                          [(List.concat (List.map ~f:(fun (x,xt) ->
                               [Iprotect (l', sin, z2);
                                Iimport (l', "r1", z3, SAbstract (sin, z2), xt, F.EVar (l',x));
                                Isalloc (l',1);
                                Isst (l',0, "r1")]) ps));
                           [Imv (l',"ra", UApp (l', UW (l', WLoc (l', lend)),
                                             [OS (SAbstract (sout, z2))]));
                            Icall (l',UW (l', w),
                                   SAbstract (sin, z2),
                                   QEnd (tytrans t1, SAbstract (sout, z2)))]],
                        []))))
      in (((lend, (TAL.Box, hend))::hm,rm,sm), v)
    | _ -> raise (Failure ("ft: can't convert at type " ^ F.show t ^ " value " ^ TAL.show_w w))

  let rec tf t v m =
    let (hm,rm,sm) = m in
    match (t, v) with
    | (F.TUnit, F.EUnit l) -> (m, TAL.WUnit l)
    | (F.TInt, F.EInt (l,n)) -> (m, TAL.WInt (l,n))
    | (F.TTuple ts, F.ETuple (l,es)) ->
      let ((hm',rm',sm'), ws) = List.fold_left
          ~f:(fun (mx, b) (t,v) -> let (m'', w) = tf t v mx in (m'', w::b))
          ~init:(m, [])
          (List.zip_exn ts es) in
      let l' = gen_sym ~pref:"loc" () in
      (((l',(TAL.(Box, HTuple ws)))::hm',rm',sm'), TAL.WLoc (l, l'))
    | (F.TRec (a,t), F.EFold (l,a',t',e)) when (a',t') = (a,t) ->
      let (m', w) = tf (F.type_sub (FTAL.FType (a, F.TRec (a,t))) t) e m in
      (m', TAL.WFold (l,a,tytrans t,w))
    | (F.TArrow (ts,t1), F.ELam (l,ps,body)) ->
      let loc = gen_sym ~pref:"lf" () in
      let e = gen_sym ~pref:"e" () in
      let z1 = gen_sym ~pref:"z" () in
      let z2 = gen_sym ~pref:"z" () in
      let s' = TAL.SAbstract (List.map ~f:tytrans ts, z1) in
      let s = TAL.(SAbstract ((TBox (PBlock ([], [("r1", tytrans t1)],
                                             SAbstract ([], z1), QEpsilon e))) ::
                              List.map ~f:tytrans ts, z1)) in
      let body_wrapped =
        let n = List.length ts in
        F.EApp (l,F.ELam (l,ps,body),
                List.mapi ~f:(fun i t' ->
                    F.EBoundary (l,t', Some s, (l, [TAL.Isld (l,"r1", n-i);
                                               TAL.Ihalt (l,tytrans t', s, "r1")], [])))
                  (List.map ~f:snd ps))
      in
      let instrs = TAL.([Isalloc (l,1); Isst (l,0, "ra");
                         Iimport (l,"r1", z2, SAbstract ([], z1), t1, body_wrapped);
                         Isld (l,"ra",0); Isfree (l,List.length ts + 1); Iret (l,"ra", "r1")]) in
      let h =
        TAL.(HCode
               ([DZeta z1; DEpsilon e],
                [("ra", TBox (PBlock ([], [("r1", tytrans t1)], SAbstract ([], z1), QEpsilon e)))],
                s',
                QR "ra",
                instrs))
      in
      (((loc,(TAL.Box, h))::hm,rm,sm), TAL.WLoc (l,loc))
    | (F.TArrowMod (ts,sin,sout,t1), F.ELamMod (l,ps,sin',sout',body))
      when sin = sin && sout = sout' ->
      let loc = gen_sym ~pref:"lf" () in
      let e = gen_sym ~pref:"e" () in
      let z1 = gen_sym ~pref:"z" () in
      let z2 = gen_sym ~pref:"z" () in
      let s' = TAL.SAbstract (List.map ~f:tytrans ts, z1) in
      let s = TAL.(SAbstract ((TBox (PBlock ([], [("r1", tytrans t1)],
                                             SAbstract ([], z1), QEpsilon e))) ::
                              List.map ~f:tytrans ts, z1)) in

      let body_wrapped =
        let n = List.length ts in
        F.EApp (l,F.ELamMod (l,ps,sin,sout,body),
                List.mapi ~f:(fun i t' ->
                    F.EBoundary (l,t', Some s, (l, [TAL.Isld (l,"r1", n-i);
                                               TAL.Ihalt (l,tytrans t', s, "r1")], [])))
                  (List.map ~f:snd ps))
      in
      let instrs = TAL.([Isalloc (l,1); Isst (l,0, "ra"); Iimport (l,"r1", z2, SAbstract ([], z1), t1, body_wrapped);
                         Isld (l,"ra",0); Isfree (l,List.length ts + 1); Iret (l,"ra", "r1")]) in
      let h =
        TAL.(HCode
               ([DZeta z1; DEpsilon e],
                [("ra", TBox (PBlock ([], [("r1", tytrans t1)], SAbstract ([], z1), QEpsilon e)))],
                s',
                QR "ra",
                instrs))
      in
      (((loc,(TAL.Box, h))::hm,rm,sm), TAL.WLoc (l,loc))
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
                    | SAbs of TAL.sigma * string
  [@@deriving show]

  exception TypeError of string * l

  type context = TAL.psi * TAL.delta * F.gamma * TAL.chi * TAL.q * TAL.sigma

  let default_context q = ([],[],[],[],q,TAL.SConcrete [])

  let get_tyenv (_,d,_,_,_,_) = d
  let set_tyenv (p,_,g,c,q,s) d = (p,d,g,c,q,s)

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
        let open F in
        match exp, get_ret context with
        | EVar (l,i), TAL.QOut ->
          begin match List.Assoc.find (get_env context) i with
            | Some v -> (FT v, get_stack context)
            | None -> raise (TypeError ("Variable '" ^ i ^ "' not in scope.", l))
          end
        | EUnit l, TAL.QOut  -> (FT TUnit, get_stack context)
        | EInt _, TAL.QOut -> (FT TInt, get_stack context)
        | EBinop (l,e1,o,e2), TAL.QOut ->
          begin match tc' e1 with
            | (FT TInt, s1) ->
              begin match tc (set_stack context s1) (FC e2) with
                | (FT TInt, s2) -> (FT TInt, s2)
                | (FT t, _) -> raise (TypeError (show_binop o ^ ": second argument has type " ^ show t ^ ", not int.", l))
                | _ -> raise (TypeError (show_binop o ^ ": Uh-oh, got something I didn't understand.", l))
              end
            | (FT t, _) -> raise (TypeError (show_binop o ^ ": first argument has type " ^ show t ^ ", int.", l))
            | _ -> raise (TypeError (show_binop o ^ ": Uh-oh, got something I didn't understand.", l))
          end
        | EIf0 (l,c,e1,e2), TAL.QOut ->
          begin match tc' c with
            | FT TInt, s1 ->
              begin match tc (set_stack context s1) (FC e1) with
                | FT t1, s2 ->
                  begin match tc (set_stack context s2) (FC e2) with
                    | FT t2, s3 -> if t_eq t1 t2 && TAL.s_eq s2 s3 then (FT t1, s2) else
                        raise (TypeError ("if: then branch has type " ^ show t1 ^ " but else branch has type " ^ show t2 ^ ".", l))
                    | _ -> raise (TypeError ("if: Uh-oh, got something I didn't understand.", l))
                  end
                | _ -> raise (TypeError ("if: Uh-oh, got something I didn't understand.", l))
              end
            | _ -> raise (TypeError ("if: test not an int.", l))
          end
        | ELam (l,ps,b), TAL.QOut ->
          let zeta = TAL.SAbstract ([], gen_sym ~pref:"z" ()) in
          begin match tc (set_stack (set_env context (List.append ps (get_env context))) zeta)
                        (FC b) with
          | (FT t, zeta') when zeta = zeta' -> (FT (TArrow (List.map ~f:snd ps, t)), get_stack context)
          | (FT _, _) -> raise (TypeError ("lam: body does not preserve stack.", l))
          | _ -> raise (TypeError ("lam: Uh-oh, got something I didn't understand.", l))
          end
        | ELamMod (l,ps,sin,sout,b), TAL.QOut ->
          let z = gen_sym ~pref:"z" () in
          let zeta = TAL.SAbstract (sin, z) in
          let zeta_out = TAL.SAbstract (sout, z) in
          begin match tc (set_stack (set_env context (List.append ps (get_env context))) zeta)
                        (FC b) with
          | (FT t, zeta') when zeta_out = zeta' -> (FT (TArrow (List.map ~f:snd ps, t)), get_stack context)
          | (FT _, _) -> raise (TypeError ("lam: body manipulates stack in invalid way.", l))
          | _ -> raise (TypeError ("lam: Uh-oh, got something I didn't understand.", l))
          end
        | EApp (l,f,args), TAL.QOut -> begin match tc' f with
            | FT (TArrow (ps, rv)), s ->
              if List.length ps <> List.length args then
                raise (TypeError ("app: function expected " ^
                                  string_of_int (List.length ps) ^
                                  " arguments, but passed " ^
                                  string_of_int (List.length args) ^ ".", l))
              else
                let i = ref 0 in
                (FT rv, List.fold_left ~f:(fun s0 (t,e) ->
                     i := !i + 1;
                     match tc (set_stack context s0) (FC e) with
                     | FT t', s1 when t_eq t t' -> s1
                     | FT t', _ -> raise (TypeError ("app: " ^ string_of_int !i ^
                                                     "th argument should have type " ^
                                                     show t ^ " but has type " ^ show t' ^ ".", l))
                     | _ -> raise (TypeError ("app: Uh-oh, got something I didn't understand.", l))
                   ) ~init:s (List.zip_exn ps args))
            | (FT t,_) ->
              raise (TypeError ("app: got non-function of type " ^ show t ^ ".", l))
            | _ -> raise (TypeError ("app: Uh-oh, got something I didn't understand.", l))
          end
        | EFold (l,a,t,e), TAL.QOut ->
          begin match tc' e with
            | FT t', s -> if F.t_eq t' (F.type_sub (FTAL.FType (a, TRec (a,t))) t) then (FT (TRec (a,t)), s)
              else
                raise (TypeError ("fold: expected body to have type " ^ show t' ^ ".", l))
            | _ -> raise (TypeError ("fold: Uh-oh, got something I didn't understand.", l))
          end
        | EUnfold (l,e), TAL.QOut -> begin match tc' e with
            | FT (TRec (a,t)), s -> (FT (F.type_sub (FTAL.FType (a, TRec (a,t))) t), s)
            | (FT t, _) -> raise (TypeError ("unfold: body not a recursive type: " ^ show t ^ ".", l))
            | _ -> raise (TypeError ("unfold: Uh-oh, got something I didn't understand.", l))
          end
        | ETuple (l,es), TAL.QOut ->
          begin match List.fold_left ~f:(fun (l',s0) e -> match tc (set_stack context s0) (FC e) with
              | FT t', s1 -> (List.append l' [t'], s1)
              | _ -> raise (TypeError ("tuple: Uh-oh, got something I didn't understand.", l)))
              ~init:([], get_stack context) es with
          | l,s -> (FT (TTuple l), s)
          end
        | EPi (loc,n,e'), TAL.QOut -> begin match tc' e' with
            | FT (TTuple l), s when List.length l > n -> (FT (List.nth_exn l n), s)
            | FT (TTuple l), s -> raise (TypeError ("pi: index " ^ string_of_int n
                                                    ^ " is too high for a tuple of size " ^
                                                    string_of_int (List.length l) ^ ".", loc))
            | FT t, _ -> raise (TypeError ("pi: given non-tuple of type " ^ show t ^ ".", loc))
            | _ -> raise (TypeError ("pi: Uh-oh, got something I didn't understand.", loc))
          end
        | EBoundary (l,t,s,c), TAL.QOut ->
          let s' = Option.value ~default:(get_stack context) s in
          begin match tc (set_ret context (TAL.QEnd (tytrans t, s'))) (TC c) with
            | TT t0, s0 when not (TAL.t_eq t0 (tytrans t)) ->
              raise (TypeError ("FT: contents should have had type " ^ show t ^
                                " which is not equivalent to type " ^ TAL.show t0 ^ ".",l))
            | TT t0, s0 when not (TAL.s_eq s0 s') ->
              raise (TypeError ("FT: after running stack should have had type " ^
                                TAL.show_sigma s' ^ " but instead had type " ^ TAL.show_sigma s0 ^ ".",l))
            | TT t0, s0 -> (FT t, s0)
            | _ -> raise (TypeError ("FT: Uh-oh, got something I didn't understand.", l))
          end
        | _ -> raise (TypeError ("exp: F expressions must have return marker out.", F.get_loc exp))
      end
    | TC (loc, instrs, h) ->
      let ht = List.map ~f:(fun (l,(m, p)) -> (l, (m, tc_h_shallow context loc m p))) h in
      let context = set_heap context (List.append (get_heap context) ht) in
      let _ = List.iter ~f:(fun (l,(_, v)) ->
          (* NOTE(dbp 2017-02-20): Since these types are fully
             specified, these checks shouldn't be able to go wrong.
             *)
          match List.Assoc.find (get_heap context) l with
          | None -> raise (TypeError ("component: Uh-oh, got something I didn't understand." ^ l, loc))
          | Some (m,p) ->
            let p' = tc_h context loc m v in
            if not (TAL.psi_elem_eq p' p) then
              raise (TypeError ("component: Uh-oh, got something I didn't understand.", loc)) else ()) h in
      begin
        tc_is context instrs;
        match TAL.ret_type context (get_ret context) with
        | Some s -> s
        | None -> raise (TypeError ("component: return marker invalid: " ^
                                    TAL.show_q (get_ret context) ^ ".", loc))
      end

  and tc_is context instrs : unit =
    let open TAL in
    match instrs, get_ret context with
    | Iaop (l,op, rd, rs, u)::is, QR r when rd = r ->
      raise (TypeError (show_aop op ^ ": can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iaop (l,op, rd, rs, u)::is, _ ->
      begin match List.Assoc.find (get_reg context) rs, tc_u context u with
        | None, _ -> raise (TypeError (show_aop op ^ ": source register " ^ rs ^ " is empty.", l))
        | Some t, _ when t <> TInt -> raise (TypeError (show_aop op ^ ": source register has type " ^
                                                        show t ^ ", not int.", l))
        | _, t when t <> TInt -> raise (TypeError (show_aop op ^ ": operand has type " ^ show t ^ ", not int.", l))
        | _ -> tc_is (set_reg context (List.Assoc.add (get_reg context) rd TInt)) is
      end
    | Imv (l,rd,u)::is, QR r when rd = r ->
      raise (TypeError ("mv: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Imv (l,rd,u)::is, q ->
      let context = match q, u with
        | QR r, UR (_, r') when r = r' -> set_ret context (QR rd)
        | _ -> context in
      tc_is (set_reg context (List.Assoc.add (get_reg context) rd (tc_u context u))) is
    | Iimport (l,rd,z,s,t,f)::is, QR r when rd = r ->
      raise (TypeError ("import: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iimport (l,rd,z,s,t,f)::is, _ when
        stack_pref_length s > stack_pref_length (get_stack context) ||
        not (s_eq (stack_drop (get_stack context) (stack_pref_length (get_stack context) - stack_pref_length s)) s) ->
      raise (TypeError ("import: protected suffix does not match current stack. Suffix is " ^
                        show_sigma s ^ ", but current stack is " ^ show_sigma (get_stack context) ^ ".", l))
    | Iimport (l,rd,z,s,t,f)::is, _ ->
      let pref = stack_take (get_stack context) (stack_pref_length (get_stack context) - stack_pref_length s) in
      let suf = stack_drop (get_stack context) (stack_pref_length (get_stack context) - stack_pref_length s) in
      begin match tc (set_stack (set_ret context QOut) (SAbstract (pref, z))) (FC f) with
        | (FT t',s') when not (F.t_eq t t') ->
          raise (TypeError ("import: F expression has type " ^ F.show t' ^ ", but should have type " ^ F.show t ^ ".", l))
        | (FT t',SConcrete _)  ->
          raise (TypeError ("import: F expression does not protect abstract stack tail.", l))
        | (FT t',SAbstract (_, z')) when z <> z'  ->
          raise (TypeError ("import: F expression does not preserve abstract stack tail. Should have been " ^ z ^ " but was " ^ z' ^ ".", l))
        | (FT t',SAbstract (newpref, _)) -> tc_is (set_stack (set_reg context (List.Assoc.add (get_reg context) rd (tytrans t))) (stack_prepend newpref suf)) is
        | _  -> raise (TypeError ("import: Uh-oh, got something I didn't understand.", l))
      end
    | [Ihalt (l,t,s,r)], QEnd (t',s') when not (t_eq t' t) ->
      raise (TypeError ("halt: specified return type, " ^ show t ^ ", does not match return marker's: " ^ show t' ^ ".", l))
    | [Ihalt (l,t,s,r)], QEnd (t',s') when not (s_eq s s') ->
      raise (TypeError ("halt: specified stack, " ^ show_sigma s ^ ", does not match return marker's: " ^ show_sigma s' ^ ".", l))
    | [Ihalt (l,t,s,r)], QEnd _ when not (s_eq s (get_stack context)) ->
      raise (TypeError ("halt: specified stack, " ^ show_sigma s ^
                        ", does not match current stack: " ^
                        show_sigma (get_stack context) ^ ".", l))
    | [Ihalt (l,t,s,r)], QEnd _ ->
      begin match List.Assoc.find (get_reg context) r with
        | Some t' when t_eq t t' -> ()
        | Some t' -> raise (TypeError ("halt: value in return register " ^ r ^
                                       " should have type " ^ show t ^ " but instead is " ^ show t' ^ ".", l))
        | None -> raise (TypeError ("halt: return register " ^ r ^ " is empty.", l))
      end
    | [Ihalt (l,_,_,_)], q ->
      raise (TypeError ("halt: return marker must be end{}, instead is: " ^ show_q q ^ ".", l))
    | Isalloc (l,n) :: is, _ ->
      tc_is (set_stack context (List.fold_left ~f:(fun s _ -> stack_cons TUnit s)
                                  ~init:(get_stack context) (List.init ~f:(fun x -> x) n))) is
    | Isfree (l,n) :: is, QI n' when n > n' ->
      raise (TypeError ("sfree: return marker is at position " ^ string_of_int n' ^ ", so you can't free " ^
                        string_of_int n ^ " cells: the return address would be lost.", l))
    | Isfree (l,n) :: is, _ when stack_pref_length (get_stack context) < n ->
      raise (TypeError ("sfree: only " ^ string_of_int (stack_pref_length (get_stack context)) ^
                        " stack cells are exposed, so can't free " ^ string_of_int n ^ ".", l))
    | Isfree (l,n) :: is, QI n' ->
      tc_is (set_ret (set_stack context (stack_drop (get_stack context) n ))
            (QI (n' - n))) is
    | Isfree (l,n) :: is, _ ->
      tc_is (set_stack context (stack_drop (get_stack context) n )) is
    | Iprotect (l,pref,v)::is, QI n when n > List.length pref ->
      raise (TypeError ("protect: return marker is at position " ^ string_of_int n ^
                        ", so you can't hide everything past the first " ^
                        string_of_int (List.length pref) ^ " cells: the return address would be hidden.", l))
    | Iprotect (l,pref, v)::is, _ when not (s_pref_eq (stack_take (get_stack context) (List.length pref)) pref) ->
      raise (TypeError ("protect: specified prefix " ^
                        show_sigma_prefix pref ^ " does not match current stack: " ^
                        show_sigma (get_stack context) ^ ".", l))
    | Iprotect (l,pref, v)::is, _ ->
      let stail = stack_drop (get_stack context) (List.length pref) in
      let new_q = retmarker_sub (SAbs (stail, v)) (get_ret context) in
      tc_is (set_ret (set_stack (set_tyenv context (List.append (get_tyenv context) [DZeta v])) (SAbstract (pref, v))) new_q) is
    | Isst(l,n,r):: is, _ when stack_pref_length (get_stack context) <= n ->
      raise (TypeError ("sst: only " ^ string_of_int (stack_pref_length (get_stack context)) ^
                        " stack cells are exposed, so can't store at position " ^ string_of_int n ^ ".", l))
    | Isst(l,n,r):: is, QI n' when n = n' ->
      raise (TypeError ("sst: can't overwrite current return marker at position " ^
                        string_of_int n' ^ " on the stack.", l))
    | Isst(l,n,r):: is, q ->
      begin match List.Assoc.find (get_reg context) r with
        | None -> raise (TypeError ("sst: register " ^ r ^ " is empty.", l))
        | Some t ->
          let context = match q with
            | QR r' when r = r' -> set_ret context (QI n)
            | _ -> context
          in
          tc_is (set_stack context (stack_prepend (stack_take (get_stack context) n) (stack_cons t (stack_drop (get_stack context) (n+1))))) is
      end
    | Isld(l,rd,n)::is, QR r when r = rd ->
      raise (TypeError ("sld: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Isld(l,rd,n)::is, _ when stack_pref_length (get_stack context) <= n ->
      raise (TypeError ("sld: only " ^ string_of_int (stack_pref_length (get_stack context)) ^
                        " stack cells are exposed, so can't load from position " ^
                        string_of_int n ^ ".", l))
    | Isld(l,rd,n)::is, q ->
      let context = match q with
        | QI n' when n = n' -> set_ret context (QR rd)
        | _ -> context
      in
      tc_is (set_reg context (List.Assoc.add (get_reg context) rd (List.last_exn (stack_take (get_stack context) (n+1))))) is
    | Ild(l,rd,rs,n)::is, QR r when r = rd ->
      raise (TypeError ("ld: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Ild(l,rd,rs,n)::is, _ ->
      begin match List.Assoc.find (get_reg context) rs with
        | None -> raise (TypeError ("ld: register " ^ rs ^ " is empty.", l))
        | Some (TBox (PTuple ps)) | Some (TTupleRef ps) when n >= List.length ps ->
          raise (TypeError ("ld: can't load from index " ^
                            string_of_int n ^ " from a tuple of length " ^
                            string_of_int (List.length ps) ^ ".", l))
        | Some (TBox (PTuple ps)) | Some (TTupleRef ps) ->
          let t = List.nth_exn ps n in
          tc_is (set_reg context (List.Assoc.add (get_reg context) rd t)) is
        | Some t ->
          raise (TypeError ("ld: can't load from non-tuple of type " ^ show t ^ ".", l))
      end
    | Ist(l,rd, n, rs)::is, QR r when r = rd ->
      raise (TypeError ("st: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Ist(l,rd, n, rs)::is, _ ->
      begin match List.Assoc.find (get_reg context) rs with
        | None -> raise (TypeError ("st: source register " ^ rs ^ " is empty.", l))
        | Some t ->
          begin match List.Assoc.find (get_reg context) rd with
            | None -> raise (TypeError ("st: destination register " ^ rd ^ " is empty.", l))
            | Some (TTupleRef ps) when n >= List.length ps ->
              raise (TypeError ("st: can't store at index " ^ string_of_int n ^
                                "in a tuple of length " ^ string_of_int (List.length ps) ^
                                ".", l))
            | Some (TTupleRef ps) ->
              let t' = List.nth_exn ps n in
              if not (TAL.t_eq t t') then
                raise (TypeError ("st: can't overwrite a position with type "
                                  ^ show t' ^ " with a value of type " ^ show t ^ ".", l))
              else tc_is context is
            | Some (TBox (PTuple _)) ->
              raise (TypeError ("st: can't write to a box (i.e., immutable) tuple.", l))
            | Some t ->
              raise (TypeError ("st: can't store to a non-tuple of type: " ^ show t ^ ".", l))
          end
      end
    | Iralloc (l,rd, n)::is, _ when stack_pref_length (get_stack context) < n ->
      raise (TypeError ("ralloc: trying to allocate a tuple of size " ^ string_of_int n ^ " but there are only " ^
                        string_of_int (stack_pref_length (get_stack context))  ^ " visible cells on the stack.", l))
    | Iralloc (l,rd,n)::is, QR r when rd = r ->
      raise (TypeError ("ralloc: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iralloc (l,rd,n)::is, QI n' when n' + 1 <= n ->
      raise (TypeError ("ralloc: current return marker is on stack at position " ^ string_of_int n' ^
                        ", so allocating a tuple of size " ^ string_of_int n ^ " would move it.", l))
    | Iralloc (l,rd,n)::is, q ->
      let q' = match q with
        | QI n' -> QI (n' - n)
        | _ -> q in
      tc_is (set_ret (set_stack (set_reg context (List.Assoc.add (get_reg context) rd (TTupleRef (stack_take (get_stack context) n)))) (stack_drop (get_stack context) n)) q') is
    | Iballoc (l,rd, n)::is, _ when stack_pref_length (get_stack context) < n ->
      raise (TypeError ("balloc: trying to allocate a tuple of size " ^ string_of_int n ^ " but there are only " ^
                        string_of_int (stack_pref_length (get_stack context))  ^ " visible cells on the stack.", l))
    | Iballoc (l,rd,n)::is, QR r when rd = r ->
      raise (TypeError ("balloc: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iballoc (l,rd,n)::is, QI n' when n' + 1 <= n ->
      raise (TypeError ("balloc: current return marker is on stack at position " ^ string_of_int n' ^
                        ", so allocating a tuple of size " ^ string_of_int n ^ " would move it.", l))
    | Iballoc (l,rd,n)::is, q ->
      let q' = match q with
        | QI n' -> QI (n' - n)
        | _ -> q in
      tc_is (set_ret (set_stack (set_reg context (List.Assoc.add (get_reg context) rd (TBox (PTuple (stack_take (get_stack context) n))))) (stack_drop (get_stack context) n)) q') is
    | Iunpack (l,a, rd, u)::is, QR r when rd = r ->
      raise (TypeError ("unpack: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iunpack (l,a, rd, u)::is, _ ->
      begin match tc_u context u with
        | TExists (a', t) ->
          let newt = type_sub (TType (a, TVar a')) t in
          tc_is (set_reg context (List.Assoc.add (get_reg context) rd newt)) is
        | t -> raise (TypeError ("unpack: operand is non-existential of type " ^ show t ^ ".", l))
      end
    | Iunfold (l,rd, u)::is, QR r when rd = r ->
      raise (TypeError ("unfold: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iunfold (l,rd, u)::is, _ ->
      begin match tc_u context u with
        | TRec (a, t) ->
          let t' = type_sub (TType (a, TRec (a,t))) t in
          tc_is (set_reg context (List.Assoc.add (get_reg context) rd t')) is
        | t -> raise (TypeError ("unfold: operand is non-fold of type " ^ show t ^ ".", l))
      end
    | [Iret (l,rt, rv)], QR r when r = rt ->
      begin match List.Assoc.find (get_reg context) rt,
                  List.Assoc.find (get_reg context) rv with
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), Some ta when ra <> rv ->
        raise (TypeError ("ret: returning to a block expecting value in register " ^ ra ^ ", not " ^ rv ^ ".", l))
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), Some ta when not (t_eq ta t) ->
        raise (TypeError ("ret: returning to a block expecting value of type " ^ show t ^ ", not " ^ show ta ^ ".", l))
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), Some ta when not (s_eq s (get_stack context)) ->
        raise (TypeError ("ret: returning to a block expecting stack of type " ^
                          show_sigma s ^ " but current stack has type " ^
                          show_sigma (get_stack context) ^ ".", l))
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), Some ta -> ()
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), None ->
        raise (TypeError ("ret: value register " ^ ra ^ " is empty.", l))
      | _ -> raise (TypeError ("ret: return address " ^ rt ^ " register empty.", l))
      end
    | [Iret (l,rt, rv)], QR r  ->
      raise (TypeError ("ret: return marker says to return to " ^
                        r ^ ", but trying to return to " ^ rt ^ ".", l))
    | [Iret (l,rt, rv)], q  ->
      raise (TypeError ("ret: return marker isn't register " ^ rt ^ ", it's " ^ show_q q ^ ".", l))
    | [Ijmp (l,u)], q -> begin match tc_u context u with
        | TBox (PBlock ([], c, s, q')) when not (q_eq q q') ->
          raise (TypeError ("jmp: current return marker is " ^ show_q q ^
                            ", but trying to jump to block with return marker " ^ show_q q' ^ ".", l))
        | TBox (PBlock ([], c, s, q')) when not (s_eq s (get_stack context)) ->
          raise (TypeError ("jmp: block being jumped to expects stack of type " ^
                            show_sigma s ^ ", but current stack has type " ^
                            show_sigma (get_stack context) ^ ".", l))
        | TBox (PBlock ([], c, s, q')) when not (register_subset c (get_reg context)) ->
          raise (TypeError ("jmp: block being jumped to expects register file of type " ^ show_chi c ^
                            ", but current register file has type " ^ show_chi (get_reg context) ^ ".", l))
        | TBox (PBlock ([], c, s, q')) -> ()
        | t -> raise (TypeError ("jmp: can't jump to non-block of type " ^ show t ^ ".", l))
      end
    | Ibnz(l,rt,u)::is, q -> begin match List.Assoc.find (get_reg context) rt with
        | None -> raise (TypeError ("bnz: test register " ^ rt ^ " is empty.", l))
        | Some t when t <> TInt ->
          raise (TypeError ("bnz: test register has type " ^ show  t ^ ", not int.", l))
        | Some t -> begin match tc_u context u with
            | TBox (PBlock ([], c, s, q')) when not (q_eq q q') ->
              raise (TypeError ("bnz: current return marker is " ^ show_q q ^
                                ", but trying to branch to a block with return marker " ^
                                show_q q' ^ ".", l))
            | TBox (PBlock ([], c, s, q')) when not (s_eq s (get_stack context)) ->
              raise (TypeError ("bnz: block being branched to expects stack of type " ^ show_sigma s ^
                                ", but current stack has type " ^ show_sigma (get_stack context) ^ ".", l))
            | TBox (PBlock ([], c, s, q')) when not (register_subset c (get_reg context)) ->
              raise (TypeError ("bnz: block being branched to expects register file of type " ^ show_chi c ^
                                ", but current register file has type " ^ show_chi (get_reg context) ^ ".", l))
            | TBox (PBlock ([], c, s, q')) -> ()
            | t -> raise (TypeError ("bnz: can't branch to non-block of type " ^ show t ^ ".", l))
          end
      end
    | [Icall(l,u,s,QEnd(t',s'))], QEnd(t,s'') when t_eq t t' && s_eq s' s'' ->
      begin match tc_u context u with
        | TBox (PBlock ([DZeta z; DEpsilon e], hatc, hats, hatq)) ->
          let pref_len = stack_pref_length (get_stack context) - stack_pref_length s in
          if pref_len < 0 then
            raise (TypeError ("call: can't protect suffix of length " ^ string_of_int (stack_pref_length s) ^
                              " when current stack only has length " ^ string_of_int (stack_pref_length (get_stack context)) ^ ".", l))
          else if not (s_eq hats (SAbstract (stack_take (get_stack context) pref_len, z))) then
            raise (TypeError ("call: block being called expects stack of type " ^ show_sigma hats ^
                              ", which doesn't match specified prefix.", l))
          else
            begin match ret_addr_type (set_stack (set_reg context hatc) hats) hatq with
              | Some (TBox (PBlock (_, _,hats', QEpsilon e))) ->
                begin match hats' with
                  | SAbstract (_, z') when z = z' ->
                    if not (register_subset (TAL.chi_sub (EMarker (e, QEnd(t',s'))) (chi_sub (SType (z, s)) hatc)) (get_reg context)) then
                      raise (TypeError ("call: block being called expects register file with type " ^
                                        show_chi (TAL.chi_sub (EMarker (e, QEnd(t',s'))) (chi_sub (SType (z, s)) hatc)) ^
                                        " which is not compatible with current register file of type " ^
                                        show_chi (get_reg context) ^ ".", l))
                    else
                      ()
                  | _ ->
                    raise (TypeError ("call: block that will be returned to does not protect abstract stack suffix " ^ z ^ ".", l))
                end
              | _ -> raise (TypeError ("call: block being called to does not return to block with abstract return marker.", l))
            end
        | t -> raise (TypeError ("call: block being called does not follow calling convention: " ^ show t ^ ".", l))
      end
    | [Icall(l,u,s,QI i')], QI i ->
      begin match tc_u context u with
        | TBox (PBlock ([DZeta z; DEpsilon e], hatc, hats, hatq)) ->
          let pref_len = stack_pref_length (get_stack context) - stack_pref_length s in
          if pref_len < 0 then
            raise (TypeError ("call: can't protect suffix of length " ^ string_of_int (stack_pref_length s) ^
                              " when current stack only has length " ^ string_of_int (stack_pref_length (get_stack context)) ^ ".", l))
          else if not (s_eq hats (SAbstract (stack_take (get_stack context) pref_len, z))) then
            raise (TypeError ("call: block being called expects stack of type " ^ show_sigma hats ^
                              ", which doesn't match specified prefix.", l))
          else if i < pref_len then
            raise (TypeError ("call: return marker is stored at position " ^ string_of_int i ^
                              " on stack, which will not be in protected tail.", l))
          else
            begin match ret_addr_type (set_stack (set_reg context hatc) hats) hatq with
              | Some (TBox (PBlock (_, _,hats', QEpsilon e))) ->
                let new_pref_len = stack_pref_length hats' in
                if i' <> i + new_pref_len - pref_len then
                  raise (TypeError ("call: return marker, which started at position " ^ string_of_int i ^
                                    ", does not end up at specified position on stack.", l))
                else begin match hats' with
                  | SAbstract (_, z') when z = z' ->
                    if not (register_subset (TAL.chi_sub (EMarker (e, QI i')) (chi_sub (SType (z, s)) hatc)) (get_reg context)) then
                      raise (TypeError ("call: block being called expects register file with type " ^
                                        show_chi (TAL.chi_sub (EMarker (e, QI i')) (chi_sub (SType (z, s)) hatc)) ^
                                        " which is not compatible with current register file of type " ^
                                        show_chi (get_reg context) ^ ".", l))
                    else
                      ()
                  | _ ->
                    raise (TypeError ("call: block that will be returned to does not protect abstract stack suffix " ^ z ^ ".", l))
                end
              | _ -> raise (TypeError ("call: block being called to does not return to block with abstract return marker.", l))
            end
        | t -> raise (TypeError ("call: block being called does not follow calling convention: " ^ show t ^ ".", l))
      end
    | (Ihalt(l,_,_,_)::_), _ -> raise (TypeError ("halt: must be the last instruction in a block.", l))
    | (Iret(l,_,_)::_), _ -> raise (TypeError ("ret: must be the last instruction in a block.", l))
    | (Ijmp(l,_)::_), _ -> raise (TypeError ("jmp: must be the last instruction in a block.", l))
    | [Icall(l,_,_,_)], _ -> raise (TypeError ("call: return marker must be end{} or be on the stack.", l))
    | (Icall(l,_,_,_)::_), _ -> raise (TypeError ("call: must be the last instruction in a block.", l))
    | [], _ -> raise (TypeError ("Uh-oh! I found an empty block somewhere...", dummy_loc))


  and tc_u context u = let open TAL in match u with
    | UW (l,w) -> tc_w context w
    | UR (l,r) -> begin match List.Assoc.find (get_reg context) r with
        | None -> raise (TypeError ("Unbound register", l))
        | Some t -> t
      end
    | UPack (l,t, u, s, t') ->
      if tc_u context u = type_sub (TType (s,t')) t
      then TExists (s,t')
      else raise (TypeError ("Ill-typed existential", l))
    | UFold (l,s,t,u) ->
      if tc_u context u = type_sub (TType (s, TRec (s, t))) t
      then TRec (s,t)
      else raise (TypeError ("Ill-typed fold", l))
    | UApp (l, u, os) ->
      begin match tc_u context u with
        | TBox (PBlock (d,c,s,q)) ->
          let (ds,dr) = List.split_n d (List.length os) in
          List.fold_left
            ~f:(fun t' p -> type_sub p t')
            ~init:(TBox (PBlock (dr,c,s,q)))
            (type_zip ds os)
        | _ -> raise (TypeError ("Can't apply non-block to types", l))
      end

  and tc_w context w = let open TAL in match w with
    | WUnit l -> TUnit
    | WInt _ -> TInt
    | WLoc (l,loc) ->
      begin match List.Assoc.find (get_heap context) loc with
        | None -> raise (TypeError ("Unbound location", l))
        | Some (Box, t) -> TBox t
        | Some (Ref, PTuple ts) -> TTupleRef ts
        | _ -> raise (Failure "Impossible")
      end
    | WPack (l,t, w, s, t') ->
      if tc_w context w = type_sub (TType (s,t')) t
      then TExists (s,t')
      else raise (TypeError ("Ill-typed existential", l))
    | WFold (l,s,t,w) ->
      if tc_w context w = type_sub (TType (s, TRec (s, t))) t
      then TAL.TRec (s,t)
      else raise (TypeError ("Ill-typed fold", l))
    | WApp (l,w, os) ->
      begin match tc_w context w with
        | TBox (PBlock (d,c,s,q)) ->
          let (ds,dr) = List.split_n d (List.length os) in
          List.fold_left ~f:(fun t' p -> type_sub p t') ~init:(TBox (PBlock (dr,c,s,q))) (type_zip ds os)
        | _ -> raise (TypeError ("Can't apply non-block to types", l))
      end

  and tc_h context l mut h = match mut, h with
    | TAL.Box, TAL.HCode (d,c,s,q,is) ->
      let _ = tc_is (set_ret (set_stack (set_reg (set_tyenv context d) c) s) q) is in
      TAL.PBlock (d,c,s,q)
    | _, TAL.HTuple ws -> TAL.PTuple (List.map ~f:(tc_w context) ws)
    | _ -> raise (TypeError ("Can't have mutable code pointers",l))

  and tc_h_shallow context l mut h = match mut, h with
    | TAL.Box, TAL.HCode (d,c,s,q,is) -> TAL.PBlock (d,c,s,q)
    | _, TAL.HTuple ws -> TAL.PTuple (List.map ~f:(tc_w context) ws)
    | _  -> raise (TypeError ("Can't have mutable code pointers",l))

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
      EVar of l * string
    | EUnit of l
    | EInt of l * int
    | EBinop of l * exp * binop * exp
    | EIf0 of l * exp * exp * exp
    | ELam of l * (string * t) list * exp
    | ELamMod of l * (string * t) list * TAL.sigma_prefix * TAL.sigma_prefix * exp
    | EApp of l * exp * exp list
    | EFold of l * string * t * exp
    | EUnfold of l * exp
    | ETuple of l * exp list
    | EPi of l * int * exp
    | EBoundary of l * t * TAL.sigma option * TAL.component
  val show_exp : exp -> string
  val pp_exp : Format.formatter -> exp -> unit
  val get_loc : exp -> l


  type context =
      CHole
    | CBinop1 of l * context * binop * exp
    | CBinop2 of l * exp * binop * context
    | CIf0 of l * context * exp * exp
    | CApp1 of l * context * exp list
    | CAppn of l * exp * exp list * context * exp list
    | CFold of l * string * t * context
    | CUnfold of l * context
    | CTuple of l * exp list * context * exp list
    | CPi of l * int * context
    | CBoundary of l * t * TAL.sigma option * TAL.context
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
  let show t = Printer.(r (FP.p_t t))

  type binop = BPlus | BMinus | BTimes
  [@@deriving show]


  type exp =
      EVar of l * string
    | EUnit of l
    | EInt of l * int
    | EBinop of l * exp * binop * exp
    | EIf0 of l * exp * exp * exp
    | ELam of l * (string * t) list * exp
    | ELamMod of l * (string * t) list * TAL.sigma_prefix * TAL.sigma_prefix * exp
    | EApp of l * exp * exp list
    | EFold of l * string * t * exp
    | EUnfold of l * exp
    | ETuple of l * exp list
    | EPi of l * int * exp
    | EBoundary of l * t * TAL.sigma option * TAL.component
  [@@deriving show]
  let show_exp e = Printer.(r (FP.p_exp e))
  let get_loc = function
    | EVar (l,_)
    | EUnit l
    | EInt (l,_)
    | EBinop (l,_,_,_)
    | EIf0 (l,_,_,_)
    | ELam (l,_,_)
    | ELamMod (l,_,_,_,_)
    | EApp (l,_,_)
    | EFold (l,_,_,_)
    | EUnfold (l,_)
    | ETuple (l,_)
    | EPi (l,_,_)
    | EBoundary (l,_,_,_) -> l


  let rec value e =
    match e with
    | EUnit l -> true
    | EInt _ -> true
    | ELam _ -> true
    | ELamMod _ -> true
    | EFold _ -> true
    | ETuple (l,es) -> List.for_all ~f:value es
    | _ -> false

  type context =
      CHole
    | CBinop1 of l * context * binop * exp
    | CBinop2 of l * exp * binop * context
    | CIf0 of l * context * exp * exp
    | CApp1 of l * context * exp list
    | CAppn of l * exp * exp list * context * exp list
    | CFold of l * string * t * context
    | CUnfold of l * context
    | CTuple of l * exp list * context * exp list
    | CPi of l * int * context
    | CBoundary of l * t * TAL.sigma option * TAL.context
  [@@deriving show]
  let show_context c = Printer.(r (FP.p_context c))

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
      t_eq b1 (type_sub (FTAL.FType (s2, TVar s1)) b2)
    | TTuple ts, TTuple ts1 -> List.for_all2_exn ~f:t_eq ts ts1
    | _ -> false


  let rec sub p e =
    match e with
    | EVar (_,x) -> begin match p with
        | FTAL.FTerm (x', e') when x = x' -> e'
        | _ -> e
      end
    | EUnit _ -> e
    | EInt _ -> e
    | EBinop (l, e1, b, e2) -> EBinop (l, sub p e1, b, sub p e2)
    | EIf0 (l, e1, e2, e3) -> EIf0 (l, sub p e1, sub p e2, sub p e3)
    | ELam (l, args, body) ->
      begin match p with
        | FTAL.FTerm (x', e') when List.Assoc.mem args x' -> e
        | _ -> ELam (l, args, sub p body)
      end
    | ELamMod (l, args, sin, sout, body) ->
      begin match p with
        | FTAL.FTerm (x', e') when List.Assoc.mem args x' -> e
        | _ -> ELamMod (l,args, sin, sout, sub p body)
      end
    | EApp (l, e1, eargs) ->
      EApp (l, sub p e1, List.map ~f:(sub p) eargs)
    | EFold (l, s, t, e1) ->
      begin match p with
        | FTAL.FType (a, t') when a = s -> e
        | _ -> EFold (l, s, t, sub p e1)
      end
    | EUnfold (l, e1) -> EUnfold (l, sub p e1)
    | ETuple (l, es) -> ETuple (l, List.map ~f:(sub p) es)
    | EPi (l, n, e1) -> EPi (l, n, sub p e1)
    | EBoundary (l, t, s, comp) -> EBoundary (l, type_sub p t, Option.(s >>| TAL.stack_sub p), TAL.sub p comp)

  let step_prim (m, e) =
    match e with
    | EBinop (l, EInt (_, n1), BPlus, EInt (_, n2)) -> (m, EInt (l, n1 + n2))
    | EBinop (l, EInt (_, n1), BMinus, EInt (_, n2)) -> (m, EInt (l, n1 - n2))
    | EBinop (l, EInt (_, n1), BTimes, EInt (_, n2)) -> (m, EInt (l, n1 * n2))
    | EIf0 (_, EInt (_, 0), e2, e3) -> (m, e2)
    | EIf0 (_, EInt _, e2, e3) -> (m, e3)
    | EApp (_, ELam (_, ps, body), eargs) when List.(length ps = length eargs) ->
      (m, List.fold_left ~f:(fun e p -> sub p e) ~init:body (List.map2_exn ~f:(fun (x,_) e -> FTAL.FTerm (x,e)) ps eargs))
    | EApp (_, ELamMod (_, ps, sin, sout, body), eargs) when List.(length ps = length eargs) ->
      (m, List.fold_left ~f:(fun e p -> sub p e) ~init:body (List.map2_exn ~f:(fun (x,_) e -> FTAL.FTerm (x,e)) ps eargs))
    | EUnfold (_, EFold (_,_,_,eb)) -> (m, eb)
    | EPi (_, n, (ETuple (_, vs))) when List.length vs > n -> (m, List.nth_exn vs n)
    | EBoundary (_, t, s, (_,[TAL.Ihalt (_, t',s',r)],[])) when TAL.t_eq (FTAL.tytrans t) t' ->
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
  let show_ft = function
    | F e -> F.show_exp e
    | TC c -> TAL.show_component c
    | TI is -> TAL.show_instrs is

  let rec decomp e =
    match e with
    | EVar _ -> None
    | EUnit _ -> None
    | EInt _ -> None
    | ELam _ -> None
    | EFold _ -> None

    | EBinop (l, e1, b, e2) when not (value e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CBinop1 (l, ctxt, b, e2), e'))
    | EBinop (l, e1, b, e2) when value e1 && not (value e2) ->
      decomp_cont e2 (fun ctxt e' -> Some (CBinop2 (l, e1, b, ctxt), e'))
    | EBinop (_, e1, b, e2) when value e1 && value e2 -> Some (CHole, F e)

    | EIf0 (l, e1, e2, e3) when not (value e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CIf0 (l, ctxt, e2, e3), e'))
    | EIf0 (_, e1, e2, e3) when value e1 ->
      Some (CHole, F e)

    | EApp (l, e1, eargs) when not (value e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CApp1 (l, ctxt, eargs), e'))
    | EApp (l, e1, eargs) when value e1 && List.exists ~f:(fun x -> not (value x)) eargs ->
      decomp_list eargs (fun bef ctxt aft e' -> Some (CAppn (l, e1, bef, ctxt, aft), e'))
    | EApp (_, e1, eargs) -> Some (CHole, F e)

    | EUnfold (_, e1) when value e1 -> Some (CHole, F e)
    | EUnfold (l, e1) -> decomp_cont e1 (fun ctxt e' -> Some (CUnfold (l, ctxt), e'))

    | ETuple (l, es) ->
      decomp_list es (fun bef ctxt aft e' -> Some (CTuple (l, bef, ctxt, aft), e'))

    | EPi (_, n, e1) when value e1 -> Some (CHole, F e)
    | EPi (l, n, e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CPi (l, n, ctxt), e'))

    | EBoundary (l, t, s, comp) ->
      begin match TAL.decomp comp with
          None -> Some (CHole, F e)
        | Some (ctxt, e') -> Some (CBoundary (l, t, s, ctxt), e')
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
    | CBinop1 (l, ctxt', b, e1) -> EBinop (l, plug ctxt' e, b, e1)
    | CBinop2 (l, e1, b, ctxt') -> EBinop (l, e1, b, plug ctxt' e)
    | CIf0 (l, ctxt', e1, e2) -> EIf0 (l, plug ctxt' e, e1, e2)
    | CApp1 (l, ctxt', es) -> EApp (l, plug ctxt' e, es)
    | CAppn (l, ef, bef, ctxt', aft) -> EApp (l, ef, List.concat [bef; [plug ctxt' e]; aft])
    | CFold (l, s, t, ctxt') -> EFold (l, s, t, plug ctxt' e)
    | CUnfold (l, ctxt') -> EUnfold (l, plug ctxt' e)
    | CTuple (l, bef, ctxt', aft) -> ETuple (l, List.concat [bef; [plug ctxt' e]; aft])
    | CPi (l, n, ctxt') -> EPi (l, n, plug ctxt' e)
    | CBoundary (l, t,s,talctxt) -> EBoundary (l, t, s, TAL.plug talctxt e)



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
      let _ = Debug.log "decomp TI instrs" (String.concat "; " (List.map ~f:(fun i -> TAL.show_instr i) is)) in
      let _ = Debug.log "decomp TI regs" (TAL.show_regm r) in
      let _ = Debug.log "decomp TI stack" (TAL.show_stackm s) in
      let (m', is') = TAL.reduce (m, is) in
      let (h',r',s') = m' in
      let _ = Debug.log "stepped TI instrs" (String.concat "; " (List.map ~f:(fun i -> TAL.show_instr i) is')) in
      let _ = Debug.log "stepped TI regs" (TAL.show_regm r') in
      let _ = Debug.log "stepped TI stack" (TAL.show_stackm s') in
      let _ = Debug.log "stepped TI heap" (TAL.show_heapm h') in
      (m', plug ctxt (TI is'))
    | Some (ctxt, TC (l,is,h)) ->
      let m' = TAL.load m h in
      (m', plug ctxt (TC (l,is, [])))
    | None -> (m, e)


  let stepn n e =
    let rec stepn' n l e =
      let () = Debug.log "step" (string_of_int n) in
      match l, n with
      |_, 0 -> e
      | Some e', _ when e = e' -> e
      | _ -> stepn' (n - 1) (Some e) (step e)
    in stepn' n None e


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

  and mut = Ref | Box

  and psi = (loc * (mut * psi_elem)) list

  and chi = (reg * t) list

  val ret_type : FTAL.context -> q -> (FTAL.t * sigma) option
  val ret_addr_type : FTAL.context -> q -> t option

  val stack_cons : t -> sigma -> sigma
  val stack_take : sigma -> int -> sigma_prefix
  val stack_drop : sigma -> int -> sigma
  val stack_pref_length : sigma -> int
  val stack_prepend : sigma_prefix -> sigma -> sigma
  val stack_nth : sigma -> int -> t option
  val stack_nth_exn : sigma -> int -> t

  val register_subset : chi -> chi -> bool

  val show : t -> string
  val pp : Format.formatter -> t -> unit
  val t_eq : t -> t -> bool
  val show_sigma : sigma -> string
  val pp_sigma : Format.formatter -> sigma -> unit
  val show_sigma_prefix : sigma_prefix -> string
  val pp_sigma_prefix : Format.formatter -> sigma_prefix -> unit
  val s_eq : sigma -> sigma -> bool
  val s_pref_eq : sigma_prefix -> sigma_prefix -> bool
  val show_q : q -> string
  val pp_q : Format.formatter -> q -> unit
  val q_eq : q -> q -> bool
  val show_psi : psi -> string
  val pp_psi : Format.formatter -> psi -> unit
  val psi_elem_eq : psi_elem -> psi_elem -> bool
  val show_psi_elem : psi_elem -> string
  val show_chi : chi -> string

  type omega =
      OT of t
    | OS of sigma
    | OQ of q
  val show_omega : omega -> string

  type w =
      WUnit of l
    | WInt of l * int
    | WLoc of l * loc
    | WPack of l * t * w * string * t
    | WFold of l * string * t * w
    | WApp of l * w * omega list
  val show_w : w -> string


  type u =
      UW of l * w
    | UR of l * reg
    | UPack of l * t * u * string * t
    | UFold of l * string * t * u
    | UApp of l * u * omega list
  val show_u : u -> string

  type aop = Add | Sub | Mult
  val show_aop : aop -> string

  type instr =
      Iaop of l * aop * reg * reg * u
    | Ibnz of l * reg * u
    | Ild of l * reg * reg * int
    | Ist of l * reg * int * reg
    | Iralloc of l * reg * int
    | Iballoc of l * reg * int
    | Imv of l * reg * u
    | Iunpack of l * string * reg * u
    | Iunfold of l * reg * u
    | Isalloc of l * int
    | Isfree of l * int
    | Isld of l * reg * int
    | Isst of l * int * reg
    | Ijmp of l * u
    | Icall of l * u * sigma * q
    | Iret of l * reg * reg
    | Ihalt of l * t * sigma * reg
    | Iprotect of l * sigma_prefix * string
    | Iimport of l * reg * string * sigma * F.t * F.exp
  val show_instr : instr -> string
  val show_instrs : instr list -> string
  val pp_instr : Format.formatter -> instr -> unit

  type h =
      HCode of delta * chi * sigma * q * instr list
    | HTuple of w list
  val show_h : h -> string

  type heapm = (loc * (mut * h)) list
  val show_heapm : heapm -> string

  type regm = (reg * w) list
  val show_regm : regm -> string

  type stackm = w list
  val show_stackm : stackm -> string

  type mem = heapm * regm * stackm

  val load : mem -> heapm -> mem

  type component = l * instr list * heapm
  val show_component : component -> string
  val pp_component : Format.formatter -> component -> unit

  type context =
      CComponentEmpty of l * contextI
    | CComponentHeap of l * contextC

  and contextI =
      CHoleI
    | CImportI of l * reg * string * sigma * F.t * F.context * instr list

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

  val chi_sub : FTAL.substitution -> chi -> chi

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

  and psi_elem =
      PBlock of delta * chi * sigma * q
    | PTuple of t list


  and mut = Ref | Box

  and psi = (loc * (mut * psi_elem)) list

  and chi = (reg * t) list

  let show_sigma s = Printer.(r (TALP.p_s s))
  let show_sigma_prefix s = Printer.(r (TALP.p_sigma_prefix s))
  let show t = Printer.(r (TALP.p_t t))
  let show_psi_elem p = Printer.(r (TALP.p_psi p))
  let show_q q = Printer.(r (TALP.p_q q))
  let show_chi c = Printer.(r (TALP.p_chi c))

  let ret_type context q = match q with
    | QR r -> begin match List.Assoc.find (FTAL.get_reg context) r with
        | Some (TBox (PBlock ([], [(r,t)], s, _))) -> Some (FTAL.TT t, s)
        | _ -> None
      end
    | QI i -> begin match TAL.stack_nth (FTAL.get_stack context) i with
        | Some (TBox (PBlock ([], [(r,t)], s, _))) -> Some (FTAL.TT t, s)
        | _ -> None
      end
    | QEpsilon _ -> None
    | QEnd (t, s) -> Some (FTAL.TT t, s)
    | QOut -> None

  let ret_addr_type context q = match q with
    | QR r -> begin match List.Assoc.find (FTAL.get_reg context) r with
        | Some (TBox (PBlock ([], [(_,_)], _, _))) ->
          Some (List.Assoc.find_exn (FTAL.get_reg context) r)
        | _ -> None
      end
    | QI i -> begin match TAL.stack_nth (FTAL.get_stack context) i with
        | Some (TBox (PBlock ([], [(_,_)], s, _))) ->
          Some (TAL.stack_nth_exn (FTAL.get_stack context) i)
        | _ -> None
      end
    | QEpsilon _
    | QEnd _
    | QOut -> None

  type omega =
      OT of t
    | OS of sigma
    | OQ of q
  [@@deriving show]
  let show_omega o = Printer.(r (TALP.p_o o))

  type omega_list = omega list
  [@@deriving show]

  type w =
      WUnit of l
    | WInt of l * int
    | WLoc of l * loc
    | WPack of l * t * w * string * t
    | WFold of l * string * t * w
    | WApp of l * w * omega list
  [@@deriving show]
  let show_w w = Printer.(r (TALP.p_w w))

  type u =
      UW of l * w
    | UR of l * reg
    | UPack of l * t * u * string * t
    | UFold of l * string * t * u
    | UApp of l * u * omega list
  [@@deriving show]
  let show_u u = Printer.(r (TALP.p_u u))

  type aop = Add | Sub | Mult
  [@@deriving show]

  type instr =
      Iaop of l * aop * reg * reg * u
    | Ibnz of l * reg * u
    | Ild of l * reg * reg * int
    | Ist of l * reg * int * reg
    | Iralloc of l * reg * int
    | Iballoc of l * reg * int
    | Imv of l * reg * u
    | Iunpack of l * string * reg * u
    | Iunfold of l * reg * u
    | Isalloc of l * int
    | Isfree of l * int
    | Isld of l * reg * int
    | Isst of l * int * reg
    | Ijmp of l * u
    | Icall of l * u * sigma * q
    | Iret of l * reg * reg
    | Ihalt of l * t * sigma * reg
    | Iprotect of l * sigma_prefix * string
    | Iimport of l * reg * string * sigma * F.t * F.exp
  [@@deriving show]
  let show_instr i = Printer.(r (TALP.p_instr i))
  let show_instrs is = Printer.(r (TALP.p_instruction_sequence is))

  type h =
      HCode of delta * chi * sigma * q * instr list
    | HTuple of w list
  [@@deriving show]
  let show_h h = Printer.(r (TALP.p_h h))

  type heapm = (loc * (mut * h)) list
  [@@deriving show]
  let show_heapm m = Printer.(r (TALP.p_heapm m))
  type regm = (reg * w) list
  let show_regm m = Printer.(r (TALP.p_regm m))
  type stackm = w list
  let show_stackm m = Printer.(r (TALP.p_stackm m))
  type mem = heapm * regm * stackm

  let stack_cons t s = match s with
    | SConcrete l -> SConcrete (t::l)
    | SAbstract (l,a) -> SAbstract (t::l,a)

  let stack_take s n = match s with
    | SConcrete l | SAbstract (l,_) -> List.take l n

  let stack_drop s n = match s with
    | SConcrete l -> SConcrete (List.drop l n)
    | SAbstract (l,a) -> SAbstract (List.drop l n, a)

  let stack_pref_length s = match s with
    | SConcrete l | SAbstract (l,_) -> List.length l

  let stack_prepend p s = match s with
    | SConcrete l -> SConcrete (List.append p l)
    | SAbstract (l,a) -> SAbstract (List.append p l, a)

  let stack_nth s n = match s with
    | SConcrete l | SAbstract (l,_) -> List.nth l n

  let stack_nth_exn s n = match s with
    | SConcrete l | SAbstract (l,_) -> List.nth_exn l n

  let load (h,r,s) h' =
    (* NOTE(dbp 2016-09-08): We should do renaming, but relying, for now, on the fact
       that we always gensym new location names, so not renaming should be safe. *)
    (List.append h' h, r, s)

  type component = l * instr list * heapm
  [@@deriving show]
  let show_component c = Printer.(r (TALP.p_component c))

  type context =
      CComponentEmpty of l * contextI
    | CComponentHeap of l * contextC
  [@@deriving show]

  and contextI =
      CHoleI
    | CImportI of l * reg * string * sigma * F.t * F.context * instr list
  [@@deriving show]

  and contextC =
      CHoleC
  [@@deriving show]

  let show_context c = Printer.(r (TALP.p_context c))

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
    | CComponentEmpty (l, ctxt') ->
      begin match ctxt' with
        | CHoleI -> (l, un_ti e, [])
        | CImportI (l, r,z,s,t,ctxt',is) -> (l, Iimport (l, r,z,s,t,F.plug ctxt' e)::is, [])
      end
    | CComponentHeap (l, CHoleC) -> un_tc e

  let rec sub p ((loc,is, hm) : component) : component =
    (loc, List.map ~f:(instr_sub p) is,
     List.map ~f:(fun (l,h) ->
         match h with
         | (m, HCode (d,c,s,q,is)) -> (l, (m, HCode (d,c,s,q, List.map ~f:(instr_sub p) is)))
         | _ -> (l,h)
       ) hm)

  and instr_sub p i = match i with
    | Iaop (l, op, r1, r2, u) -> Iaop (l, op, r1, r2, u_sub p u)
    | Ibnz (l, r,u) -> Ibnz (l, r, u_sub p u)
    | Imv (l, r,u) -> Imv (l, r, u_sub p u)
    | Iunpack (l, a,r,u) -> Iunpack (l, a,r,u_sub p u)
    | Iunfold (l, r,u) -> Iunfold (l, r, u_sub p u)
    | Ijmp (l, u) -> Ijmp (l, u_sub p u)
    | Icall (l, u,s,q) -> Icall (l, u_sub p u, stack_sub p s, retmarker_sub p q)
    | Ihalt (l, t,s,r) -> Ihalt (l, type_sub p t, stack_sub p s, r)
    | Iimport (l, r,z,s,t,e) -> Iimport (l, r,z,stack_sub p s,F.type_sub p t,F.sub p e)
    | _ -> i

  and u_sub p u = match u with
    | UW (l, w) -> UW (l, w_sub p w)
    | UR _ -> u
    | UPack (l, t',ubody,a,t) -> begin match p with
        | FTAL.TType (a', _) when a = a' ->
          UPack (l, type_sub p t', ubody, a, t)
        | _ -> UPack (l, type_sub p t', u_sub p ubody, a, type_sub p t)
      end
    | UFold (l, a, t, ubody) -> begin match p with
        | FTAL.TType (a', _) when a = a' -> u
        | _ -> UFold (l, a, type_sub p t, u_sub p ubody)
      end
    | UApp (l, ubody, os) -> UApp (l, u_sub p ubody, List.map ~f:(omega_sub p) os)

  and w_sub p w = match w with
    | WPack (l, t',wbody,a,t) -> begin match p with
        | FTAL.TType (a', _) when a = a' ->
          WPack (l, type_sub p t', wbody, a, t)
        | _ -> WPack (l, type_sub p t', w_sub p wbody, a, type_sub p t)
      end
    | WFold (l, a,t,wbody) -> begin match p with
        | FTAL.TType (a', _) when a = a' -> w
        | _ -> WFold (l, a, type_sub p t, w_sub p wbody)
      end
    | WApp (l, wbody, os) -> WApp (l, w_sub p wbody, List.map ~f:(omega_sub p) os)
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
    | QEnd (t',s) -> begin match p with
        | FTAL.SAbs (s', a) ->
          let news = match s, s' with
            | SAbstract (lold, z), SAbstract (lhide, z') when
                z = z' && List.length lold >= List.length lhide && (List.drop lold (List.length lold - List.length lhide)) = lhide ->
              SAbstract (List.take lold (List.length lold - List.length lhide), a)
            | SConcrete lold, SConcrete lhide when
                List.length lold >= List.length lhide && (List.drop lold (List.length lold - List.length lhide)) = lhide ->
              SAbstract (List.take lold (List.length lold - List.length lhide), a)
            | _ -> stack_sub p s in
          QEnd (type_sub p t', news)
        | _ -> QEnd (type_sub p t', stack_sub p s)
      end
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
    | TUnit | TInt -> t

  and stack_sub p s = match s with
    | SAbstract (pref, z) -> begin match p with
        | FTAL.SType (z', s') when z = z' -> begin match s' with
            | SConcrete rest ->
              SConcrete (List.append (List.map ~f:(type_sub p) pref) rest)
            | SAbstract (some, var) ->
              SAbstract (List.append (List.map ~f:(type_sub p) pref) some, var)
          end
        | _ -> SAbstract (List.map ~f:(type_sub p) pref, z)
      end
    | SConcrete ts -> SConcrete (List.map ~f:(type_sub p) ts)

  and omega_sub p o = match o with
    | OT t -> OT (type_sub p t)
    | OS s -> OS (stack_sub p s)
    | OQ q -> OQ (retmarker_sub p q)

  and chi_sub p c = List.map ~f:(fun (r,t) -> (r, type_sub p t)) c


  let option_cons o1 o2 = match o1,o2 with
    | _, None -> None
    | None, Some xs -> Some xs
    | Some x, Some xs -> Some (x::xs)

  let rec delta_rebindings d1 d2 =
    match d1,d2 with
    | DAlpha a1::d1', DAlpha a2::d2' ->
      option_cons
        (if a1 = a2 then None
         else Some (FTAL.TType (a1,TVar a2)))
        (delta_rebindings d1' d2')
    | DZeta a1::d1', DZeta a2::d2'->
      option_cons
        (if a1 = a2 then None
         else Some (FTAL.SType (a1,SAbstract ([], a2))))
        (delta_rebindings d1' d2')
    | DEpsilon a1::d1', DEpsilon a2::d2' ->
      option_cons
        (if a1 = a2 then None
         else Some (FTAL.EMarker (a1,QEpsilon a2)))
        (delta_rebindings d1' d2')
    | [], [] -> Some []
    | _ -> None


  let rec t_eq t1 t2 = match t1, t2 with
    | TVar v1, TVar v2 -> v1 = v2
    | TUnit, TUnit -> true
    | TInt, TInt -> true
    | TExists (a1, b1), TExists (a2, b2) ->
      t_eq b1 (type_sub (FTAL.TType (a2, TVar a1)) b2)
    | TRec (a1, b1), TRec (a2, b2) ->
      t_eq b1 (type_sub (FTAL.TType (a2, TVar a1)) b2)
    | TTupleRef ts1, TTupleRef ts2 ->
      List.for_all2_exn ~f:t_eq ts1 ts2
    | TBox (PBlock (d1, c1, s1, q1)), TBox (PBlock (d2, c2, s2, q2)) ->
      begin match delta_rebindings d2 d1 with
        | None -> false
        | Some binds ->
          let c1 = List.sort (fun (a,_) (b,_) -> compare a b) c1 in
          let c2 = List.sort (fun (a,_) (b,_) -> compare a b) c2 in
          let s2' = List.fold_left ~f:(fun s b -> stack_sub b s) ~init:s2 binds in
          let q2' = List.fold_left ~f:(fun q b -> retmarker_sub b q) ~init:q2 binds in
          List.length c1 = List.length c2 &&
          List.for_all2_exn ~f:(fun (r1, t1) (r2, t2) ->
              let t2' = List.fold_left
                  ~f:(fun t' b -> type_sub b t')
                  ~init:t2 binds in
              r1 = r2 && t_eq t1 t2') c1 c2 &&
          s_eq s1 s2' &&
          q_eq q1 q2'
      end
    | TBox (PTuple ts1), TBox (PTuple ts2) ->
      List.for_all2_exn ~f:t_eq ts1 ts2
    | _ -> false

  and s_eq s1 s2 = match s1,s2 with
    | SAbstract (pr1, z1), SAbstract (pr2, z2) -> list_for_all2 ~f:t_eq pr1 pr2 && z1 = z2
    | SConcrete ts1, SConcrete ts2 -> list_for_all2 ~f:t_eq ts1 ts2
    | _ -> false

  and s_pref_eq s1 s2 = list_for_all2 ~f:t_eq s1 s2

  and q_eq q1 q2 = match q1, q2 with
    | QR r1, QR r2 -> r1 = r2
    | QI i1, QI i2 -> i1 = i2
    | QEpsilon e1, QEpsilon e2 -> e1 = e2
    | QEnd (t1, s1), QEnd (t2, s2) ->
      t_eq t1 t2 && s_eq s1 s2
    | QOut, QOut -> true
    | _ -> false

  and psi_elem_eq p1 p2 = t_eq (TBox p1) (TBox p2)

  and chi_eq c1 c2 =
    let s = List.sort ~cmp:(fun (a1,_) (a2,_) -> compare a1 a2) in
    list_for_all2 ~f:(fun (r1,t1) (r2,t2) -> r1 = r1 && t_eq t1 t2) (s c1) (s c2)

  let register_subset c1 c2 =
    (list_subset (List.map ~f:fst c1) (List.map ~f:fst c2)) &&
    (List.for_all c1 ~f:(fun (r,t) -> t_eq t (List.Assoc.find_exn c2 r)))


  let decomp (loc, is, m) =
    match m with
    | [] ->
      begin match is with
        | [] -> None
        | Ihalt _ :: _ -> None
        | Iimport (l,r,z,s,t,e) :: rest ->
          begin match F.decomp e with
            | None -> if F.value e then Some (CComponentEmpty (loc, CHoleI), F.TI is) else None
            | Some (ctxt, e') -> Some (CComponentEmpty (loc, CImportI (l, r, z, s, t, ctxt, rest)), e')
          end
        | _ -> Some (CComponentEmpty (loc, CHoleI), F.TI is)
      end
    | _ -> Some (CComponentHeap (loc, CHoleC), F.TC (loc, is, m))

  let rec ru r = function
    | UApp (l, u, o) -> WApp (l, ru r u, o)
    | UPack (l, t1, u, s, t2) -> WPack (l, t1, ru r u, s, t2)
    | UFold (l, s, t, u) -> WFold (l, s, t, ru r u)
    | UW (_, w) -> w
    | UR (_, rn) -> List.Assoc.find_exn r rn

  let delta op w1 w2 =
    match (op, w1, w2) with
    | (Add, WInt (l, n1), WInt (_, n2)) -> WInt (l, n1 + n2)
    | (Sub, WInt (l, n1), WInt (_, n2)) -> WInt (l, n1 - n2)
    | (Mult, WInt (l, n1), WInt (_, n2)) -> WInt (l, n1 * n2)
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
    List.rev (List.fold_left ~f:(fun acc i -> (List.fold_left ~f:(fun i' p -> instr_sub p i') ~init:i subs)::acc) ~init:[] is)

  let reduce (c : mem * instr list) =
    match c with
    | ((hm,rm,sm), Iaop (_, op, rd, rs, u)::is) ->
      ((hm, replace rm rd (delta op (List.Assoc.find_exn rm rs) (ru rm u)), sm), is)
    | ((hm,rm,sm), Ibnz (_, r,u)::is) ->
      begin match List.Assoc.find rm r with
        | Some (WInt (_, 0)) -> ((hm,rm,sm), is)
        | Some (WInt _) ->
          let hc os l =
            match List.Assoc.find hm l with
            | Some (_, (HCode (delt,ch,s,qr,is))) ->
              instrs_sub delt os is
            | _ -> raise (Failure "branching to missing or non-code")
          in
          begin match ru rm u with
            | WLoc (_, l) -> ((hm,rm,sm), hc [] l)
            | WApp (_, WLoc (_, l), os) -> ((hm,rm,sm), hc os l)
            | _ -> raise (Failure "branching to non-loc")
          end
        | _ -> raise (Failure "branching to on missing or non-int")
      end
    | ((hm,rm,sm), Ild (_, rd,rs,i)::is) ->
      begin match List.Assoc.find_exn rm rs with
        | WLoc (_, l) ->
          begin match List.Assoc.find hm l with
            | Some (_, HTuple ws) when List.length ws > i ->
              ((hm, replace rm rd (List.nth_exn ws i), sm), is)
            | Some (_, HTuple _) -> raise (Failure "ld: tuple index out of bounds")
            | _ -> raise (Failure "ld: trying to load from missing or non-tuple")
          end
        | _ -> raise (Failure "ld: trying to load from non-location")
      end
    | ((hm,rm,sm), Ist (_, rd,i,rs)::is) ->
      begin match List.Assoc.find rm rd with
        | Some (WLoc (_, l)) ->
          begin match List.Assoc.find hm l with
            | Some (Ref, HTuple ws) when List.length ws > i ->
              (((replace hm l (Ref, HTuple (list_replace i ws (List.Assoc.find_exn rm rs)))), rm, sm), is)
            | Some (Box, HTuple ws) ->
              raise (Failure "st: can't write to immutable tuple")
            | Some (_, HTuple _) -> raise (Failure "st: tuple index out of bounds")
            | _ -> raise (Failure "st: trying to store to missing or non-tuple")
          end
        | _ -> raise (Failure "st: trying to store to missing or non-location")
      end
    | ((hm,rm,sm), Iralloc (l',rd,n)::is) when List.length sm >= n ->
      let l = FTAL.gen_sym () in (((l, (Ref, HTuple (List.take sm n))) :: hm, replace rm rd (WLoc (l',l)), List.drop sm n), is)
    | ((hm,rm,sm), Iballoc (l',rd,n)::is) when List.length sm >= n ->
      let l = FTAL.gen_sym () in (((l, (Box, HTuple (List.take sm n))) :: hm, replace rm rd (WLoc (l',l)), List.drop sm n), is)
    | ((hm,rm,sm), Imv (_,rd,u)::is) ->
      ((hm, replace rm rd (ru rm u), sm), is)
    | ((hm,rm,sm), Iunpack (_,a,rd,u)::is) ->
      begin match ru rm u with
        | WPack (_,t1,w,a,t2) -> ((hm, replace rm rd w, sm), instrs_sub [DAlpha a] [OT t1] is)
        | _ -> raise (Failure "unpack: trying to unpack non-pack")
      end
    | ((hm,rm,sm), Iunfold (_,rd, u)::is) ->
      begin match ru rm u with
        | WFold (_,a,t,w) -> ((hm, replace rm rd w, sm), is)
        | _ -> raise (Failure "unfold: trying to unpack non-pack")
      end
    | ((hm,rm,sm), Isalloc (l,n)::is) ->
      ((hm,rm,List.append (List.init ~f:(fun _ -> WUnit l) n) sm), is)
    | ((hm,rm,sm), Isfree (_,n)::is) when List.length sm >= n ->
      ((hm,rm,List.drop sm n), is)
    | ((hm,rm,sm), Isld (_,rd,i)::is) when List.length sm > i ->
      ((hm, replace rm rd (List.nth_exn sm i), sm), is)
    | ((hm,rm,sm), Isst (_,i,rs)::is) when List.length sm > i ->
      ((hm,rm,list_replace i sm (List.Assoc.find_exn rm rs)), is)
    | ((hm,rm,sm), Ijmp (_,u)::is) ->
      let hc os l =
        match List.Assoc.find hm l with
        | Some (_, HCode (delt,ch,s,qr,is)) -> instrs_sub delt os is
        | _ -> raise (Failure "jumping to missing or non-code")
      in
      begin match ru rm u with
        | WLoc (_,l) -> ((hm,rm,sm), hc [] l)
        | WApp (_,WLoc (_,l), os) -> ((hm,rm,sm), hc os l)
        | _ -> raise (Failure "jmp: trying to jump to non-location")
      end
    | ((hm,rm,sm), Icall (_,u,s,q)::is) ->
      let hc os l =
        match List.Assoc.find hm l with
        | Some (_, HCode (delt,ch,s,qr,is)) ->
          instrs_sub delt (List.append os [OS s; OQ q]) is
        | _ -> raise (Failure "calling to missing or non-code")
      in
      begin match ru rm u with
        | WLoc (_, l) -> ((hm,rm,sm), hc [] l)
        | WApp (_, WLoc (_,l), os) -> ((hm,rm,sm), hc os l)
        | _ -> raise (Failure "call: trying to jump to non-location")
      end
    | ((hm,rm,sm), Iret (_,rloc,_)::is) ->
      let hc os l =
        match List.Assoc.find hm l with
        | Some (_, HCode (delt,ch,s,qr,is)) -> instrs_sub delt os is
        | _ -> raise (Failure "returning to missing or non-code")
      in
      begin match List.Assoc.find rm rloc with
        | Some (WLoc (_,l)) -> ((hm,rm,sm), hc [] l)
        | Some (WApp (_,WLoc (_,l), os)) -> ((hm,rm,sm), hc os l)
        | _ -> raise (Failure ("ret: trying to return to missing or non-location " ^ rloc))
      end
    | ((hm,rm,sm), Iimport (l,r,z,s,t,v)::is) ->
      let (m, w) = FTAL.tf t v (hm,rm,sm) in
      (m, Imv (l,r, UW (l, w))::is)
    | ((hm,rm,sm), Iprotect (_,_,_)::is) ->
      ((hm,rm,sm), is)
    | _ -> c

end and Printer : sig
  open PPrint
  val r : document -> string

end = struct
  let r d =
    let b = Buffer.create 100 in
    PPrint.ToBuffer.pretty 0.8 80 b d;
    Buffer.contents b
end and TALP : sig
    open PPrint
    val p_w : TAL.w -> document
    val p_t : TAL.t -> document
    val p_o : TAL.omega -> document
    val p_s : TAL.sigma -> document
    val p_sigma_prefix : TAL.sigma_prefix -> document
    val p_q : TAL.q -> document
    val p_u : TAL.u -> document
    val p_h : TAL.h -> document
    val p_psi : TAL.psi_elem -> document
    val p_delta : TAL.delta -> document
    val p_chi : TAL.chi -> document
    val p_instr : TAL.instr -> document
    val p_regm : TAL.regm -> document
    val p_stackm : TAL.stackm -> document
    val p_heapm : TAL.heapm -> document
    val p_component : TAL.component -> document
    val p_instruction_sequence : TAL.instr list -> document
    val p_context : TAL.context -> document
end = struct
  open PPrint;;
  open TAL

  let p_sequence (ds: document list) =
    group @@ brackets @@ align @@ group @@ separate (comma ^^ break 1) ds
  and p_sequence_map f xs =
    group @@ brackets @@ align @@ group @@ separate_map (comma ^^ break 1) f xs

  let args docs = break 0 ^^ separate (comma ^^ break 1) docs

  let p_nat n = !^(string_of_int n)

  let rec p_w (w : w) : document =
    group @@ match w with
    | WUnit _ -> lparen ^^ rparen
    | WInt (_,n) -> !^(string_of_int n)
    | WLoc (_,l) -> !^l
    | WPack (_,t',w,a,t) ->
      pack_h t' (p_w w) a t
    | WFold (_,a,t,w) -> fold_h a t (p_w w)
    | WApp (_,w,os) -> app_h (p_w w) os
  and p_t (t : t) : document =
    group @@ match t with
    | TVar a -> !^a
    | TUnit -> !^"unit"
    | TInt -> !^"int"
    | TExists (a,t) -> !^"exists " ^^ p_t (TVar a) ^^ dot ^^ p_t t
    | TRec (a,t) -> !^"mu " ^^ p_t (TVar a) ^^ dot ^^ p_t t
    | TTupleRef ts -> p_mut Ref ^^ space ^^ p_psi (PTuple ts)
    | TBox p -> p_mut Box ^^ space ^^ p_psi p
  and p_o (o : omega) : document =
    group @@ match o with
    | OT t -> p_t t
    | OS s -> p_s s
    | OQ q -> p_q q
  and p_s (s : sigma) : document =
    group @@ match s with
    | SConcrete l ->
      if List.length l > 0 then
        p_sigma_prefix l ^^ !^" *"
      else !^"*"
    | SAbstract (l, z) ->
      if List.length l > 0 then
        p_sigma_prefix l ^^ !^" " ^^ !^z
      else !^z
  and p_sigma_prefix (p : sigma_prefix) : document =
    let rec loop = function
      | [] -> !^"::"
      | [t] -> p_t t ^^ !^"::"
      | t::ts -> p_t t ^^ break 1 ^^ !^":: " ^^ loop ts in
    group @@ nest 2 @@ loop p
  and p_q (q : q) : document =
    group @@ match q with
    | QR r -> !^r
    | QI i -> p_nat i
    | QEpsilon s -> !^s
    | QEnd (t,s) ->
      !^"end" ^^ lbrace ^^ nest 2 (p_t t ^^ semi ^^
                                   p_s s ^^ rbrace)
    | QOut -> !^"out"
  and p_u (u : u) : document =
    group @@ match u with
    | UW (_,w) -> p_w w
    | UR (_,r) -> !^r
    | UPack (_,t',u,a,t) -> pack_h t' (p_u u) a t
    | UFold (_,a,t,u) -> fold_h a t (p_u u)
    | UApp (_,u,os) -> app_h (p_u u) os
  and p_psi (p : psi_elem) : document =
    group @@ match p with
    | PTuple ps -> nest 2 @@ angles @@ separate_map (comma ^^ break 1) p_t ps
    | PBlock (d,c,s,q) -> nest 2 (
        !^"forall" ^^ p_delta d ^^ dot ^^ break 0
        ^^ (nest 1 @@ braces @@ (p_chi c ^^ semi ^^ break 1 ^^ p_s s))
        ^^ space ^^ p_q q
      )
  and p_h (h : h) : document =
    group @@ match h with
    | HCode (d,c,s,q,is) ->
      nest 2 (
        !^"code " ^^ p_delta d
        ^^ (nest 1 @@ align @@ braces (p_chi c ^^ semi ^^ break 1 ^^ p_s s))
        ^^ space
        ^^ p_q q ^^ dot ^^ break 0 ^^ p_instruction_sequence is
      )
    | HTuple (ws) -> angles @@ separate_map (comma ^^ break 1) p_w ws
  and p_mut (m : mut) : document =
    group @@ match m with
    | Box -> !^"box"
    | Ref -> !^"ref"
  and p_delta (d : delta) : document =
    let p_elem (DAlpha a | DZeta a | DEpsilon a) = !^a in
    group @@ brackets @@ align @@ separate_map (comma ^^ break 1) p_elem d
  and p_chi (c : chi) : document =
    let p_decl (r, t) = !^r ^^ space ^^ colon ^^ space ^^ align (p_t t) in
    group @@ align @@ separate_map (comma ^^ break 1) p_decl c
  and p_instr (i : instr) : document =
    group @@ nest 2 @@ match i with
    | Iaop(_,a,r1,r2,u) -> p_aop a ^^ space ^^ args [!^r1; !^r2; p_u u]
    | Ibnz(_,r,u) -> !^"bnz " ^^ args [!^r; p_u u]
    | Ild(_,r1,r2,n) -> !^"ld " ^^ args [!^r1; !^r2 ^^ brackets (p_nat n)]
    | Ist(_,r1,n,r2) -> !^"st " ^^ args [!^r1 ^^ brackets (p_nat n); !^r2]
    | Iralloc(_,r,n) -> !^"ralloc " ^^ args [!^r; p_nat n]
    | Iballoc(_,r,n) -> !^"balloc " ^^ args[!^r; p_nat n]
    | Imv(_,r,u) -> !^"mv " ^^ args [!^r; p_u u]
    | Iunpack(_,a,r,u) ->
      !^"unpack " ^^ args [angles (!^a ^^ comma ^^ space ^^ !^r); p_u u]
    | Iunfold(_,r,u) -> !^"unfold " ^^ args [!^r; p_u u]
    | Isalloc (_,n) -> !^"salloc " ^^ args [p_nat n]
    | Isfree  (_,n) -> !^"sfree " ^^ args [p_nat n]
    | Isld(_,r,n) -> !^"sld " ^^ args [!^r; p_nat n]
    | Isst(_,n,r) -> !^"sst " ^^ args [p_nat n; !^r]
    | Ijmp (_,u) -> !^"jmp " ^^ args [p_u u]
    | Icall(_,u,s,q) -> !^"call " ^^ args [
        p_u u ^^ space ^^ braces (p_s s ^^ comma ^^ space ^^ p_q q);
      ]
    | Iret(_,r1,r2) -> !^"ret " ^^ args [!^r1 ^^ space ^^ braces !^r2]
    | Ihalt(_,t,s,r) -> !^"halt " ^^ args [p_t t; p_s s ^^ space ^^ braces !^r]
    | Iprotect(_,sp, z) -> !^"protect " ^^ args [p_sigma_prefix sp; !^z]
    | Iimport(_,r,z,s,t,e) ->
      !^"import " ^^ args [
        !^r;
        p_s s ^^ space ^^ !^"as" ^^ space ^^ !^z;
        FP.p_t t ^^ space ^^ !^ "TF" ^^ (braces @@ align @@ FP.p_exp e);
      ]
  and p_instruction_sequence (is : instr list) : document =
    group (lbracket ^^ align
             (group (separate_map (semi ^^ break 1) p_instr is ^^ rbracket)))
  and p_aop (a : aop) : document =
    group @@ match a with
    | Add -> !^"add"
    | Sub -> !^"sub"
    | Mult -> !^"mul"
  and p_regm (m : regm) : document =
    let p_binding (r, w) = !^r ^^ !^" -> " ^^ nest 2 (align (p_w w)) in
    p_sequence_map p_binding m
  and p_heapm (m : heapm) : document =
    let p_binding (l, (p, h)) =
      !^l ^^ !^" -> " ^^ nest 2 (align (p_mut p ^^ space ^^  p_h h)) in
    p_sequence_map p_binding m
  and p_stackm (m : stackm) : document =
    if List.length m > 0 then
      group @@ nest 2 (separate_map (!^" ::" ^^ break 1) p_w m ^^ !^" :: *")
    else !^"*"
  and p_component ((l,is,h) : component) : document =
    group @@ nest 2 (
      lparen ^^ p_instruction_sequence is ^^ comma ^^ break 1
      ^^ p_heapm h ^^ rparen
    )
  and p_context (c : context) : document =
    group @@ match c with
    | CComponentEmpty (_, CHoleI) | CComponentHeap (_, CHoleC) -> !^"[.]"
    | CComponentEmpty (_, CImportI (_,r,z,s,t,c,is)) ->
      !^"import " ^^ args [!^r; !^z ^^ !^" as " ^^ p_s s;
           FP.p_t t ^^ lbrace ^^ FP.p_context c ^^ rbrace ^^ semi ^^ break 1
           ^^ separate_map (semi ^^ break 1) p_instr is]

  and pack_h t' d a t =
    !^"pack " ^^
    langle ^^ p_t t' ^^ comma ^^ d ^^ rangle ^^
    !^" as " ^^ p_t (TExists (a,t))
  and fold_h a t d =
    !^"fold " ^^ p_t (TRec (a,t)) ^^
    !^" " ^^ d
  and app_h d os =
    nest 2 (d ^^ lbracket ^^
            separate_map (!^", ") p_o os ^^
            rbracket)
end and FP : sig
    open PPrint
    val p_t : F.t -> document
    val p_exp : F.exp -> document
    val p_context : F.context -> document

end = struct
  open PPrint;;
  open F

  let rec p_t (t : t) : document =
    match t with
    | TVar s -> !^s
    | TUnit -> !^"unit"
    | TInt -> !^"int"
    | TArrow (ts,t) -> nest 2 (lparen ^^ separate_map (comma ^^ break 1) p_t ts ^^ rparen ^^ !^" -> " ^^ p_t t)
    | TArrowMod (ts,sin,sout,t) -> nest 2 (lparen ^^ separate_map (comma ^^ break 1) p_t ts ^^ rparen ^^ lbracket ^^ TALP.p_sigma_prefix sin ^^ rbracket ^^ !^" -> " ^^ lbracket ^^ TALP.p_sigma_prefix sout ^^ rbracket ^^ p_t t)
    | TRec(a,t) -> nest 2 (!^"mu " ^^ !^a ^^ dot ^^ p_t t)
    | TTuple ts -> nest 2 (langle ^^ group (separate_map (comma ^^ break 1) p_t ts) ^^ rangle)

  and p_simple_exp = function
    | EVar (_,e) -> !^e
    | EUnit _ -> lparen ^^ rparen
    | EInt (_,n) -> !^(string_of_int n)
    | ETuple(_,es) -> langle ^^ group (separate_map (comma ^^ break 1) p_exp es) ^^ rangle
    | EPi(_,n,e) -> !^"pi" ^^ space ^^ !^(string_of_int n) ^^ lparen ^^ p_exp e ^^ rparen
    | EBoundary(_,t,ms,c) ->
      let p_ms = function
        | None -> !^"?"
        | Some s -> TALP.p_s s in
      nest 2 (
        !^"FT"
        ^^ (brackets @@ align @@ group (p_t t ^^ comma ^^ break 1 ^^ p_ms ms))
        ^^ break 0 ^^ TALP.p_component c
      )
    | e -> group (lparen ^^ p_exp e ^^ rparen)

  and p_app_exp = function
    | EApp(_,e,es) ->
      group
        (p_simple_exp e
         ^^ break 1
         ^^ group (separate_map (break 1) p_simple_exp es))
    | e -> p_simple_exp e

  and p_mul_exp = function
    | EBinop(_,e1, (BTimes as op), e2) -> p_simple_exp e1 ^^ p_binop op ^^ p_simple_exp e2
    | e -> p_app_exp e

  and p_sum_exp = function
    | EBinop(_,e1, (BPlus as op), e2) -> p_sum_exp e1 ^^ p_binop op ^^ p_sum_exp e2
    | EBinop(_,e1, (BMinus as op), e2) -> p_sum_exp e1 ^^ p_binop op ^^ p_mul_exp e2
    | e -> p_mul_exp e

  and p_arith_exp e = p_sum_exp e

  and p_exp (e : exp) : document =
    group @@ nest 2 (match e with
    | EIf0(_,et,e1,e2) ->
      !^"if0" ^^ space ^^ p_simple_exp et
      ^^ break 1 ^^ p_simple_exp e1
      ^^ break 1 ^^ p_simple_exp e2
    | EFold(_,a,t,e) ->
      !^"fold " ^^ group (lparen ^^ p_t (TRec (a,t)) ^^ rparen) ^^ space ^^ p_exp e
    | EUnfold(_,e) -> !^"unfold " ^^ p_exp e
    | ELam(_,ps, e) ->
      !^"lam " ^^ p_telescope ps ^^ !^"." ^^ break 1 ^^ p_exp e
    | ELamMod(_,ps,sin,sout,e) ->
      !^"lam "
      ^^ p_stack_prefix sin
      ^^ p_stack_prefix sout
      ^^ p_telescope ps ^^ !^"."
      ^^ break 1 ^^ p_exp e
    | e -> p_sum_exp e
  )

  and p_stack_prefix s =
    lbracket ^^ TALP.p_sigma_prefix s ^^ rbracket

  and p_telescope ps =
    let p_binding (p, t) = group (!^p ^^ colon ^^ align (p_t t)) in
    group @@ align @@ parens (separate_map (comma ^^ space) p_binding ps)

  and p_binop (b : binop) : document =
    match b with
    | BPlus -> !^"+"
    | BMinus -> !^"-"
    | BTimes -> !^"*"

  and p_context (c : context) : document =
    nest 2 (match c with
    | CHole -> !^"[.]"
    | CBinop1 (_,c,o,e) -> p_context c ^^ space ^^ p_binop o ^^ space ^^ p_exp e
    | CBinop2 (_,e,o,c) -> p_exp e ^^ space ^^ p_binop o ^^ space ^^ p_context c
    | CIf0 (_,c,e1,e2) ->
      !^"if0 " ^^ p_context c ^^ space
      ^^ lparen ^^ p_exp e1 ^^ rparen ^^ space
      ^^ lparen ^^ p_exp e2 ^^ rparen
    | CApp1 (_,c,es) -> lparen ^^ p_context c ^^ space ^^ group (separate_map (break 1) p_exp es) ^^ rparen
    | CAppn (_,f,es1,c,es2) -> lparen ^^ p_exp f ^^ space ^^
                             group (separate_map (break 1) p_exp es1 ^^
                                    (break 1) ^^ p_context c ^^ (break 1) ^^
                                    separate_map (break 1) p_exp es2) ^^
                             rparen
    | CFold (_,a,t,c) -> !^"fold " ^^ lparen ^^ p_t (TRec (a,t)) ^^ rparen ^^ space ^^ p_context c
    | CUnfold (_,c) -> !^"unfold " ^^ lparen ^^ p_context c ^^ rparen
    | CTuple (_,es1, c, es2) -> langle ^^ group (separate_map (break 1) p_exp es1 ^^
                                               (break 1) ^^ p_context c ^^ (break 1) ^^
                                               separate_map (break 1) p_exp es2) ^^
                              rangle
    | CPi (_,n, c) -> !^"pi." ^^ !^(string_of_int n) ^^ lparen ^^ p_context c ^^ rparen
    | CBoundary (_,t,ms,c) ->
      !^"FT" ^^ lbracket ^^ p_t t ^^ comma ^^
      (match ms with
       | None -> !^"?"
       | Some s -> TALP.p_s s) ^^ rbracket ^^ TALP.p_context c)


end
