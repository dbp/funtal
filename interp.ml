open Utils
module rec FTAL : sig
  open Syntax
  open FTAL

  val ft : F.t -> TAL.w -> TAL.mem -> (TAL.mem * F.exp)
  val tf : F.t -> F.exp -> TAL.mem -> (TAL.mem * TAL.w)

end = struct
  module TAL' = TAL
  module F' = F
  open Syntax
  open FTAL


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
    | (F.TRec (a, t), TAL.WFold (l, a',t',w)) when Typecheck.FTAL.tytrans (F.TRec (a,t)) = TAL.TRec (a', t') ->
      let (m', v) = ft (Typecheck.F.type_sub (FTAL.FType (a, F.TRec (a, t))) t) w m in
      (m', F.EFold (l, a, t, v))
    | (F.TArrow (ts,t1), TAL.WLoc (l', l)) ->
      let z1 = gen_sym ~pref:"z" () in
      let z2 = gen_sym ~pref:"z" () in
      let z3 = gen_sym ~pref:"z" () in
      let lend = gen_sym ~pref:"lend" () in
      let hend =
        TAL.(HCode ([DZeta z1],
                    [("r1", Typecheck.FTAL.tytrans t1)],
                    (SAbstract ([], z1)),
                    (QEnd (Typecheck.FTAL.tytrans t1, SAbstract ([], z1))),
                    [Ihalt (l', Typecheck.FTAL.tytrans t1, SAbstract ([], z1), "r1")])) in
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
                                   QEnd (Typecheck.FTAL.tytrans t1, SAbstract ([], z2)))]],
                        []))))
      in (((lend, (TAL.Box, hend))::hm,rm,sm), v)
    | (F.TArrowMod (ts,sin,sout,t1), TAL.WLoc (l', l)) ->
      let lend = gen_sym ~pref:"lend" () in
      let z1 = gen_sym ~pref:"z" () in
      let z2 = gen_sym ~pref:"z" () in
      let z3 = gen_sym ~pref:"z" () in
      let hend =
        TAL.(HCode ([DZeta z1],
                   [("r1", Typecheck.FTAL.tytrans t1)],
                   SAbstract (sin, z1),
                   (QEnd (Typecheck.FTAL.tytrans t1, SAbstract (sout, z1))),
                   [Ihalt (l', Typecheck.FTAL.tytrans t1, SAbstract (sout, z1), "r1")])) in
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
                                   QEnd (Typecheck.FTAL.tytrans t1, SAbstract (sout, z2)))]],
                        []))))
      in (((lend, (TAL.Box, hend))::hm,rm,sm), v)
    | _ -> raise (Failure ("ft: can't convert at type " ^ Pretty.F.show t ^ " value " ^ Pretty.TAL.show_w w))

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
      let (m', w) = tf (Typecheck.F.type_sub (FTAL.FType (a, F.TRec (a,t))) t) e m in
      (m', TAL.WFold (l,a,Typecheck.FTAL.tytrans t,w))
    | (F.TArrow (ts,t1), F.ELam (l,ps,body)) ->
      let loc = gen_sym ~pref:"lf" () in
      let e = gen_sym ~pref:"e" () in
      let z1 = gen_sym ~pref:"z" () in
      let z2 = gen_sym ~pref:"z" () in
      let s' = TAL.SAbstract (List.map ~f:Typecheck.FTAL.tytrans ts, z1) in
      let s = TAL.(SAbstract ((TBox (PBlock ([], [("r1", Typecheck.FTAL.tytrans t1)],
                                             SAbstract ([], z1), QEpsilon e))) ::
                              List.map ~f:Typecheck.FTAL.tytrans ts, z1)) in
      let body_wrapped =
        let n = List.length ts in
        F.EApp (l,F.ELam (l,ps,body),
                List.mapi ~f:(fun i t' ->
                    F.EBoundary (l,t', Some s, (l, [TAL.Isld (l,"r1", n-i);
                                               TAL.Ihalt (l,Typecheck.FTAL.tytrans t', s, "r1")], [])))
                  (List.map ~f:snd ps))
      in
      let instrs = TAL.([Isalloc (l,1); Isst (l,0, "ra");
                         Iimport (l,"r1", z2, SAbstract ([], z1), t1, body_wrapped);
                         Isld (l,"ra",0); Isfree (l,List.length ts + 1); Iret (l,"ra", "r1")]) in
      let h =
        TAL.(HCode
               ([DZeta z1; DEpsilon e],
                [("ra", TBox (PBlock ([], [("r1", Typecheck.FTAL.tytrans t1)], SAbstract ([], z1), QEpsilon e)))],
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
      let s' = TAL.SAbstract (List.map ~f:Typecheck.FTAL.tytrans ts, z1) in
      let s = TAL.(SAbstract ((TBox (PBlock ([], [("r1", Typecheck.FTAL.tytrans t1)],
                                             SAbstract ([], z1), QEpsilon e))) ::
                              List.map ~f:Typecheck.FTAL.tytrans ts, z1)) in

      let body_wrapped =
        let n = List.length ts in
        F.EApp (l,F.ELamMod (l,ps,sin,sout,body),
                List.mapi ~f:(fun i t' ->
                    F.EBoundary (l,t', Some s, (l, [TAL.Isld (l,"r1", n-i);
                                               TAL.Ihalt (l,Typecheck.FTAL.tytrans t', s, "r1")], [])))
                  (List.map ~f:snd ps))
      in
      let instrs = TAL.([Isalloc (l,1); Isst (l,0, "ra"); Iimport (l,"r1", z2, SAbstract ([], z1), t1, body_wrapped);
                         Isld (l,"ra",0); Isfree (l,List.length ts + 1); Iret (l,"ra", "r1")]) in
      let h =
        TAL.(HCode
               ([DZeta z1; DEpsilon e],
                [("ra", TBox (PBlock ([], [("r1", Typecheck.FTAL.tytrans t1)], SAbstract ([], z1), QEpsilon e)))],
                s',
                QR "ra",
                instrs))
      in
      (((loc,(TAL.Box, h))::hm,rm,sm), TAL.WLoc (l,loc))
    | _ -> raise (Failure "tf: can't convert")




end
and F : sig
  open Syntax
  open F

  val value : exp -> bool

  val sub : FTAL.substitution -> exp -> exp

  val plug : context -> ft -> exp

  val decomp : exp -> (context * F.ft) option

  val step : TAL.mem * exp -> TAL.mem * exp

  val stepn : int -> TAL.mem * exp -> TAL.mem * exp

end = struct
  module FTAL' = FTAL
  module F' = F
  module TAL' = TAL
  open Syntax
  open F



  let rec value e =
    match e with
    | EUnit l -> true
    | EInt _ -> true
    | ELam _ -> true
    | ELamMod _ -> true
    | EFold _ -> true
    | ETuple (l,es) -> List.for_all ~f:value es
    | _ -> false

  type env = (string * t) list

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
    | EBoundary (l, t, s, comp) -> EBoundary (l, Typecheck.F.type_sub p t, Option.(s >>| Typecheck.TAL.stack_sub p), TAL'.sub p comp)

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
    | EBoundary (_, t, s, (_,[TAL.Ihalt (_, t',s',r)],[])) when Typecheck.TAL.t_eq (Typecheck.FTAL.tytrans t) t' ->
      let (hm,rm,sm) = m in
      FTAL'.ft t (List.Assoc.find_exn rm r) m
    | _ -> (m, e)

  let split_at f l =
    let rec split_at' f acc l =
      match l with
      | []    -> (acc, None, [])
      | x::xs -> if f x then (List.rev acc, Some x, xs) else split_at' f (x::acc) xs
    in split_at' f [] l

  let is_some = function | None -> false
                         | Some _ -> true


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
      begin match TAL'.decomp comp with
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
    | CBoundary (l, t,s,talctxt) -> EBoundary (l, t, s, TAL'.plug talctxt e)



  let step (m, e) =
    let (h,r,s) = m in
    match decomp e with
    | Some (ctxt, F e') ->
      let _ = Debug.log "decomp F ctxt" (Pretty.F.show_context ctxt) in
      let _ = Debug.log "decomp F exp" (Pretty.F.show_exp e') in
      let (m', e'') = step_prim (m, e') in
      let _ = Debug.log "stepped F exp" (Pretty.F.show_exp e'') in
      (m', plug ctxt (F e''))
    | Some (ctxt, TI is) ->
      let () = Debug.log "decomp TI ctxt" (Pretty.F.show_context ctxt) in
      let _ = Debug.log "decomp TI instrs" (String.concat "; " (List.map ~f:(fun i -> Pretty.TAL.show_instr i) is)) in
      let _ = Debug.log "decomp TI regs" (Pretty.TAL.show_regm r) in
      let _ = Debug.log "decomp TI stack" (Pretty.TAL.show_stackm s) in
      let (m', is') = TAL'.reduce (m, is) in
      let (h',r',s') = m' in
      let _ = Debug.log "stepped TI instrs" (String.concat "; " (List.map ~f:(fun i -> Pretty.TAL.show_instr i) is')) in
      let _ = Debug.log "stepped TI regs" (Pretty.TAL.show_regm r') in
      let _ = Debug.log "stepped TI stack" (Pretty.TAL.show_stackm s') in
      let _ = Debug.log "stepped TI heap" (Pretty.TAL.show_heapm h') in
      (m', plug ctxt (TI is'))
    | Some (ctxt, TC (l,is,h)) ->
      let m' = TAL'.load m h in
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



end
and TAL : sig
  open Syntax
  open TAL


  val load : mem -> heapm -> mem

  val sub : FTAL.substitution -> component -> component


  val plug : context -> F.ft -> component

  val reduce : mem * instr list -> mem * instr list

  val decomp : component -> (context * F.ft) option

end = struct
  module FTAL' = FTAL
  module F' = F
  module TAL' = TAL
  open Syntax
  open TAL


  let load (h,r,s) h' =
    (* NOTE(dbp 2016-09-08): We should do renaming, but relying, for now, on the fact
       that we always gensym new location names, so not renaming should be safe. *)
    (List.append h' h, r, s)

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
        | CImportI (l, r,z,s,t,ctxt',is) -> (l, Iimport (l, r,z,s,t,F'.plug ctxt' e)::is, [])
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
    | Icall (l, u,s,q) -> Icall (l, u_sub p u, Typecheck.TAL.stack_sub p s, Typecheck.TAL.retmarker_sub p q)
    | Ihalt (l, t,s,r) -> Ihalt (l, Typecheck.TAL.type_sub p t, Typecheck.TAL.stack_sub p s, r)
    | Iimport (l, r,z,s,t,e) -> Iimport (l, r,z,Typecheck.TAL.stack_sub p s,Typecheck.F.type_sub p t,F'.sub p e)
    | _ -> i

  and u_sub p u = match u with
    | UW (l, w) -> UW (l, w_sub p w)
    | UR _ -> u
    | UPack (l, t',ubody,a,t) -> begin match p with
        | FTAL.TType (a', _) when a = a' ->
          UPack (l, Typecheck.TAL.type_sub p t', ubody, a, t)
        | _ -> UPack (l, Typecheck.TAL.type_sub p t', u_sub p ubody, a, Typecheck.TAL.type_sub p t)
      end
    | UFold (l, a, t, ubody) -> begin match p with
        | FTAL.TType (a', _) when a = a' -> u
        | _ -> UFold (l, a, Typecheck.TAL.type_sub p t, u_sub p ubody)
      end
    | UApp (l, ubody, os) -> UApp (l, u_sub p ubody, List.map ~f:(Typecheck.TAL.omega_sub p) os)

  and w_sub p w = match w with
    | WPack (l, t',wbody,a,t) -> begin match p with
        | FTAL.TType (a', _) when a = a' ->
          WPack (l, Typecheck.TAL.type_sub p t', wbody, a, t)
        | _ -> WPack (l, Typecheck.TAL.type_sub p t', w_sub p wbody, a, Typecheck.TAL.type_sub p t)
      end
    | WFold (l, a,t,wbody) -> begin match p with
        | FTAL.TType (a', _) when a = a' -> w
        | _ -> WFold (l, a, Typecheck.TAL.type_sub p t, w_sub p wbody)
      end
    | WApp (l, wbody, os) -> WApp (l, w_sub p wbody, List.map ~f:(Typecheck.TAL.omega_sub p) os)
    | _ -> w







  let decomp (loc, is, m) =
    match m with
    | [] ->
      begin match is with
        | [] -> None
        | Ihalt _ :: _ -> None
        | Iimport (l,r,z,s,t,e) :: rest ->
          begin match F'.decomp e with
            | None -> if F'.value e then Some (CComponentEmpty (loc, CHoleI), F.TI is) else None
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





  let instrs_sub delt os is =
    let subs = Typecheck.TAL.type_zip delt os in
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
      let l = gen_sym () in (((l, (Ref, HTuple (List.take sm n))) :: hm, replace rm rd (WLoc (l',l)), List.drop sm n), is)
    | ((hm,rm,sm), Iballoc (l',rd,n)::is) when List.length sm >= n ->
      let l = gen_sym () in (((l, (Box, HTuple (List.take sm n))) :: hm, replace rm rd (WLoc (l',l)), List.drop sm n), is)
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
      let (m, w) = FTAL'.tf t v (hm,rm,sm) in
      (m, Imv (l,r, UW (l, w))::is)
    | ((hm,rm,sm), Iprotect (_,_,_)::is) ->
      ((hm,rm,sm), is)
    | _ -> c

end
