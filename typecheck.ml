open Utils
open Syntax

module rec FTAL : sig
  open Syntax
  open FTAL
  val tytrans : Syntax.F.t -> TAL.t
  exception TypeError of string * l

  val default_context : TAL.q -> context

  val tc : FTAL.context -> e -> t * TAL.sigma
  val tc_is : l -> context -> TAL.instr list -> unit
  val tc_w : context -> TAL.w -> TAL.t
  val tc_u : context -> TAL.u -> TAL.t
  val tc_h : context -> l -> TAL.mut -> TAL.h -> TAL.psi_elem
  val tc_h_shallow : context -> l -> TAL.mut -> TAL.h -> TAL.psi_elem
end = struct
  module F' = F
  module TAL' = TAL
  open Syntax
  open FTAL
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

  exception TypeError of string * l

  let default_context q = ([],[],[],[],q,TAL.SConcrete [])

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
                | (FT t, _) -> raise (TypeError (Pretty.F.show_binop o ^ ": second argument has type " ^ Pretty.F.show t ^ ", not int.", l))
                | _ -> raise (TypeError (Pretty.F.show_binop o ^ ": Uh-oh, got something I didn't understand.", l))
              end
            | (FT t, _) -> raise (TypeError (Pretty.F.show_binop o ^ ": first argument has type " ^ Pretty.F.show t ^ ", int.", l))
            | _ -> raise (TypeError (Pretty.F.show_binop o ^ ": Uh-oh, got something I didn't understand.", l))
          end
        | EIf0 (l,c,e1,e2), TAL.QOut ->
          begin match tc' c with
            | FT TInt, s1 ->
              begin match tc (set_stack context s1) (FC e1) with
                | FT t1, s2 ->
                  begin match tc (set_stack context s2) (FC e2) with
                    | FT t2, s3 -> if F'.t_eq t1 t2 && TAL'.s_eq s2 s3 then (FT t1, s2) else
                        raise (TypeError ("if: then branch has type " ^ Pretty.F.show t1 ^ " but else branch has type " ^ Pretty.F.show t2 ^ ".", l))
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
          | (FT t, zeta') when zeta_out = zeta' -> (FT (TArrowMod (List.map ~f:snd ps, sin, sout, t)), get_stack context)
          | (FT _, zeta') -> raise (TypeError ("lam: body manipulates stack in invalid way. Expected " ^ Pretty.TAL.show_sigma zeta_out ^ " but got " ^ Pretty.TAL.show_sigma zeta' , l))
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
                     | FT t', s1 when F'.t_eq t t' -> s1
                     | FT t', _ -> raise (TypeError ("app: " ^ string_of_int !i ^
                                                     "th argument should have type " ^
                                                     Pretty.F.show t ^ " but has type " ^ Pretty.F.show t' ^ ".", l))
                     | _ -> raise (TypeError ("app: Uh-oh, got something I didn't understand.", l))
                   ) ~init:s (List.zip_exn ps args))
            | FT (TArrowMod (ps, sin, sout, rv)), s ->
              if List.length ps <> List.length args then
                raise (TypeError ("app: function expected " ^
                                  string_of_int (List.length ps) ^
                                  " arguments, but passed " ^
                                  string_of_int (List.length args) ^ ".", l))
              else
                let i = ref 0 in
                let s' = List.fold_left ~f:(fun s0 (t,e) ->
                    i := !i + 1;
                    match tc (set_stack context s0) (FC e) with
                    | FT t', s1 when F'.t_eq t t' -> s1
                    | FT t', _ -> raise (TypeError ("app: " ^ string_of_int !i ^
                                                    "th argument should have type " ^
                                                    Pretty.F.show t ^ " but has type " ^ Pretty.F.show t' ^ ".", l))
                    | _ -> raise (TypeError ("app: Uh-oh, got something I didn't understand.", l))
                  ) ~init:s (List.zip_exn ps args) in
                if TAL.stack_pref_length s' >= List.length sin && TAL'.s_pref_eq (TAL.stack_take s' (List.length sin)) sin then
                  (FT rv, s')
                else raise (TypeError ("app: stack modifying lambda expected stack prefix of " ^ Pretty.TAL.show_sigma_prefix sin ^ ", but got stack of shape " ^ Pretty.TAL.show_sigma s' ^ ".", l))
            | (FT t,_) ->
              raise (TypeError ("app: got non-function of type " ^ Pretty.F.show t ^ ".", l))
            | _ -> raise (TypeError ("app: Uh-oh, got something I didn't understand.", l))
          end
        | EFold (l,a,t,e), TAL.QOut ->
          begin match tc' e with
            | FT t', s -> if F'.t_eq t' (F'.type_sub (FTAL.FType (a, TRec (a,t))) t) then (FT (TRec (a,t)), s)
              else
                raise (TypeError ("fold: expected body to have type " ^ Pretty.F.show t' ^ ".", l))
            | _ -> raise (TypeError ("fold: Uh-oh, got something I didn't understand.", l))
          end
        | EUnfold (l,e), TAL.QOut -> begin match tc' e with
            | FT (TRec (a,t)), s -> (FT (F'.type_sub (FTAL.FType (a, TRec (a,t))) t), s)
            | (FT t, _) -> raise (TypeError ("unfold: body not a recursive type: " ^ Pretty.F.show t ^ ".", l))
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
            | FT t, _ -> raise (TypeError ("pi: given non-tuple of type " ^ Pretty.F.show t ^ ".", loc))
            | _ -> raise (TypeError ("pi: Uh-oh, got something I didn't understand.", loc))
          end
        | EBoundary (l,t,s,c), TAL.QOut ->
          let s' = Option.value ~default:(get_stack context) s in
          begin match tc (set_ret context (TAL.QEnd (tytrans t, s'))) (TC c) with
            | TT t0, s0 when not (TAL'.t_eq t0 (tytrans t)) ->
              raise (TypeError ("FT: contents should have had type " ^ Pretty.F.show t ^
                                " which is not equivalent to type " ^ Pretty.TAL.show t0 ^ ".",l))
            | TT t0, s0 when not (TAL'.s_eq s0 s') ->
              raise (TypeError ("FT: after running stack should have had type " ^
                                Pretty.TAL.show_sigma s' ^ " but instead had type " ^ Pretty.TAL.show_sigma s0 ^ ".",l))
            | TT t0, s0 -> (FT t, s0)
            | _ -> raise (TypeError ("FT: Uh-oh, got something I didn't understand.", l))
          end
        | _ -> raise (TypeError ("exp: F expressions must have return marker out.", F'.get_loc exp))
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
            if not (TAL'.psi_elem_eq p' p) then
              raise (TypeError ("component: Uh-oh, got something I didn't understand.", loc)) else ()) h in
      begin
        tc_is loc context instrs;
        match TAL.ret_type context (get_ret context) with
        | Some s -> s
        | None -> raise (TypeError ("component: return marker invalid: " ^
                                    Pretty.TAL.show_q (get_ret context) ^ ".", loc))
      end

  and tc_is (prev_loc : l) context instrs : unit =
    let open TAL in
    match instrs, get_ret context with
    | Iaop (l,op, rd, rs, u)::is, QR r when rd = r ->
      raise (TypeError (Pretty.TAL.show_aop op ^ ": can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iaop (l,op, rd, rs, u)::is, _ ->
      begin match List.Assoc.find (get_reg context) rs, tc_u context u with
        | None, _ -> raise (TypeError (Pretty.TAL.show_aop op ^ ": source register " ^ rs ^ " is empty.", l))
        | Some t, _ when t <> TInt -> raise (TypeError (Pretty.TAL.show_aop op ^ ": source register has type " ^
                                                        Pretty.TAL.show t ^ ", not int.", l))
        | _, t when t <> TInt -> raise (TypeError (Pretty.TAL.show_aop op ^ ": operand has type " ^ Pretty.TAL.show t ^ ", not int.", l))
        | _ -> tc_is l (set_reg context (List.Assoc.add (get_reg context) rd TInt)) is
      end
    | Imv (l,rd,u)::is, QR r when rd = r ->
      raise (TypeError ("mv: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Imv (l,rd,u)::is, q ->
      let context = match q, u with
        | QR r, UR (_, r') when r = r' -> set_ret context (QR rd)
        | _ -> context in
      tc_is l (set_reg context (List.Assoc.add (get_reg context) rd (tc_u context u))) is
    | Iimport (l,rd,z,s,t,f)::is, (QR _ as q) | Iimport (l,rd,z,s,t,f)::is, (QEpsilon _ as q) ->
      raise (TypeError ("import: return marker must be end or stack position, not " ^ Pretty.TAL.show_q q ^ ".", l))
    | Iimport (l,rd,z,s,t,f)::is, _ when
        TAL.stack_pref_length s > TAL.stack_pref_length (get_stack context) ||
        not (TAL'.s_eq (TAL.stack_drop (get_stack context) (TAL.stack_pref_length (get_stack context) - TAL.stack_pref_length s)) s) ->
      raise (TypeError ("import: protected suffix does not match current stack. Suffix is " ^
                        Pretty.TAL.show_sigma s ^ ", but current stack is " ^ Pretty.TAL.show_sigma (get_stack context) ^ ".", l))
    | Iimport (l,rd,z,s,t,f)::is, QI i when
        (let exposed = (TAL.stack_pref_length (get_stack context) - TAL.stack_pref_length s) in
         i < exposed) ->
      raise (TypeError ("import: return marker is not in protected suffix of stack. It's at position " ^
                        string_of_int i ^
                        " and current stack is " ^ Pretty.TAL.show_sigma (get_stack context) ^ ".", l))
    | Iimport (l,rd,z,s,t,f)::is, _ ->
      let pref = TAL.stack_take (get_stack context) (TAL.stack_pref_length (get_stack context) - TAL.stack_pref_length s) in
      let suf = TAL.stack_drop (get_stack context) (TAL.stack_pref_length (get_stack context) - TAL.stack_pref_length s) in
      begin match tc (set_stack (set_ret context QOut) (SAbstract (pref, z))) (FC f) with
        | (FT t',s') when not (F'.t_eq t t') ->
          raise (TypeError ("import: F expression has type " ^ Pretty.F.show t' ^ ", but should have type " ^ Pretty.F.show t ^ ".", l))
        | (FT t',SConcrete _)  ->
          raise (TypeError ("import: F expression does not protect abstract stack tail.", l))
        | (FT t',SAbstract (_, z')) when z <> z'  ->
          raise (TypeError ("import: F expression does not preserve abstract stack tail. Should have been " ^ z ^ " but was " ^ z' ^ ".", l))
        | (FT t',SAbstract (newpref, _)) -> tc_is l (set_stack (set_reg context (List.Assoc.add (get_reg context) rd (tytrans t))) (TAL.stack_prepend newpref suf)) is
        | _  -> raise (TypeError ("import: Uh-oh, got something I didn't understand.", l))
      end
    | [Ihalt (l,t,s,r)], QEnd (t',s') when not (TAL'.t_eq t' t) ->
      raise (TypeError ("halt: specified return type, " ^ Pretty.TAL.show t ^ ", does not match return marker's: " ^ Pretty.TAL.show t' ^ ".", l))
    | [Ihalt (l,t,s,r)], QEnd (t',s') when not (TAL'.s_eq s s') ->
      raise (TypeError ("halt: specified stack, " ^ Pretty.TAL.show_sigma s ^ ", does not match return marker's: " ^ Pretty.TAL.show_sigma s' ^ ".", l))
    | [Ihalt (l,t,s,r)], QEnd _ when not (TAL'.s_eq s (get_stack context)) ->
      raise (TypeError ("halt: specified stack, " ^ Pretty.TAL.show_sigma s ^
                        ", does not match current stack: " ^
                        Pretty.TAL.show_sigma (get_stack context) ^ ".", l))
    | [Ihalt (l,t,s,r)], QEnd _ ->
      begin match List.Assoc.find (get_reg context) r with
        | Some t' when TAL'.t_eq t t' -> ()
        | Some t' -> raise (TypeError ("halt: value in return register " ^ r ^
                                       " should have type " ^ Pretty.TAL.show t ^ " but instead is " ^ Pretty.TAL.show t' ^ ".", l))
        | None -> raise (TypeError ("halt: return register " ^ r ^ " is empty.", l))
      end
    | [Ihalt (l,_,_,_)], q ->
      raise (TypeError ("halt: return marker must be end{}, instead is: " ^ Pretty.TAL.show_q q ^ ".", l))
    | Isalloc (l,n) :: is, _ ->
      tc_is l (set_stack context (List.fold_left ~f:(fun s _ -> TAL.stack_cons TUnit s)
                                    ~init:(get_stack context) (List.init ~f:(fun x -> x) n))) is
    | Isfree (l,n) :: is, QI n' when n > n' ->
      raise (TypeError ("sfree: return marker is at position " ^ string_of_int n' ^ ", so you can't free " ^
                        string_of_int n ^ " cells: the return address would be lost.", l))
    | Isfree (l,n) :: is, _ when TAL.stack_pref_length (get_stack context) < n ->
      raise (TypeError ("sfree: only " ^ string_of_int (TAL.stack_pref_length (get_stack context)) ^
                        " stack cells are exposed, so can't free " ^ string_of_int n ^ ".", l))
    | Isfree (l,n) :: is, QI n' ->
      tc_is l (set_ret (set_stack context (TAL.stack_drop (get_stack context) n ))
                 (QI (n' - n))) is
    | Isfree (l,n) :: is, _ ->
      tc_is l (set_stack context (TAL.stack_drop (get_stack context) n )) is
    | Iprotect (l,pref,v)::is, QI n when n > List.length pref ->
      raise (TypeError ("protect: return marker is at position " ^ string_of_int n ^
                        ", so you can't hide everything past the first " ^
                        string_of_int (List.length pref) ^ " cells: the return address would be hidden.", l))
    | Iprotect (l,pref, v)::is, _ when not (TAL'.s_pref_eq (TAL.stack_take (get_stack context) (List.length pref)) pref) ->
      raise (TypeError ("protect: specified prefix " ^
                        Pretty.TAL.show_sigma_prefix pref ^ " does not match current stack: " ^
                        Pretty.TAL.show_sigma (get_stack context) ^ ".", l))
    | Iprotect (l,pref, v)::is, _ ->
      let stail = TAL.stack_drop (get_stack context) (List.length pref) in
      let new_q = TAL'.retmarker_sub (SAbs (stail, v)) (get_ret context) in
      tc_is l (set_ret (set_stack (set_tyenv context (List.append (get_tyenv context) [DZeta v])) (SAbstract (pref, v))) new_q) is
    | Isst(l,n,r):: is, _ when TAL.stack_pref_length (get_stack context) <= n ->
      raise (TypeError ("sst: only " ^ string_of_int (TAL.stack_pref_length (get_stack context)) ^
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
          tc_is l (set_stack context (TAL.stack_prepend (TAL.stack_take (get_stack context) n) (TAL.stack_cons t (TAL.stack_drop (get_stack context) (n+1))))) is
      end
    | Isld(l,rd,n)::is, QR r when r = rd ->
      raise (TypeError ("sld: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Isld(l,rd,n)::is, _ when TAL.stack_pref_length (get_stack context) <= n ->
      raise (TypeError ("sld: only " ^ string_of_int (TAL.stack_pref_length (get_stack context)) ^
                        " stack cells are exposed, so can't load from position " ^
                        string_of_int n ^ ".", l))
    | Isld(l,rd,n)::is, q ->
      let context = match q with
        | QI n' when n = n' -> set_ret context (QR rd)
        | _ -> context
      in
      tc_is l (set_reg context (List.Assoc.add (get_reg context) rd (List.last_exn (TAL.stack_take (get_stack context) (n+1))))) is
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
          tc_is l (set_reg context (List.Assoc.add (get_reg context) rd t)) is
        | Some t ->
          raise (TypeError ("ld: can't load from non-tuple of type " ^ Pretty.TAL.show t ^ ".", l))
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
              if not (TAL'.t_eq t t') then
                raise (TypeError ("st: can't overwrite a position with type "
                                  ^ Pretty.TAL.show t' ^ " with a value of type " ^ Pretty.TAL.show t ^ ".", l))
              else tc_is l context is
            | Some (TBox (PTuple _)) ->
              raise (TypeError ("st: can't write to a box (i.e., immutable) tuple.", l))
            | Some t ->
              raise (TypeError ("st: can't store to a non-tuple of type: " ^ Pretty.TAL.show t ^ ".", l))
          end
      end
    | Iralloc (l,rd, n)::is, _ when TAL.stack_pref_length (get_stack context) < n ->
      raise (TypeError ("ralloc: trying to allocate a tuple of size " ^ string_of_int n ^ " but there are only " ^
                        string_of_int (TAL.stack_pref_length (get_stack context))  ^ " visible cells on the stack.", l))
    | Iralloc (l,rd,n)::is, QR r when rd = r ->
      raise (TypeError ("ralloc: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iralloc (l,rd,n)::is, QI n' when n' + 1 <= n ->
      raise (TypeError ("ralloc: current return marker is on stack at position " ^ string_of_int n' ^
                        ", so allocating a tuple of size " ^ string_of_int n ^ " would move it.", l))
    | Iralloc (l,rd,n)::is, q ->
      let q' = match q with
        | QI n' -> QI (n' - n)
        | _ -> q in
      tc_is l (set_ret (set_stack (set_reg context (List.Assoc.add (get_reg context) rd (TTupleRef (TAL.stack_take (get_stack context) n)))) (TAL.stack_drop (get_stack context) n)) q') is
    | Iballoc (l,rd, n)::is, _ when TAL.stack_pref_length (get_stack context) < n ->
      raise (TypeError ("balloc: trying to allocate a tuple of size " ^ string_of_int n ^ " but there are only " ^
                        string_of_int (TAL.stack_pref_length (get_stack context))  ^ " visible cells on the stack.", l))
    | Iballoc (l,rd,n)::is, QR r when rd = r ->
      raise (TypeError ("balloc: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iballoc (l,rd,n)::is, QI n' when n' + 1 <= n ->
      raise (TypeError ("balloc: current return marker is on stack at position " ^ string_of_int n' ^
                        ", so allocating a tuple of size " ^ string_of_int n ^ " would move it.", l))
    | Iballoc (l,rd,n)::is, q ->
      let q' = match q with
        | QI n' -> QI (n' - n)
        | _ -> q in
      tc_is l (set_ret (set_stack (set_reg context (List.Assoc.add (get_reg context) rd (TBox (PTuple (TAL.stack_take (get_stack context) n))))) (TAL.stack_drop (get_stack context) n)) q') is
    | Iunpack (l,a, rd, u)::is, QR r when rd = r ->
      raise (TypeError ("unpack: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iunpack (l,a, rd, u)::is, _ ->
      begin match tc_u context u with
        | TExists (a', t) ->
          let newt = TAL'.type_sub (TType (a, TVar a')) t in
          tc_is l (set_reg context (List.Assoc.add (get_reg context) rd newt)) is
        | t -> raise (TypeError ("unpack: operand is non-existential of type " ^ Pretty.TAL.show t ^ ".", l))
      end
    | Iunfold (l,rd, u)::is, QR r when rd = r ->
      raise (TypeError ("unfold: can't overwrite current return address in register " ^ rd ^ ".", l))
    | Iunfold (l,rd, u)::is, _ ->
      begin match tc_u context u with
        | TRec (a, t) ->
          let t' = TAL'.type_sub (TType (a, TRec (a,t))) t in
          tc_is l (set_reg context (List.Assoc.add (get_reg context) rd t')) is
        | t -> raise (TypeError ("unfold: operand is non-fold of type " ^ Pretty.TAL.show t ^ ".", l))
      end
    | [Iret (l,rt, rv)], QR r when r = rt ->
      begin match List.Assoc.find (get_reg context) rt,
                  List.Assoc.find (get_reg context) rv with
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), Some ta when ra <> rv ->
        raise (TypeError ("ret: returning to a block expecting value in register " ^ ra ^ ", not " ^ rv ^ ".", l))
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), Some ta when not (TAL'.t_eq ta t) ->
        raise (TypeError ("ret: returning to a block expecting value of type " ^ Pretty.TAL.show t ^ ", not " ^ Pretty.TAL.show ta ^ ".", l))
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), Some ta when not (TAL'.s_eq s (get_stack context)) ->
        raise (TypeError ("ret: returning to a block expecting stack of type " ^
                          Pretty.TAL.show_sigma s ^ " but current stack has type " ^
                          Pretty.TAL.show_sigma (get_stack context) ^ ".", l))
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), Some ta -> ()
      | Some (TBox (PBlock ([], [(ra,t)], s, q))), None ->
        raise (TypeError ("ret: value register " ^ ra ^ " is empty.", l))
      | _ -> raise (TypeError ("ret: return address " ^ rt ^ " register empty.", l))
      end
    | [Iret (l,rt, rv)], QR r  ->
      raise (TypeError ("ret: return marker says to return to " ^
                        r ^ ", but trying to return to " ^ rt ^ ".", l))
    | [Iret (l,rt, rv)], q  ->
      raise (TypeError ("ret: return marker isn't register " ^ rt ^ ", it's " ^ Pretty.TAL.show_q q ^ ".", l))
    | [Ijmp (l,u)], q -> begin match tc_u context u with
        | TBox (PBlock ([], c, s, q')) when not (TAL'.q_eq q q') ->
          raise (TypeError ("jmp: current return marker is " ^ Pretty.TAL.show_q q ^
                            ", but trying to jump to block with return marker " ^ Pretty.TAL.show_q q' ^ ".", l))
        | TBox (PBlock ([], c, s, q')) when not (TAL'.s_eq s (get_stack context)) ->
          raise (TypeError ("jmp: block being jumped to expects stack of type " ^
                            Pretty.TAL.show_sigma s ^ ", but current stack has type " ^
                            Pretty.TAL.show_sigma (get_stack context) ^ ".", l))
        | TBox (PBlock ([], c, s, q')) when not (TAL'.register_subset c (get_reg context)) ->
          raise (TypeError ("jmp: block being jumped to expects register file of type " ^ Pretty.TAL.show_chi c ^
                            ", but current register file has type " ^ Pretty.TAL.show_chi (get_reg context) ^ ".", l))
        | TBox (PBlock ([], c, s, q')) -> ()
        | t -> raise (TypeError ("jmp: can't jump to non-block of type " ^ Pretty.TAL.show t ^ ".", l))
      end
    | Ibnz(l,rt,u)::is, q -> begin match List.Assoc.find (get_reg context) rt with
        | None -> raise (TypeError ("bnz: test register " ^ rt ^ " is empty.", l))
        | Some t when t <> TInt ->
          raise (TypeError ("bnz: test register has type " ^ Pretty.TAL.show t ^ ", not int.", l))
        | Some t -> begin match tc_u context u with
            | TBox (PBlock ([], c, s, q')) when not (TAL'.q_eq q q') ->
              raise (TypeError ("bnz: current return marker is " ^ Pretty.TAL.show_q q ^
                                ", but trying to branch to a block with return marker " ^
                                Pretty.TAL.show_q q' ^ ".", l))
            | TBox (PBlock ([], c, s, q')) when not (TAL'.s_eq s (get_stack context)) ->
              raise (TypeError ("bnz: block being branched to expects stack of type " ^ Pretty.TAL.show_sigma s ^
                                ", but current stack has type " ^ Pretty.TAL.show_sigma (get_stack context) ^ ".", l))
            | TBox (PBlock ([], c, s, q')) when not (TAL'.register_subset c (get_reg context)) ->
              raise (TypeError ("bnz: block being branched to expects register file of type " ^ Pretty.TAL.show_chi c ^
                                ", but current register file has type " ^ Pretty.TAL.show_chi (get_reg context) ^ ".", l))
            | TBox (PBlock ([], c, s, q')) ->
              tc_is l context is
            | t -> raise (TypeError ("bnz: can't branch to non-block of type " ^ Pretty.TAL.show t ^ ".", l))
          end
      end
    | [Icall(l,u,s,QEnd(t',s'))], QEnd(t,s'') when TAL'.t_eq t t' && TAL'.s_eq s' s'' ->
      begin match tc_u context u with
        | TBox (PBlock ([DZeta z; DEpsilon e], hatc, hats, hatq)) ->
          let pref_len = TAL.stack_pref_length (get_stack context) - TAL.stack_pref_length s in
          if pref_len < 0 then
            raise (TypeError ("call: can't protect suffix of length " ^ string_of_int (TAL.stack_pref_length s) ^
                              " when current stack only has length " ^ string_of_int (TAL.stack_pref_length (get_stack context)) ^ ".", l))
          else if not (TAL'.s_eq hats (SAbstract (TAL.stack_take (get_stack context) pref_len, z))) then
            raise (TypeError ("call: block being called expects stack of type " ^ Pretty.TAL.show_sigma hats ^
                              ", which doesn't match specified prefix.", l))
          else
            begin match TAL.ret_addr_type (set_stack (set_reg context hatc) hats) hatq with
              | Some (TBox (PBlock (_, _,hats', QEpsilon e))) ->
                begin match hats' with
                  | SAbstract (_, z') when z = z' ->
                    if not (TAL'.register_subset (TAL'.chi_sub (EMarker (e, QEnd(t',s'))) (TAL'.chi_sub (SType (z, s)) hatc)) (get_reg context)) then
                      raise (TypeError ("call: block being called expects register file with type " ^
                                        Pretty.TAL.show_chi (TAL'.chi_sub (EMarker (e, QEnd(t',s'))) (TAL'.chi_sub (SType (z, s)) hatc)) ^
                                        " which is not compatible with current register file of type " ^
                                        Pretty.TAL.show_chi (get_reg context) ^ ".", l))
                    else
                      ()
                  | _ ->
                    raise (TypeError ("call: block that will be returned to does not protect abstract stack suffix " ^ z ^ ".", l))
                end
              | _ -> raise (TypeError ("call: block being called to does not return to block with abstract return marker.", l))
            end
        | t -> raise (TypeError ("call: block being called does not follow calling convention: " ^ Pretty.TAL.show t ^ ".", l))
      end
    | [Icall(l,u,s,QI i')], QI i ->
      begin match tc_u context u with
        | TBox (PBlock ([DZeta z; DEpsilon e], hatc, hats, hatq)) ->
          let pref_len = TAL.stack_pref_length (get_stack context) - TAL.stack_pref_length s in
          if pref_len < 0 then
            raise (TypeError ("call: can't protect suffix of length " ^ string_of_int (TAL.stack_pref_length s) ^
                              " when current stack only has length " ^ string_of_int (TAL.stack_pref_length (get_stack context)) ^ ".", l))
          else if not (TAL'.s_eq hats (SAbstract (TAL.stack_take (get_stack context) pref_len, z))) then
            raise (TypeError ("call: block being called expects stack of type " ^ Pretty.TAL.show_sigma hats ^
                              ", which doesn't match specified prefix.", l))
          else if i < pref_len then
            raise (TypeError ("call: return marker is stored at position " ^ string_of_int i ^
                              " on stack, which will not be in protected tail.", l))
          else
            begin match TAL.ret_addr_type (set_stack (set_reg context hatc) hats) hatq with
              | Some (TBox (PBlock (_, _,hats', QEpsilon e))) ->
                let new_pref_len = TAL.stack_pref_length hats' in
                if i' <> i + new_pref_len - pref_len then
                  raise (TypeError ("call: return marker, which started at position " ^ string_of_int i ^
                                    ", does not end up at specified position on stack.", l))
                else begin match hats' with
                  | SAbstract (_, z') when z = z' ->
                    if not (TAL'.register_subset (TAL'.chi_sub (EMarker (e, QI i')) (TAL'.chi_sub (SType (z, s)) hatc)) (get_reg context)) then
                      raise (TypeError ("call: block being called expects register file with type " ^
                                        Pretty.TAL.show_chi (TAL'.chi_sub (EMarker (e, QI i')) (TAL'.chi_sub (SType (z, s)) hatc)) ^
                                        " which is not compatible with current register file of type " ^
                                        Pretty.TAL.show_chi (get_reg context) ^ ".", l))
                    else
                      ()
                  | _ ->
                    raise (TypeError ("call: block that will be returned to does not protect abstract stack suffix " ^ z ^ ".", l))
                end
              | _ -> raise (TypeError ("call: block being called to does not return to block with abstract return marker.", l))
            end
        | t -> raise (TypeError ("call: block being called does not follow calling convention: " ^ Pretty.TAL.show t ^ ".", l))
      end
    | (Ihalt(l,_,_,_)::_), _ -> raise (TypeError ("halt: must be the last instruction in a block.", l))
    | (Iret(l,_,_)::_), _ -> raise (TypeError ("ret: must be the last instruction in a block.", l))
    | (Ijmp(l,_)::_), _ -> raise (TypeError ("jmp: must be the last instruction in a block.", l))
    | [Icall(l,_,_,_)], _ -> raise (TypeError ("call: return marker must be end{} or be on the stack.", l))
    | (Icall(l,_,_,_)::_), _ -> raise (TypeError ("call: must be the last instruction in a block.", l))
    | [], _ -> raise (TypeError ("reached the end of a block without a jmp, ret, call, or halt.", prev_loc))


  and tc_u context u = let open TAL in match u with
    | UW (l,w) -> tc_w context w
    | UR (l,r) -> begin match List.Assoc.find (get_reg context) r with
        | None -> raise (TypeError ("Unbound register", l))
        | Some t -> t
      end
    | UPack (l,t, u, s, t') ->
      if tc_u context u = TAL'.type_sub (TType (s,t')) t
      then TExists (s,t')
      else raise (TypeError ("Ill-typed existential", l))
    | UFold (l,s,t,u) ->
      if tc_u context u = TAL'.type_sub (TType (s, TRec (s, t))) t
      then TRec (s,t)
      else raise (TypeError ("Ill-typed fold", l))
    | UApp (l, u, os) ->
      begin match tc_u context u with
        | TBox (PBlock (d,c,s,q)) ->
          let (ds,dr) = List.split_n d (List.length os) in
          List.fold_left
            ~f:(fun t' p -> TAL'.type_sub p t')
            ~init:(TBox (PBlock (dr,c,s,q)))
            (TAL'.type_zip ds os)
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
      if tc_w context w = TAL'.type_sub (TType (s,t')) t
      then TExists (s,t')
      else raise (TypeError ("Ill-typed existential", l))
    | WFold (l,s,t,w) ->
      if tc_w context w = TAL'.type_sub (TType (s, TRec (s, t))) t
      then TAL.TRec (s,t)
      else raise (TypeError ("Ill-typed fold", l))
    | WApp (l,w, os) ->
      begin match tc_w context w with
        | TBox (PBlock (d,c,s,q)) ->
          let (ds,dr) = List.split_n d (List.length os) in
          List.fold_left ~f:(fun t' p -> TAL'.type_sub p t') ~init:(TBox (PBlock (dr,c,s,q))) (TAL'.type_zip ds os)
        | _ -> raise (TypeError ("Can't apply non-block to types", l))
      end

  and tc_h context l mut h = match mut, h with
    | TAL.Box, TAL.HCode (d,c,s,q,is) ->
      let _ = tc_is l (set_ret (set_stack (set_reg (set_tyenv context d) c) s) q) is in
      TAL.PBlock (d,c,s,q)
    | _, TAL.HTuple ws -> TAL.PTuple (List.map ~f:(tc_w context) ws)
    | _ -> raise (TypeError ("Can't have mutable code pointers",l))

  and tc_h_shallow context l mut h = match mut, h with
    | TAL.Box, TAL.HCode (d,c,s,q,is) -> TAL.PBlock (d,c,s,q)
    | _, TAL.HTuple ws -> TAL.PTuple (List.map ~f:(tc_w context) ws)
    | _  -> raise (TypeError ("Can't have mutable code pointers",l))

end
and TAL : sig
  open Syntax
  open TAL
  val t_eq : t -> t -> bool
  val s_eq : sigma -> sigma -> bool
  val s_pref_eq : sigma_prefix -> sigma_prefix -> bool
  val q_eq : q -> q -> bool
  val psi_elem_eq : psi_elem -> psi_elem -> bool
  val type_sub : FTAL.substitution -> t -> t

  val stack_sub : FTAL.substitution -> sigma -> sigma

  val omega_sub : FTAL.substitution -> omega -> omega

  val retmarker_sub : FTAL.substitution -> q -> q

  val chi_sub : FTAL.substitution -> chi -> chi

  val type_zip : delta -> omega list -> FTAL.substitution list

  val register_subset : chi -> chi -> bool

end = struct
  open Syntax
  open TAL

  let rec psi_sub (p:FTAL.substitution) t = match t with
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

  let type_zip delt os =
    List.map2_exn ~f:(fun d o -> match d,o with
        | DAlpha a, OT t -> FTAL.TType (a,t)
        | DZeta z, OS s -> FTAL.SType (z,s)
        | DEpsilon e, OQ q -> FTAL.EMarker (e,q)
        | _ ->
          raise (Failure ("Trying to instantiate wrong type of type variables: "
                          ^ Pretty.TAL.show_delta delt ^ " and " ^ Pretty.TAL.show_omega_list os)))
      delt os


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

end
and F : sig
  open Syntax
  open F
  val t_eq : t -> t -> bool
  val type_sub : FTAL.substitution -> t -> t
  val get_loc : exp -> l
end = struct
  module TAL' = TAL
  open Syntax
  open F
  let rec type_sub p typ = match typ with
    | TVar a -> begin match p with
        | FTAL.FType (a', t) when a = a' -> t
        | _ -> typ
      end
    | TArrow (params,ret) ->
      TArrow (List.map ~f:(type_sub p) params, type_sub p ret)
    | TArrowMod (params, sin, sout, ret) ->
      TArrowMod (List.map ~f:(type_sub p) params, List.map ~f:(TAL'.type_sub p) sin, List.map ~f:(TAL'.type_sub p) sout, type_sub p ret)
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
      List.for_all2_exn ~f:TAL'.t_eq sin1 sin2 &&
      List.for_all2_exn ~f:TAL'.t_eq sout1 sout2 &&
      t_eq r1 r2
    | TRec (s1, b1), TRec (s2, b2) ->
      t_eq b1 (type_sub (FTAL.FType (s2, TVar s1)) b2)
    | TTuple ts, TTuple ts1 -> List.for_all2_exn ~f:t_eq ts ts1
    | _ -> false

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
end
