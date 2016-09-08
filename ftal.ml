(*
SETUP:
   - install opam, and ocaml 4.03
   - opam install ppx_deriving ounit

RUN TESTS:
   - make test

DEBUG:
   - `DEBUG=1 make test` will print out debug logging messages.

TODO:
   - write examples out
   - do renaming for heap fragment loading
   - actually implement type substitutions
   - implement type checker
   ...
*)

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

  val gen_sym : unit -> string

end = struct

  let gen_sym =
    let count = ref 0 in
    fun () -> let v = !count in count := v + 1; String.concat "" ["g"; string_of_int v]

  let rec tytrans t =
    match t with
      F.TVar s -> TAL.TVar s
    | F.TUnit -> TAL.TUnit
    | F.TInt -> TAL.TInt
    | F.TRec (a,t) -> TAL.TRec (a, tytrans t)
    | F.TTuple ts -> TAL.TBox (TAL.PTuple (List.map tytrans ts))
    | F.TArrow (z,ps,t1) ->
      let zeta = gen_sym () in
      let epsilon = gen_sym () in
      TAL.TBox (TAL.PBlock ([TAL.DZeta zeta; TAL.DEpsilon epsilon],
                            [("ra", TAL.TBox (TAL.PBlock ([],
                                                          [("r1", tytrans t1)],
                                                          (TAL.SZeta zeta),
                                                          (TAL.QEpsilon epsilon))))],
                            (List.fold_left (fun r e -> TAL.SCons (e,r))
                               (TAL.SZeta zeta)
                               (List.map tytrans ps)),
                            (TAL.QR "ra")))

  let rec ft t w m =
    let (hm,rm,sm) = m in
    match (t, w) with
    | (F.TUnit, TAL.WUnit) -> (m, F.EUnit)
    | (F.TInt, TAL.WInt n) -> (m, F.EInt n)
    | (F.TTuple ts, TAL.WLoc l) ->
      begin match List.assoc l hm with
        | TAL.HTuple ws ->
          let (m', vs) =
            List.fold_left
              (fun (mx, b) (t,w) -> let (m'',v) = ft t w mx in (m'', v::b))
              (m, [])
              (List.combine ts ws) in
          (m', F.ETuple vs)
        | _ -> raise (Failure "ft: can't convert tuple if loc isn't pointing to tuple")
      end
    | (F.TRec (a, t), TAL.WFold (a',t',w)) when tytrans (F.TRec (a,t)) = TAL.TRec (a', t') ->
      let (m', v) = ft (F.tysub t (F.TRec (a, t)) a) w m in
      (m', F.EFold (a, t, v))
    | (F.TArrow (z,ts,t1), TAL.WLoc l) ->
      let lend = gen_sym () in
      let hend =
        TAL.HCode ([TAL.DZeta z],
                   [("r1", tytrans t1)],
                   (TAL.SZeta z),
                   (TAL.QEnd (tytrans t1, TAL.SZeta z)),
                   [TAL.Iret (TAL.QEnd (tytrans t1, TAL.SZeta z), "r1")]) in
      let ps = List.map (fun t -> (gen_sym (), t)) ts in
      let v = F.ELam (z, ps, F.EBoundary
                        (t1, (TAL.(List.append
                                     (List.concat (List.map (fun (x,xt) -> [Iimport ("r1", SZeta z, xt, F.EVar x); Isalloc 1; Isst (0, "r1")]) ps))
                                     [Imv ("ra", UApp (UW (WLoc lend), [OS (SZeta z)]));
                                      Ijmp (UApp (UW w, [OS (SZeta z); OQ (QEnd (tytrans t1, SZeta z))]))], []))))
      in (((lend, hend)::hm,rm,sm), v)

    | _ -> raise (Failure "ft: can't convert")

  let rec tf t v m =
    let (hm,rm,sm) = m in
    match (t, v) with
    | (F.TUnit, F.EUnit) -> (m, TAL.WUnit)
    | (F.TInt, F.EInt n) -> (m, TAL.WInt n)
    | (F.TTuple ts, F.ETuple es) ->
      let ((hm',rm',sm'), ws) = List.fold_left
          (fun (mx, b) (t,v) -> let (m'', w) = tf t v mx in (m'', w::b))
          (m, [])
          (List.combine ts es) in
      let l = gen_sym () in
      (((l,TAL.HTuple ws)::hm',rm',sm'), TAL.WLoc l)
    | (F.TRec (a,t), F.EFold (a',t',e)) when (a',t') = (a,t) ->
      let (m', w) = tf (F.tysub t (F.TRec (a,t)) a) e m in
      (m', TAL.WFold (a,tytrans t,w))
    | (F.TArrow (z,ts,t1), F.ELam (z',ps,body)) when z = z' ->
      let l = gen_sym () in
      let e = gen_sym () in
      let s' =
        List.fold_left (fun r e -> TAL.SCons (e,r))
          (TAL.SZeta z)
          (List.map tytrans ts) in
      let s = TAL.(SCons (TBox (PBlock ([], [("r1", tytrans t1)],
                                           SZeta z, QEpsilon e)),
                     s')) in
      let body_wrapped =
        let n = List.length ts in
        List.fold_left (fun b (i, (id, t')) ->
            F.sub (id, F.EBoundary (t', ([TAL.Isld ("r1", n+1-i);
                                          TAL.Iret
                                            (TAL.QEnd (tytrans t1, s),
                                           "r1")], []))) body)
          body
          (List.mapi (fun i x -> (i,x)) ps)
      in
      let instrs = TAL.([Isalloc 1; Isst (0, "ra"); Iimport ("r1", SZeta z, t1, body_wrapped);
                         Isld ("ra",0); Isfree (List.length ts + 1); Iret (QR "ra", "r1")]) in
      let h =
        TAL.(HCode
               ([DZeta z; DEpsilon e],
                [("ra", TBox (PBlock ([], [("r1", tytrans t1)], SZeta z, QEpsilon e)))],
                s',
                QR "ra",
                instrs))
      in
      (((l,h)::hm,rm,sm), TAL.WLoc l)
    | _ -> raise (Failure "tf: can't convert")

end
and F : sig

  type t =
    TVar of string
    | TUnit
    | TInt
    | TArrow of string * t list * t
    | TRec of string * t
    | TTuple of t list
  val show : t -> bytes
  val pp : Format.formatter -> t -> unit

  type binop = BPlus | BMinus | BTimes
  val show_binop : binop -> bytes

  type exp =
      EVar of string
    | EUnit
    | EInt of int
    | EBinop of exp * binop * exp
    | EIf0 of exp * exp * exp
    | ELam of string * (string * t) list * exp
    | EApp of exp * TAL.sigma list * exp list
    | EFold of string * t * exp
    | EUnfold of exp
    | ETuple of exp list
    | EPi of int * exp
    | EBoundary of t * TAL.component
  val show_exp : exp -> bytes
  val pp_exp : Format.formatter -> exp -> unit

  type context =
      CHole
    | CBinop1 of context * binop * exp
    | CBinop2 of exp * binop * context
    | CIf0 of context * exp * exp
    | CApp1 of context * TAL.sigma list * exp list
    | CAppn of exp * TAL.sigma list * exp list * context * exp list
    | CFold of string * t * context
    | CUnfold of context
    | CTuple of exp list * context * exp list
    | CPi of int * context
    | CBoundary of t * TAL.context
  val show_context : context -> bytes
  val pp_context : Format.formatter -> context -> unit

  val value : exp -> bool

  val sub : string * exp -> exp -> exp

  val tysub : t -> t -> string -> t

  type ft = F of exp | TC of TAL.component | TI of TAL.instr list
  val show_ft : ft -> bytes

  val plug : context -> ft -> exp

  val decomp : exp -> (context * F.ft) option

  val step : TAL.mem * exp -> TAL.mem * exp

  val stepn : int -> TAL.mem * exp -> TAL.mem * exp

end = struct

  type t =
    TVar of string
    | TUnit
    | TInt
    | TArrow of string * t list * t
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
    | ELam of string * (string * t) list * exp
    | EApp of exp * TAL.sigma list * exp list
    | EFold of string * t * exp
    | EUnfold of exp
    | ETuple of exp list
    | EPi of int * exp
    | EBoundary of t * TAL.component
  [@@deriving show]

  let rec value e =
    match e with
    | EUnit -> true
    | EInt _ -> true
    | ELam _ -> true
    | EFold _ -> true
    | ETuple es -> List.for_all value es
    | _ -> false

  type context =
      CHole
    | CBinop1 of context * binop * exp
    | CBinop2 of exp * binop * context
    | CIf0 of context * exp * exp
    | CApp1 of context * TAL.sigma list * exp list
    | CAppn of exp * TAL.sigma list * exp list * context * exp list
    | CFold of string * t * context
    | CUnfold of context
    | CTuple of exp list * context * exp list
    | CPi of int * context
    | CBoundary of t * TAL.context
  [@@deriving show]

  type tyenv = string list
  type env = (string * t) list

  let rec sub p e =
    let (x',e') = p in
    match e with
    | EVar x -> if x = x' then e' else e
    | EUnit -> e
    | EInt _ -> e
    | EBinop (e1, b, e2) -> EBinop (sub p e1, b, sub p e2)
    | EIf0 (e1, e2, e3) -> EIf0 (sub p e1, sub p e2, sub p e3)
    | ELam (zeta, args, body) -> if List.mem_assoc x' args then e else ELam (zeta, args, sub p body)
    | EApp (e1, os, eargs) -> EApp (sub p e1, os, List.map (sub p) eargs)
    | EFold (s, t, e1) -> EFold (s, t, sub p e1)
    | EUnfold e1 -> EUnfold (sub p e1)
    | ETuple es -> ETuple (List.map (sub p) es)
    | EPi (n, e1) -> EPi (n, sub p e1)
    | EBoundary (t,comp) -> EBoundary (t, TAL.sub p comp)

  (* NOTE(dbp 2016-09-06): Not implemented yet, since we can
     evaluate w/o them. *)
  let tysub t t' a = t

  let step_prim (m, e) =
    match e with
    | EBinop (EInt n1, BPlus, EInt n2) -> (m, EInt (n1 + n2))
    | EBinop (EInt n1, BMinus, EInt n2) -> (m, EInt (n1 - n2))
    | EBinop (EInt n1, BTimes, EInt n2) -> (m, EInt (n1 * n2))
    | EIf0 (EInt 0, e2, e3) -> (m, e2)
    | EIf0 (EInt _, e2, e3) -> (m, e3)
    | EApp (ELam (zeta, ps, body), os, eargs) when List.(length ps = length eargs) ->
      (m, List.fold_left (fun e p -> sub p e) body (List.combine (List.map fst ps) eargs))
    | EUnfold (EFold (_,_,eb)) -> (m, eb)
    | EPi (n, (ETuple vs)) when List.length vs > n -> (m, List.nth vs n)
    | EBoundary (t, ([TAL.Iret (TAL.QEnd (t',s),r)],[])) ->
      let (hm,rm,sm) = m in
      FTAL.ft t (List.assoc r rm) m
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

    | EApp (e1, os, eargs) when not (value e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CApp1 (ctxt, os, eargs), e'))
    | EApp (e1, os, eargs) when value e1 && List.exists (fun x -> not (value x)) eargs ->
      decomp_list eargs (fun bef ctxt aft e' -> Some (CAppn (e1, os, bef, ctxt, aft), e'))
    | EApp (e1, os, eargs) -> Some (CHole, F e)

    | EUnfold e1 when value e1 -> Some (CHole, F e)
    | EUnfold e1 -> decomp_cont e1 (fun ctxt e' -> Some (CUnfold ctxt, e'))

    | ETuple es ->
      decomp_list es (fun bef ctxt aft e' -> Some (CTuple (bef, ctxt, aft), e'))

    | EPi (n, e1) when value e1 -> Some (CHole, F e)
    | EPi (n, e1) ->
      decomp_cont e1 (fun ctxt e' -> Some (CPi (n, ctxt), e'))

    | EBoundary (t, comp) ->
      begin match TAL.decomp comp with
          None -> Some (CHole, F e)
        | Some (ctxt, e') -> Some (CBoundary (t, ctxt), e')
      end

    | _ -> None
  and decomp_cont e f =
    match decomp e with
    | None -> None
    | Some (ctxt, e') -> f ctxt e'
  and decomp_list es f =
    match split_at
                (fun x -> is_some (snd x))
                (List.map (fun ea -> (ea, decomp ea)) es) with
    | (bef, Some (_, Some (ctxt, e')), aft) ->
      f (List.map fst bef) ctxt (List.map fst aft) e'
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
    | CApp1 (ctxt', os, es) -> EApp (plug ctxt' e, os, es)
    | CAppn (ef, os, bef, ctxt', aft) -> EApp (ef, os, List.concat [bef; [plug ctxt' e]; aft])
    | CFold (s, t, ctxt') -> EFold (s, t, plug ctxt' e)
    | CUnfold ctxt' -> EUnfold (plug ctxt' e)
    | CTuple (bef, ctxt', aft) -> ETuple (List.concat [bef; [plug ctxt' e]; aft])
    | CPi (n, ctxt') -> EPi (n, plug ctxt' e)
    | CBoundary (t,talctxt) -> EBoundary (t, TAL.plug talctxt e)


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
      let _ = Debug.log "decomp TI instrs" (String.concat "; " (List.map (fun i -> TAL.show_instr i) is)) in
      let _ = Debug.log "decomp TI regs" (TAL.show_regm r) in
      let (m', is') = TAL.reduce (m, is) in
      let _ = Debug.log "stepped TI instrs" (String.concat "; " (List.map (fun i -> TAL.show_instr i) is')) in
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
end
and TAL : sig


  type reg = string
  type loc = string

  type delta_elem =
      DAlpha of string
    | DZeta of string
    | DEpsilon of string
  val show_delta_elem : delta_elem -> bytes

  type delta = delta_elem list

  type t =
      TVar of string
    | TUnit
    | TInt
    | TExists of string * t
    | TRec of string * t
    | TTupleRef of t list
    | TBox of psi

  and sigma =
      SZeta of string
    | SNil
    | SCons of t * sigma

  and q =
      QR of reg
    | QI of int
    | QEpsilon of string
    | QEnd of t * sigma
    | QOut

  and psi =
      PBlock of delta * chi * sigma * q
    | PTuple of t list

  and chi = (reg * t) list

  val show : t -> bytes
  val show_sigma : sigma -> bytes
  val pp_sigma : Format.formatter -> sigma -> unit
  val show_q : q -> bytes
  val pp_q : Format.formatter -> q -> unit
  val show_psi : psi -> bytes
  val pp_psi : Format.formatter -> psi -> unit

  type omega =
      OT of t
    | OS of sigma
    | OQ of q
  val show_omega : omega -> bytes

  type w =
      WUnit
    | WInt of int
    | WLoc of loc
    | WPack of t * w * string * t
    | WFold of string * t * w
    | WApp of w * omega list
  val show_w : w -> bytes

  type u =
      UW of w
    | UR of reg
    | UPack of t * u * string * t
    | UFold of string * t * u
    | UApp of u * omega list
  val show_u : u -> bytes

  type aop = Add | Sub | Mult
  val show_aop : aop -> bytes

  type instr =
      Iaop of aop * reg * reg * u
    | Isub of reg * reg * u
    | Imult of reg * reg * u
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
    | Iret of q * reg
    | Iimport of reg * sigma * F.t * F.exp
  val show_instr : instr -> bytes
  val pp_instr : Format.formatter -> instr -> unit

  type h =
      HCode of delta * chi * sigma * q * instr list
    | HTuple of w list
  val show_h : h -> bytes

  type heapm = (loc * h) list
  type regm = (reg * w) list
  val show_regm : regm -> bytes

  type stackm = w list

  type mem = heapm * regm * stackm

  val load : mem -> heapm -> mem

  type component = instr list * heapm
  val show_component : component -> bytes
  val pp_component : Format.formatter -> component -> unit

  type context =
      CComponentEmpty of contextI
    | CComponentHeap of contextC

  and contextI =
      CHoleI
    | CImportI of reg * sigma * F.t * F.context * instr list

  and contextC =
      CHoleC

  val show_context : context -> bytes
  val pp_context : Format.formatter -> context -> unit
  val show_contextI : contextI -> bytes
  val show_contextC : contextC -> bytes

  val sub : (string * F.exp) -> component -> component

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
    | TBox of psi
  [@@deriving show]

  and sigma =
      SZeta of string
    | SNil
    | SCons of t * sigma
  [@@deriving show]

  and q =
      QR of reg
    | QI of int
    | QEpsilon of string
    | QEnd of t * sigma
    | QOut
  [@@deriving show]

  and psi =
      PBlock of delta * chi * sigma * q
    | PTuple of t list
  [@@deriving show]

  and chi = (reg * t) list

  type omega =
      OT of t
    | OS of sigma
    | OQ of q
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
    | Isub of reg * reg * u
    | Imult of reg * reg * u
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
    | Iret of q * reg
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
    (List.map
       (fun i -> match i with
          | Iimport (r,s,t,e) -> Iimport (r,s,t,F.sub p e)
          | _ -> i
       ) is,
     List.map (fun (l,h) ->
         match h with
         | HCode (d,c,s,q,is) -> let (is',_) = sub p (is,[]) in (l, HCode (d,c,s,q,is'))
         | _ -> (l,h)
       ) hm)

  let decomp (is, m) =
    match m with
    | [] ->
      begin match is with
        | [] -> None
        | Iret _ :: _-> None
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
    | UR rn -> List.assoc rn r

  let delta op w1 w2 =
    match (op, w1, w2) with
    | (Add, WInt n1, WInt n2) -> WInt (n1 + n2)
    | (Sub, WInt n1, WInt n2) -> WInt (n1 - n2)
    | (Mult, WInt n1, WInt n2) -> WInt (n1 * n2)
    | _ -> raise (Failure "delta given args that don't make any sense")

  (* NOTE(dbp 2016-09-06): Not implemented yet, since we can
     evaluate w/o them. *)
  let tysub _ _ is = is

  let replace rm r w = (r, w) :: List.remove_assoc r rm

  let rec list_replace i l x =
    if i < 0 then raise (Failure "list_replace: don't pass negative indices!") else
      match (i, l) with
      | (0, _::xs) -> x::xs
      | (_, y::xs) -> y::(list_replace (i-1) xs x)
      | (_, []) -> raise (Failure "list_replace: index larger than list")

  let rec list_take n l =
    match (n, l) with
    | (0, _) -> []
    | (_, x::xs) -> x::(list_take (n-1) xs)
    | (_, []) -> raise (Failure "list_take: taking more elements than exist")

  let rec list_drop n l =
    match (n, l) with
    | (0, _) -> l
    | (_, _::xs) -> list_drop (n-1) xs
    | (_, []) -> raise (Failure "list_drop: dropping more elements than exist")

  let rec list_repeat n v =
    match n with
    | 0 -> []
    | _ -> v :: list_repeat (n-1) v


  let reduce (c : mem * instr list) =
    match c with
    | ((hm,rm,sm), Iaop (op, rd, rs, u)::is) ->
      ((hm, replace rm rd (delta op (List.assoc rs rm) (ru rm u)), sm), is)
    | ((hm,rm,sm), Ibnz (r,u)::is) ->
      begin match List.assoc r rm with
        | WInt 0 -> ((hm,rm,sm), is)
        | WInt _ ->
          let hc os l =
            match List.assoc l hm with
            | HCode (delt,ch,s,qr,is) -> tysub os delt is
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
      begin match List.assoc rs rm with
        | WLoc l ->
          begin match List.assoc l hm with
            | HTuple ws when List.length ws > i ->
              ((hm, replace rm rd (List.nth ws i), sm), is)
            | HTuple _ -> raise (Failure "ld: tuple index out of bounds")
            | _ -> raise (Failure "ld: trying to load from non-tuple")
          end
        | _ -> raise (Failure "ld: trying to load from non-location")
      end
    | ((hm,rm,sm), Ist (rd,i,rs)::is) ->
      begin match List.assoc rd rm with
        | WLoc l ->
          begin match List.assoc l hm with
            | HTuple ws when List.length ws > i ->
              (((replace hm l (HTuple (list_replace i ws (List.assoc rs rm)))), rm, sm), is)
            | HTuple _ -> raise (Failure "st: tuple index out of bounds")
            | _ -> raise (Failure "st: trying to store to non-tuple")
          end
        | _ -> raise (Failure "st: trying to store to non-location")
      end
    | ((hm,rm,sm), Iralloc (rd,n)::is) when List.length sm >= n ->
      let l = FTAL.gen_sym () in (((l, HTuple (list_take n sm)) :: hm, replace rm rd (WLoc l), list_drop n sm), is)
    | ((hm,rm,sm), Iballoc (rd,n)::is) when List.length sm >= n ->
      let l = FTAL.gen_sym () in (((l, HTuple (list_take n sm)) :: hm, replace rm rd (WLoc l), list_drop n sm), is)
    | ((hm,rm,sm), Imv (rd,u)::is) ->
      ((hm, replace rm rd (ru rm u), sm), is)
    | ((hm,rm,sm), Iunpack (a,rd,u)::is) ->
      begin match ru rm u with
        | WPack (t1,w,a,t2) -> ((hm, replace rm rd w, sm), tysub [t1] [DAlpha a] is)
        | _ -> raise (Failure "unpack: trying to unpack non-pack")
      end
    | ((hm,rm,sm), Iunfold (rd, u)::is) ->
      begin match ru rm u with
        | WFold (a,t,w) -> ((hm, replace rm rd w, sm), is)
        | _ -> raise (Failure "unfold: trying to unpack non-pack")
      end
    | ((hm,rm,sm), Isalloc n::is) ->
      ((hm,rm,list_repeat n WUnit), is)
    | ((hm,rm,sm), Isfree n::is) when List.length sm >= n ->
      ((hm,rm,list_drop n sm), is)
    | ((hm,rm,sm), Isld (rd,i)::is) when List.length sm > i ->
      ((hm, replace rm rd (List.nth sm i), sm), is)
    | ((hm,rm,sm), Isst (i,rs)::is) when List.length sm > i ->
      ((hm,rm,list_replace i sm (List.assoc rs rm)), is)
    | ((hm,rm,sm), Ijmp u::is) ->
      let hc os l =
        match List.assoc l hm with
        | HCode (delt,ch,s,qr,is) -> tysub os delt is
        | _ -> raise (Failure "jumping to non-code")
      in
      begin match ru rm u with
        | WLoc l -> ((hm,rm,sm), hc [] l)
        | WApp (WLoc l, os) -> ((hm,rm,sm), hc os l)
        | _ -> raise (Failure "jmp: trying to jump to non-location")
      end
    | ((hm,rm,sm), Icall (u,s,q)::is) ->
      let hc os l =
        match List.assoc l hm with
        | HCode (delt,ch,s,qr,is) ->
          tysub (List.append os [OQ q; OS s]) delta is
        | _ -> raise (Failure "calling to non-code")
      in
      begin match ru rm u with
        | WLoc l -> ((hm,rm,sm), hc [] l)
        | WApp (WLoc l, os) -> ((hm,rm,sm), hc os l)
        | _ -> raise (Failure "call: trying to jump to non-location")
      end
    | ((hm,rm,sm), Iret (QR rloc,_)::is) ->
      let hc os l =
        match List.assoc l hm with
        | HCode (delt,ch,s,qr,is) -> tysub os delt is
        | _ -> raise (Failure "returning to non-code")
      in
      begin match List.assoc rloc rm with
        | WLoc l -> ((hm,rm,sm), hc [] l)
        | WApp (WLoc l, os) -> ((hm,rm,sm), hc os l)
        | _ -> raise (Failure "ret: trying to return to non-location")
      end
    | ((hm,rm,sm), Iimport (r,s,t,v)::is) ->
      let (m, w) = FTAL.tf t v (hm,rm,sm) in
      (m, Imv (r, UW w)::is)
    | _ -> c

end
