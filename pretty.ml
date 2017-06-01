open Utils
open Syntax

module rec Printer : sig
  open PPrint
  val r : document -> string
end = struct
  let r d =
    let b = Buffer.create 100 in
    PPrint.ToBuffer.pretty 0.8 80 b d;
    Buffer.contents b
end and TALP : sig
  open Syntax
  open PPrint
  val p_w : TAL.w -> document
  val p_t : TAL.t -> document
  val p_o : TAL.omega -> document
  val p_o_list : TAL.omega list -> document
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
  open PPrint
  open Syntax.TAL

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
  and p_o_list (os : omega list) : document =
    group (lbracket ^^ align
             (group (separate_map (semi ^^ break 1) p_o os ^^ rbracket)))
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
end
and FP : sig
  open Syntax
  open PPrint
  val p_t : F.t -> document
  val p_exp : F.exp -> document
  val p_context : F.context -> document

end = struct
  open PPrint
  open Syntax.F

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
