type l = { line : int; col : int }
         [@@deriving show]
let cpos {Lexing.pos_fname; pos_lnum; pos_cnum; pos_bol} =
  let line = pos_lnum in
  let col = pos_cnum - pos_bol in
  {line = line; col = col}

let dummy_loc = { line = -1; col = -1 }

module rec FTAL : sig

  type e = FC of F.exp | TC of TAL.component

  type t = FT of F.t | TT of TAL.t

  type context = TAL.psi * TAL.delta * F.gamma * TAL.chi * TAL.q * TAL.sigma

  type substitution = FTerm of string * F.exp
                    | FType of string * F.t
                    | TType of string * TAL.t
                    | SType of string * TAL.sigma
                    | EMarker of string * TAL.q
                    | SAbs of TAL.sigma * string


end = struct

  type e = FC of F.exp | TC of TAL.component

  type t = FT of F.t | TT of TAL.t

  type context = TAL.psi * TAL.delta * F.gamma * TAL.chi * TAL.q * TAL.sigma

  type substitution = FTerm of string * F.exp
                    | FType of string * F.t
                    | TType of string * TAL.t
                    | SType of string * TAL.sigma
                    | EMarker of string * TAL.q
                    | SAbs of TAL.sigma * string

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

    type binop = BPlus | BMinus | BTimes

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

    type ft = F of exp | TC of TAL.component | TI of TAL.instr list

    type gamma = (string * F.t) list


end = struct

    type t =
        TVar of string
      | TUnit
      | TInt
      | TArrow of t list * t
      | TArrowMod of t list * TAL.sigma_prefix * TAL.sigma_prefix * t
      | TRec of string * t
      | TTuple of t list

    type binop = BPlus | BMinus | BTimes

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

    type ft = F of exp | TC of TAL.component | TI of TAL.instr list

    type gamma = (string * F.t) list



end
and TAL : sig

  type reg = string
  type loc = string

  type delta_elem =
      DAlpha of string
    | DZeta of string
    | DEpsilon of string

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

  type omega =
      OT of t
    | OS of sigma
    | OQ of q

  type w =
      WUnit of l
    | WInt of l * int
    | WLoc of l * loc
    | WPack of l * t * w * string * t
    | WFold of l * string * t * w
    | WApp of l * w * omega list


  type u =
      UW of l * w
    | UR of l * reg
    | UPack of l * t * u * string * t
    | UFold of l * string * t * u
    | UApp of l * u * omega list

  type aop = Add | Sub | Mult

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

  type h =
      HCode of delta * chi * sigma * q * instr list
    | HTuple of w list

  type heapm = (loc * (mut * h)) list

  type regm = (reg * w) list

  type stackm = w list

  type mem = heapm * regm * stackm

  type component = l * instr list * heapm

  type context =
      CComponentEmpty of l * contextI
    | CComponentHeap of l * contextC

  and contextI =
      CHoleI
    | CImportI of l * reg * string * sigma * F.t * F.context * instr list

  and contextC =
      CHoleC

end = struct

  type reg = string
  type loc = string

  type delta_elem =
      DAlpha of string
    | DZeta of string
    | DEpsilon of string

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

  type omega =
      OT of t
    | OS of sigma
    | OQ of q

  type w =
      WUnit of l
    | WInt of l * int
    | WLoc of l * loc
    | WPack of l * t * w * string * t
    | WFold of l * string * t * w
    | WApp of l * w * omega list


  type u =
      UW of l * w
    | UR of l * reg
    | UPack of l * t * u * string * t
    | UFold of l * string * t * u
    | UApp of l * u * omega list

  type aop = Add | Sub | Mult

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

  type h =
      HCode of delta * chi * sigma * q * instr list
    | HTuple of w list

  type heapm = (loc * (mut * h)) list

  type regm = (reg * w) list

  type stackm = w list

  type mem = heapm * regm * stackm

  type component = l * instr list * heapm

  type context =
      CComponentEmpty of l * contextI
    | CComponentHeap of l * contextC

  and contextI =
      CHoleI
    | CImportI of l * reg * string * sigma * F.t * F.context * instr list

  and contextC =
      CHoleC

end
