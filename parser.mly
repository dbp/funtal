%token JMP CALL RET HALT
%token BNZ LD ST RALLOC BALLOC MV SALLOC SFREE SLD SST
%token PACK AS UNPACK FOLD UNFOLD
%token IMPORT PROTECT
%token CODE END NIL OUT
%token ADD MUL SUB /* these are the assembly keywords */
%token PLUS MINUS TIMES /* these are the binary symbols */
%token FORALL EXISTS MU
%token UNIT INT REF BOX
%token LANGLE RANGLE LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token DOT BIGDOT COMMA COLON SEMICOLON DOUBLECOLON ARROW QUESTION
%token LAMBDA IF0 PI
%token FT TF
%token<string> A_IDENTIFIER Z_IDENTIFIER E_IDENTIFIER OTHER_IDENTIFIER
%token<int> INTEGER
%token<string> REGISTER
%token EOF

%left PLUS MINUS
%left TIMES

%start<Ftal.TAL.component> component_eof
%start<Ftal.TAL.mem> memory_eof
%start<Ftal.TAL.instr list> instruction_sequence_eof
%start<Ftal.TAL.heapm> heap_fragment_eof
%start<Ftal.TAL.w> word_value_eof
%start<Ftal.TAL.u> small_value_eof
%start<Ftal.TAL.delta> type_env_eof

%start<Ftal.F.t> f_type_eof
%start<Ftal.F.exp> f_expression_eof

%{ open Ftal
   open TAL
%}


%%

component_eof: c=component EOF { c }
memory_eof: m=memory EOF { m }
instruction_sequence_eof: i=instruction_sequence EOF { i }
heap_fragment_eof: h=heap_fragment EOF { h }
word_value_eof: w=word_value EOF { w }
small_value_eof: u=small_value EOF { u }
type_env_eof: delta=type_env EOF { delta }

f_type_eof: tau=f_type EOF { tau }
f_expression_eof: e=f_expression EOF { e }

f_type:
| alpha=f_type_variable { F.TVar alpha }
| UNIT { F.TUnit }
| INT { F.TInt }
| LPAREN taus=separated_list(COMMA,f_type) RPAREN ARROW tau=f_type
  { F.TArrow (taus, tau) }
| LPAREN taus=separated_list(COMMA,f_type) RPAREN
  LBRACKET sin=stack_prefix RBRACKET
  ARROW
  LBRACKET sout=stack_prefix RBRACKET
  tau=f_type
  { F.TArrowMod (taus, sin, sout, tau) }
| mu=f_mu_type { let (alpha, tau) = mu in F.TRec (alpha, tau) }
| taus=tuple(f_type) { F.TTuple taus }

  f_type_variable: alpha=type_variable { alpha }
  f_mu_type: MU alpha=f_type_variable DOT tau=f_type { (alpha, tau) }

f_simple_expression:
| x=f_term_variable { F.EVar x }
| LPAREN RPAREN { F.EUnit }
| n=int { F.EInt n }
| es=tuple(f_expression) { F.ETuple es }
| PI n=int LPAREN e=f_expression RPAREN { F.EPi (n, e) }
| LPAREN e=f_expression RPAREN { e }
| FT LBRACKET tau=f_type COMMA sigma=stack_typing_annot RBRACKET c=component
  { F.EBoundary (tau, sigma, c) }

f_app_expression:
| e=f_simple_expression { e }
| e=f_simple_expression args=nonempty_list(f_simple_expression) { F.EApp (e, args) }

f_arith_expression:
| e=f_app_expression { e }
| e1=f_arith_expression op=infixop e2=f_arith_expression { F.EBinop (e1, op, e2) }

f_expression:
| e=f_arith_expression { e }
| IF0 p=f_simple_expression e1=f_simple_expression e2=f_simple_expression
  { F.EIf0 (p, e1, e2) }
| LAMBDA args=f_telescope DOT body=f_expression
  { F.ELam (args, body) }
| LAMBDA
  LBRACKET sin=stack_prefix RBRACKET
  LBRACKET sout=stack_prefix RBRACKET
  args=f_telescope DOT body=f_expression
  { F.ELamMod (args, sin, sout, body) }
| FOLD mu=f_mu_type e=f_expression
  { let (alpha, tau) = mu in F.EFold (alpha, tau, e) }
| UNFOLD e=f_expression { F.EUnfold e }

  stack_typing_annot:
  | QUESTION { None }
  | sigma=stack_typing { Some sigma }

  f_term_variable: x=identifier { x }

  f_telescope:
  | LPAREN args=separated_list(COMMA, decl(f_term_variable, f_type)) RPAREN
  { args }

  %inline infixop:
  | PLUS { F.BPlus }
  | MINUS { F.BMinus }
  | TIMES { F.BTimes }

value_type:
| alpha=type_variable { TVar alpha }
| UNIT { TUnit }
| INT { TInt }
| ex=existential_type { let (alpha, tau) = ex in TExists (alpha, tau) }
| mu=mu_type { let (alpha, tau) = mu in TRec (alpha, tau) }
| REF taus=tuple(value_type) { TTupleRef taus }
| BOX psi=heap_value_type { TBox psi }

  existential_type:
  | EXISTS alpha=type_variable DOT tau=value_type { (alpha, tau) }
  mu_type:
  | MU alpha=type_variable DOT tau=value_type { (alpha, tau) }

simple_word_value:
| LPAREN RPAREN { WUnit }
| LPAREN w=word_value RPAREN { w }
| n=int { WInt n }
| l=location { WLoc l }
| p=pack(word_value)
  { let (tau, w, alpha, tau') = p in WPack (tau, w, alpha, tau') }

word_value:
| w=simple_word_value { w }
| f=fold(word_value)
  { let (alpha,tau,w) = f in WFold (alpha, tau, w) }
| a=app(simple_word_value)
  { let (w, omega) = a in WApp (w, omega) }

  fold(value):
  | FOLD mu=mu_type v=value
    { let (alpha, tau) = mu in (alpha, tau, v) }

  pack(value):
  | PACK LANGLE tau=value_type COMMA v=value RANGLE AS goal=existential_type
    { let (alpha,tau') = goal in (tau, v, alpha, tau') }

  app(value):
  | v=value LBRACKET omegas=separated_list(COMMA,type_instantiation) RBRACKET
    { (v, omegas) }

register:
| r=REGISTER { r }

simple_small_value:
| LPAREN u=small_value RPAREN { u }
| r=register { UR r }
| p=pack(small_value)
  { let (tau, u, alpha, tau') = p in UPack (tau, u, alpha, tau') }

small_value:
| w=word_value { UW w }
| f=fold(small_value)
  { let (alpha, tau, u) = f in UFold (alpha, tau, u) }
| a=app(simple_small_value)
  { let (u, omega) = a in UApp (u, omega) }

type_instantiation:
| tau=value_type { OT tau }
| sigma=stack_typing { OS sigma }
| q=return_marker { OQ q }

heap_value_type:
| FORALL delta=type_env DOT
  LBRACE chi=simple_register_typing SEMICOLON sigma=stack_typing
  RBRACE q=return_marker
  { PBlock (delta, chi, sigma, q) }
| taus=tuple(value_type) { PTuple taus }

heap_value:
| mut=mutability_annotation
  CODE
  delta=type_env
  LBRACE chi=simple_register_typing SEMICOLON sigma=stack_typing
  RBRACE q=return_marker
  DOT i=instruction_sequence
  { (mut, HCode (delta, chi, sigma, q, i)) }
| mut=mutability_annotation ws=tuple(word_value) { (mut, HTuple ws) }

  mutability_annotation:
  | BOX { Box }
  | REF { Ref }

/*
register_typing: li=bracketed(simple_register_typing) { li }
*/
simple_register_typing: li=separated_list(COMMA, decl(register, value_type)) { li }

stack_prefix:
  | taus=separated_list(DOUBLECOLON, value_type) { taus }

stack_typing:
| prefix=list(tau=value_type DOUBLECOLON {tau}) finish=stack_typing_end
  { finish prefix }

  stack_typing_end:
  | zeta=stack_typing_variable
    { (fun prefix -> SAbstract (prefix, zeta)) }
  | BIGDOT
    { (fun prefix -> SConcrete prefix) }

return_marker:
| r=register { QR r }
| i=int { QI i }
| epsilon=return_marker_variable { QEpsilon epsilon }
| END LBRACE tau=value_type SEMICOLON sigma=stack_typing RBRACE
  { QEnd (tau, sigma) }
| OUT { QOut }

type_env: li=bracketed(simple_type_env) { li }
simple_type_env: li=separated_list(COMMA, type_env_elem) { li}

  type_env_elem:
  | alpha=type_variable { DAlpha alpha }
  | zeta=stack_typing_variable { DZeta zeta }
  | epsilon=return_marker_variable { DEpsilon epsilon }

memory:
| LPAREN h=heap_fragment SEMICOLON r=register_file SEMICOLON s=stack RPAREN
  { (h, r, s) }

heap_fragment: li=bracketed(simple_heap_fragment) { li }
simple_heap_fragment: li=separated_list(COMMA, binding(location,heap_value)) { li }

register_file: li=bracketed(simple_register_file) { li }
simple_register_file: li=separated_list(COMMA, binding(register, word_value)) { li }

  binding(variable, value):
  | x=variable ARROW v=value { (x, v) }

  decl(variable,spec):
  | x=variable COLON s=spec { (x, s) }

stack: ws=list(w=word_value DOUBLECOLON {w}) NIL { ws }

instruction_sequence:
LBRACKET i=simple_instruction_sequence RBRACKET { i }

simple_instruction_sequence:
| i=single_instruction SEMICOLON seq=simple_instruction_sequence
  { i :: seq }
| i=final_instruction option(SEMICOLON)
  { [i] }

final_instruction:
| JMP u=small_value
  { Ijmp u }
| CALL u=small_value LBRACE sigma=stack_typing COMMA q=return_marker RBRACE
  { Icall (u, sigma, q) }
| RET r=register rr=bracereg
  { Iret (r, rr) }
| HALT tau=value_type COMMA sigma=stack_typing rr=bracereg
  { Ihalt (tau, sigma, rr) }

single_instruction:
| op=aop rd=register COMMA rs=register COMMA u=small_value
  { Iaop (op, rd, rs, u) }
| BNZ r=register COMMA u=small_value
  { Ibnz (r, u) }
| LD rd=register COMMA rs=register i=bracketpos
  { Ild (rd, rs, i) }
| ST rd=register i=bracketpos COMMA rs=register
  { Ist (rd, i, rs) }
| RALLOC rd=register COMMA n=int
  { Iralloc (rd, n) }
| BALLOC rd=register COMMA n=int
  { Iballoc (rd, n) }
| MV rd=register COMMA u=small_value
  { Imv (rd, u) }
| SALLOC n=int
  { Isalloc n }
| SFREE n=int
  { Isfree n }
| SLD rd=register COMMA i=int
  { Isld (rd, i) }
| SST i=int COMMA rs=register
  { Isst (i, rs) }
| UNPACK LANGLE alpha=type_variable COMMA rd=register RANGLE COMMA u=small_value
  { Iunpack (alpha, rd, u) }
| UNFOLD rd=register COMMA u=small_value
  { Iunfold (rd, u) }
| IMPORT r=register COMMA zeta=stack_typing_variable
  AS sigma=stack_typing COMMA tau=f_type TF LBRACE e=f_expression RBRACE
  { Iimport (r, zeta, sigma, tau, e) }
| PROTECT phi=stack_prefix COMMA zeta=stack_typing_variable
  { Iprotect (phi, zeta) }

  aop:
  | ADD { Add }
  | SUB { Sub }
  | MUL { Mult }

component:
| LPAREN i=instruction_sequence COMMA h=heap_fragment RPAREN
  { (i, h) }

type_variable:
| alpha=A_IDENTIFIER { alpha }

return_marker_variable:
| epsilon=E_IDENTIFIER { epsilon }

stack_typing_variable:
| zeta=Z_IDENTIFIER { zeta }

location:
| l=identifier { l }

identifier:
| id=A_IDENTIFIER { id }
| id=E_IDENTIFIER { id }
| id=Z_IDENTIFIER { id }
| id=OTHER_IDENTIFIER { id }

int: n=INTEGER { n }
bracereg: LBRACE r=register RBRACE { r }
bracketpos: LBRACKET i=int RBRACKET { i }

tuple(elem):
| LANGLE elems=separated_list(COMMA, elem) RANGLE { elems }


%inline braced(elem):
| LBRACE x=elem RBRACE {x}

%inline bracketed(elem):
| LBRACKET x=elem RBRACKET {x}

%inline parened(elem):
| LPAREN x=elem RPAREN {x}

%inline angled(elem):
| LANGLE x=elem RANGLE {x}


