{
open Parser

exception Error of string * Lexing.position

let lexing_error lexbuf =
  let invalid_input = String.make 1 (Lexing.lexeme_char lexbuf 0) in
  raise (Error (invalid_input, lexbuf.Lexing.lex_curr_p))

let classify_type_variable lexbuf =
  let var =
    (* remove the ' that starts the lexeme *)
    let str = Lexing.lexeme lexbuf in
    String.sub str 1 (String.length str - 1) in
  match var.[0] with
  | 'a' -> TYPE_VARIABLE var
  | 'e' -> RETURN_MARKER_VARIABLE var
  | 'z' -> STACK_TYPING_VARIABLE var
  | other ->
    Printf.eprintf "Error parsing the type-level variable '%s:\n\
      type-level variables should start with either 'a' (type variables),\n\
      'e' (return marker variables) or 'z' (stack typing variables),\n\
      this variable starts with the unknown '%c'.\n"
      var var.[0];
    raise (Error (var, lexbuf.Lexing.lex_curr_p))
}

let int_literal = '-'? ['0'-'9'] ['0'-'9']*
let blank = [' ' '\t']+
let newline = ('\r'* '\n')
let identifier = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let register = ('r' ['1' - '7'] | "ra")

rule token = parse
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | blank+ { token lexbuf }
  | int_literal { INTEGER (int_of_string (Lexing.lexeme lexbuf)) }
  | "unit" { UNIT }
  | "int" { INT }
  | "exists" { EXISTS }
  | "." { DOT }
  | "mu" { MU }
  | "ref" { REF }
  | "<" { LANGLE }
  | "," { COMMA }
  | ">" { RANGLE }
  | "box" { BOX }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "pack "{ PACK }
  | "as" { AS }
  | "fold" { FOLD }
  | "code" { CODE }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | register { REGISTER (Lexing.lexeme lexbuf) }
  | "forall" { FORALL }
  | "{" { LBRACKET }
  | ";" { SEMICOLON }
  | "}" { RBRACKET }
  | ":" { COLON }
  | "::" { DOUBLECOLON }
  | "end" { END }
  | "nil" { NIL }
  | "out" { OUT }
  | "jmp" { JMP }
  | "call" { CALL }
  | "ret" { RET }
  | "halt" { HALT }
  | "add" { ADD }
  | "mul" { MUL }
  | "sub" { SUB }
  | "bnz" { BNZ }
  | "ld" { LD }
  | "st" { ST }
  | "ralloc" { RALLOC }
  | "balloc" { BALLOC }
  | "mv" { MV }
  | "salloc" { SALLOC }
  | "sfree" { SFREE }
  | "sld" { SLD }
  | "sst" { SST }
  | "unpack" { UNPACK }
  | "unfold" { UNFOLD }
  | "if0" { IF0 }
  | "pi" { PI }
  | "*" { BIGDOT }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "\\"  { LAMBDA }
  | "->" { ARROW }
  | "?" { QUESTION }
  | "FT" { FT }
  | "TF" { TF }
  | "import" { IMPORT }
  | "protect" { PROTECT }
  | identifier { IDENTIFIER (Lexing.lexeme lexbuf) }
  | "'" identifier { classify_type_variable lexbuf }
  | eof { EOF }
  | _ { lexing_error lexbuf }
