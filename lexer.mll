{
open Parser

exception Error of string * Lexing.position

let lexing_error lexbuf =
  let invalid_input = String.make 1 (Lexing.lexeme_char lexbuf 0) in
  raise (Error (invalid_input, lexbuf.Lexing.lex_curr_p))
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
  | "*" { BIGDOT }
  | "[]" { EMPTY }
  | identifier { IDENTIFIER (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { lexing_error lexbuf }
