(** Parsing error reporting *)

let position {Lexing.pos_fname; pos_lnum; pos_cnum; pos_bol} =
  let file = pos_fname in
  let line = pos_lnum in
  let character = pos_cnum - pos_bol in
  (file, line, character)

let nth_line file line =
  try
    let input = open_in file in
    for i = 1 to line - 1 do
      ignore (input_line input)
    done;
    let result = input_line input in
    close_in input;
    Some result
  with _ -> None

let report_error lexbuf = function
  | Parser.Error ->
    let file, start_line, start_character = position lexbuf.Lexing.lex_start_p in
    let _, curr_line, curr_character = position lexbuf.Lexing.lex_curr_p in
    let open Printf in
    let lines =
      if curr_line = start_line
      then sprintf "line %d" curr_line
      else sprintf "lines %d-%d" start_line curr_line in
    let characters =
      if curr_line = start_line
      then sprintf "characters %d-%d" start_character curr_character
      else sprintf "character %d" start_character in
    Printf.eprintf "File %S, %s, %s, parsing error:\n%!"
      file lines characters;
    begin match nth_line file curr_line with
      | None -> ()
      | Some line -> Printf.eprintf "> %s\n" line;
    end;
  | Lexer.Error (invalid_input, err_pos) ->
    let file, line, character = position err_pos in
    Printf.eprintf
      "File %S, line %d, character %d, lexing error:\n" file line character;
    begin match nth_line file line with
      | None -> ()
      | Some line -> Printf.eprintf "> %s\n" line;
    end;
    Printf.eprintf "Invalid input %S\n%!" invalid_input
  | exn -> raise exn

(** Parsing functions *)

let parse parse_fun lexbuf =
  parse_fun Lexer.token lexbuf

let parse_string parse_fun str =
  let lexbuf = Lexing.from_string str in
  parse parse_fun lexbuf

let parse_file parse_fun path =
  let chan = open_in path in
  let lexbuf =
    let open Lexing in
    let lexbuf = from_channel chan in
    lexbuf.lex_start_p <- {
      pos_fname = path;
      pos_lnum = 1;
      pos_bol = 0;
      pos_cnum = 0;
    };
    lexbuf.lex_curr_p <- lexbuf.lex_start_p;
    lexbuf
  in
  try parse parse_fun lexbuf
  with exn ->
    report_error lexbuf exn;
    exit 1
