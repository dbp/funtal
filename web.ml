module H = Dom_html


let parse_report_loc parse_fun str =
  let lexbuf = Lexing.from_string str in
  try `Success (Parse.parse parse_fun lexbuf)
  with | Parser.Error ->
    let (_, line, char) = Parse.position lexbuf.Lexing.lex_start_p in
    `Error (line, "Parser Error: line " ^
                  string_of_int line ^ ", character " ^
                  string_of_int char ^ ".")
       | Lexer.Error (invalid_input, err_pos) ->
         let (_, line, char) = Parse.position err_pos in
         `Error (line, "Lexing Error: line " ^
                       string_of_int line ^ ", character " ^
                       string_of_int char ^ ".")


let simple = {|
FT [int, ?] (
[mv ra, lh;
 salloc 1; mv r1, 0; sst 0, r1;
 call l {*, end{int; *}}],
[l -> box code [z, e]
          {ra: box forall[]. {r1:int; z} e; int :: z} ra.
          [sld r1, 0;
           sfree 1;
           ret ra {r1}],
 lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])
|}

let omega = {|
  (lam(f : mu a. (a) -> a).((unfold f) f))
  (fold (mu a. (a) -> a) lam(f : mu a. (a) -> a).((unfold f) f))
  |}

let higher_order = Ftal.F.show_exp Examples.higher_order
let factorial_f = Ftal.(F.show_exp (F.EApp (dummy_loc, Examples.factorial_f, [F.EInt (dummy_loc, 3)])))
let factorial_t = Ftal.(F.show_exp (F.EApp (dummy_loc, Examples.factorial_t, [F.EInt (dummy_loc, 3)])))
let call_to_call = Ftal.(F.show_exp (F.(EBoundary (dummy_loc, TInt, None, Examples.call_to_call))))
let blocks_1 = Ftal.(F.show_exp (F.EApp (dummy_loc, Examples.blocks_1, [F.EInt (dummy_loc, 3)])))
let blocks_2 = Ftal.(F.show_exp (F.EApp (dummy_loc, Examples.blocks_2, [F.EInt (dummy_loc, 3)])))

let parse_error = {| FT [int, ?] (
  [mv r1, 1;
   add r1, r1, 1
   halt int, * {r1}],
  [])
|}
let type_error = {|
(lam(x2:int).
  (lam(f:mu a.(a,
        int) -> int, x1:int).
    if0 x1
      ()
      (x1*((unfold f) f (x1-1)))) (fold (mu b.(b,
          int) -> int) (lam(f:mu a.(a,
            int) -> int, x1:int).
        if0 x1
          1
          (x1*((unfold f) f (x1-1)))))
    x2) 3 |}

let set_error ln m =
  let _ = Js.Unsafe.((coerce global)##seterror (Js.number_of_float (float_of_int ln)) (Js.string m)) in
  ()
let clear_errors _ =
  let _ = Js.Unsafe.((coerce global)##clearerrors) in
  ()

let hide_machine _ =
  H.((getElementById "machine")##setAttribute (Js.string "hidden") (Js.string "on"))
let show_machine _ =
  H.((getElementById "machine")##removeAttribute (Js.string "hidden"))
let set_text i t =
  let open H in
  (getElementById i)##.innerHTML := Js.string t
let set_editor t =
  let open Js in
  clear_errors ();
  hide_machine ();
  let _ = Unsafe.((coerce (global##.codemirror))##setValue (string t)) in
  ()
let ehandle s =
  H.handler (fun _ -> set_editor s; Js._false)
let get_editor _ =
  Js.Unsafe.((coerce (global##.codemirror))##getValue)
let set_click i h =
  H.((getElementById i)##.onclick := h);
  ()

let _ =
  let hist = ref ((Ftal.F.EUnit Ftal.dummy_loc, ([],[],[])), []) in
  let refresh _ =
    let ((e, (h,r,s)), past) = !hist in
    let _ = match Ftal.F.decomp e with
      | None ->
        H.((getElementById "next")##setAttribute (Js.string "disabled") (Js.string "on"));
        H.((getElementById "many")##setAttribute (Js.string "disabled") (Js.string "on"));
        let _ = set_text "context" (Ftal.F.show_exp e) in
        let _ = set_text "focus" "" in
        ()
      | Some (c, f) ->
        H.((getElementById "next")##removeAttribute (Js.string "disabled"));
        H.((getElementById "many")##removeAttribute (Js.string "disabled"));
        let _ = set_text "context" (Ftal.F.show_context c) in
        let _ = set_text "focus" (Ftal.F.show_ft f) in
        ()
    in
    let _ = set_text "pc" (string_of_int (List.length past)) in
    let _ = set_text "registers" (Ftal.TAL.show_regm r) in
    let _ = set_text "stack" (Ftal.TAL.show_stackm s) in
    let _ = set_text "heap" (Ftal.TAL.show_heapm h) in
    ()
  in
  let next' _ =
    let ((e,m), rest) = !hist in
    let (nm,ne) = Ftal.F.step (m, e) in
    if e = ne && m = nm
    then ()
    else hist := ((ne,nm), (e,m)::rest)
  in
  let load _ =
    let open H in
    let _ =
      let s = Js.to_string (get_editor ()) in
      Ftal.(FTAL.(
          try
            match parse_report_loc Parser.f_expression_eof s with
            | `Success e -> begin
                let _ = tc (default_context TAL.QOut) (FC e) in
                hist := ((e, ([],[],[])), []);
                refresh ();
                clear_errors ();
                show_machine ();
                Js.Opt.return Js._false
              end
            | `Error (line, msg) ->
              begin
                set_error line msg;
                Js.Opt.return Js._false
              end
          with TypeError (t,l) ->
            begin
              set_error l.line ("Type Error: " ^ t);
              hide_machine ();
              Js.Opt.return Js._false
            end
        )) in Js._false
  in
  let next _ =
    next' ();
    refresh ();
    Js._false
  in
  let prev _ =
    begin match !hist with
      | (_, []) -> ()
      | (_, x::xs) -> hist := (x,xs); refresh ()
    end; Js._false
  in
  let many _ =
    let rec repeat f = function | 0 -> () | n -> f (); repeat f (n-1) in
    repeat next' 100;
    refresh ();
    Js._false
  in
  set_click "load" (H.handler load);
  set_click "next" (H.handler next);
  set_click "prev" (H.handler prev);
  set_click "many" (H.handler many);
  hide_machine ();
  set_click "simple" (ehandle simple);
  set_click "omega" (ehandle omega);
  set_click "call_to_call" (ehandle call_to_call);
  set_click "higher_order" (ehandle higher_order);
  set_click "blocks_1" (ehandle blocks_1);
  set_click "blocks_2" (ehandle blocks_2);
  set_click "factorial_f" (ehandle factorial_f);
  set_click "factorial_t" (ehandle factorial_t);
  set_click "parse_error" (ehandle parse_error);
  set_click "type_error" (ehandle type_error);
  set_editor simple;
  ()
