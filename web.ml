module H = Dom_html

let simple = {|
FT [int, ?] (
  [mv r1, 1;
   add r1, r1, 1;
   halt int, * {r1}],
  [])
|}

let higher_order = Ftal.F.show_exp Examples.higher_order
let factorial_f = Ftal.F.show_exp Examples.factorial_f
let factorial_t = Ftal.F.show_exp Examples.factorial_t
let call_to_call = Ftal.F.show_exp (Ftal.F.(EBoundary (TInt, None, Examples.call_to_call)))
let blocks_1 = Ftal.F.show_exp Examples.blocks_1
let blocks_2 = Ftal.F.show_exp Examples.blocks_2

let _ =
  let hist = ref ((Ftal.F.EUnit, ([],[],[])), []) in
  let hide_machine _ =
    H.((getElementById "machine")##setAttribute (Js.string "hidden") (Js.string "on"))
  in
  let show_machine _ =
    H.((getElementById "machine")##removeAttribute (Js.string "hidden"))
  in
  let set_text i t =
    let open H in
    (getElementById i)##.innerHTML := Js.string t
  in
  let set_editor t =
    let open Js in
    set_text "error" "";
    hide_machine ();
    Unsafe.((coerce (global##.codemirror))##setValue (string t))
  in
  let ehandle s =
    H.handler (fun _ -> set_editor s)
  in
  let get_editor _ =
    Js.Unsafe.((coerce (global##.codemirror))##getValue)
  in
  let refresh _ =
    let ((e, (h,r,s)), past) = !hist in
    let _ = match Ftal.F.decomp e with
      | None ->
        let _ = set_text "context" (Ftal.F.show_exp e) in
        let _ = set_text "focus" "" in
        ()
      | Some (c, f) ->
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
            let e = Parse.parse_string Parser.f_expression_eof s in
            let _ = tc (default_context TAL.QOut) (FC e) in
            hist := ((e, ([],[],[])), []);
            refresh ();
            set_text "error" "";
            show_machine ();
            Js.Opt.return Js._false
          with TypeError (t,_)
             | TypeErrorW (t,_)
             | TypeErrorH (t,_,_)
             | TypeErrorU (t,_)  ->
            begin
              set_text "error" ("Type Error: " ^ t);
              hide_machine ();
              Js.Opt.return Js._false
            end
             | x -> set_text "error" "Parse Error";
               hide_machine ();
               Js.Opt.return Js._false
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
  let _ = H.((getElementById "load")##.onclick := (H.handler load)) in
  let _ = H.((getElementById "next")##.onclick := (H.handler next)) in
  let _ = H.((getElementById "prev")##.onclick := (H.handler prev)) in
  let _ = H.((getElementById "many")##.onclick := (H.handler many)) in
  let _ = H.((getElementById "machine")##setAttribute (Js.string "hidden") (Js.string "on")) in
  let _ = H.((getElementById "simple")##.onclick := (ehandle simple)) in
  let _ = H.((getElementById "call_to_call")##.onclick := (ehandle call_to_call)) in
  let _ = H.((getElementById "higher_order")##.onclick := (ehandle higher_order)) in
  let _ = H.((getElementById "blocks_1")##.onclick := (ehandle blocks_1)) in
  let _ = H.((getElementById "blocks_2")##.onclick := (ehandle blocks_2)) in
  let _ = H.((getElementById "factorial_f")##.onclick := (ehandle factorial_f)) in
  let _ = H.((getElementById "factorial_t")##.onclick := (ehandle factorial_t)) in
  let _ = set_editor simple in
  ()
