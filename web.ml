open Examples;;

module H = Dom_html

let p1 = {|FT [int, ?] (
     mv r1, 1;
     add r1, r1, 1;
     halt int, * {r1}
;
     []
)|}

let _ =
  let hist = ref ((higher_order, ([],[],[])), []) in
  let set_text i t =
    let open H in
    (getElementById i)##.innerHTML := Js.string t
  in
  let set_editor t =
    let open Js in
    Unsafe.((coerce (global##.codemirror))##setValue (string p1))
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
            let _ = H.((getElementById "machine")##removeAttribute (Js.string "hidden")) in
            Js.Opt.return Js._false
          with TypeError (t,_)
             | TypeErrorW (t,_)
             | TypeErrorH (t,_,_)
             | TypeErrorU (t,_)  ->
            begin
              set_text "error" ("Type Error: " ^ t);
              let _ = H.((getElementById "machine")##setAttribute (Js.string "hidden") (Js.string "on")) in
              Js.Opt.return Js._false
            end
             | x -> set_text "error" "Parse Error";
               let _ = H.((getElementById "machine")##setAttribute (Js.string "hidden") (Js.string "on")) in
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
  let _ = set_editor p1 in
  ()
