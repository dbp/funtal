open Examples;;

module H = Dom_html

let _ =
  let hist = ref ((higher_order, ([],[],[])), []) in
  let es = Ftal.F.show_exp (fst (fst !hist)) in
  let set_text i t =
    let open H in
    (getElementById i)##.innerHTML := Js.string t
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
  let _ = H.((getElementById "next")##.onclick := (H.handler next)) in
  let _ = H.((getElementById "prev")##.onclick := (H.handler prev)) in
  let _ = H.((getElementById "many")##.onclick := (H.handler many)) in
  Js.Opt.bind(H.(CoerceTo.textarea (getElementById "input")))
    (fun e -> e##.value := Js.string es; Js.Opt.return ())
