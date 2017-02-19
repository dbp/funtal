open Examples;;

module H = Dom_html

let _ =
  let e = ref higher_order in
  let m = ref ([],[],[]) in
  let es = Ftal.F.show_exp !e in
  let set_text i t =
    let open H in
    (getElementById i)##.innerHTML := Js.string t
  in
  let refresh _ =
    let (h,r,s) = !m in
    let _ = match Ftal.F.decomp !e with
      | None ->
        let _ = set_text "context" (Ftal.F.show_exp !e) in
        let _ = set_text "focus" "" in
        ()
      | Some (c, f) ->
        let _ = set_text "context" (Ftal.F.show_context c) in
        let _ = set_text "focus" (Ftal.F.show_ft f) in
        ()
    in
    let _ = set_text "registers" (Ftal.TAL.show_regm r) in
    let _ = set_text "stack" (Ftal.TAL.show_stackm s) in
    let _ = set_text "heap" (Ftal.TAL.show_heapm h) in
    ()
  in
  let next _ =
    let (nm,ne) = Ftal.F.step (!m, !e) in
    m := nm;
    e := ne;
    refresh ();
    Js._false
  in
  let _ = H.((getElementById "next")##.onclick := (H.handler next)) in
  Js.Opt.bind(H.(CoerceTo.textarea (getElementById "input")))
    (fun e -> e##.value := Js.string es; Js.Opt.return ())
