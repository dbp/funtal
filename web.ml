open Examples;;

module H = Dom_html

let _ =
  let e = higher_order in
  let es = Ftal.F.show_exp e in
  Js.Opt.bind(H.(CoerceTo.textarea (getElementById "input")))
    (fun e -> e##.value := Js.string es; Js.Opt.return ())
