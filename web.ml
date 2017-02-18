open Examples;;

module H = Dom_html


let () =
  let e = higher_order in
  (H.getElementById "input")##.innerHTML := Js.string (Ftal.F.show_exp e)
