let print_component chan comp =
  let doc = Ftal.TALP.p_component comp in
  PPrintEngine.ToChannel.pretty 0.8 80 chan doc;
  output_string chan "\n";
  flush chan

let print_f_expression chan expr =
  let doc = Ftal.FP.p_exp expr in
  PPrintEngine.ToChannel.pretty 0.8 80 chan doc;
  output_string chan "\n";
  flush chan


let handle_component_file path =
  let comp = Parse.parse_file Parser.component_eof path in
  print_component stdout comp

let handle_f_expression_file path =
  let expr = Parse.parse_file Parser.f_expression_eof path in
  print_f_expression stdout expr

let roundtrip_component comp =
  let path = "tmp.ftal" in
  let chan = open_out path in
  print_component chan comp;
  close_out chan;
  handle_component_file path

let roundtrip_f_expression expr =
  let path = "tmp.ftal" in
  let chan = open_out path in
  print_f_expression chan expr;
  close_out chan;
  handle_f_expression_file path

let () = handle_component_file Sys.argv.(1)
