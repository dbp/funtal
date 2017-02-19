let () =
  let comp = Parse.parse_file Parser.component_eof (Sys.argv.(1)) in
  let doc = Ftal.TALP.p_component comp in
  PPrintEngine.ToChannel.pretty 0.8 80 stdout doc;
  print_newline ()
