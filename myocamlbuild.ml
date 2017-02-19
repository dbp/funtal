(* OASIS_START *)
(* OASIS_STOP *)
open Ocamlbuild_plugin


module Menhir = struct
  let menhir () =
    if !Options.ocamlyacc = N then V"MENHIR" else !Options.ocamlyacc
  let menhir_tags mly =
    tags_of_pathname mly ++"ocaml"++"parser"++"menhir"

  let menhir_produce_messages env build =
    let messages, mly = env "%.messages", env "%.mly" in
    let open Ocamlbuild_pack in
    Ocaml_compiler.prepare_compile build mly;
    Cmd(S[menhir (); T (menhir_tags mly);
          A "--list-errors"; P mly; Sh ">"; Px messages])

  let menhir_compile_messages env build =
    let mly = env "%.mly" in
    let messages = env "%.messages" in
    let target = env "%_messages.ml" in
    Cmd(S[menhir (); T (menhir_tags mly); P mly;
          A "--compile-errors"; P messages;
          Sh ">"; Px target])

  let menhir_update_messages env build =
    let mly = env "%.mly" in
    let messages = env "%.messages" in
    let tmp = Filename.temp_file "menhir" ".messages" in
    Seq [
      Cmd(S[menhir (); T (menhir_tags mly); P mly;
            A "--update-errors"; P messages;
            Sh ">"; P tmp]);
      Cmd(S[A "mv"; P tmp; P messages]);
    ]

  let dispatcher = function
      | After_rules ->
        flag ["menhir"; "parser"; "menhir_trace"] (A"--trace");
        flag ["menhir"; "parser"; "menhir_table"] (A "--table");
        flag ["menhir"; "parser"; "menhir_canonical"] (A"--canonical");
        rule "menhir: .mly -> .messages"
          ~prod:"%.messages"
          ~deps:["%.mly"]
          menhir_produce_messages;
        rule "menhir: .mly & .messages -> _messages.ml"
          ~prod:"%_messages.ml"
          ~deps:["%.mly"; "%.messages"]
          menhir_compile_messages;
        rule "menhir: .mly & .messages -> .messages & .messages.update"
          ~stamp:"%.messages.update"
          ~deps:["%.mly"; "%.messages"]
          menhir_update_messages;
      | _ -> ()
end


let _ =
       dispatch
         (fun hook ->
            dispatch_default hook;
            Menhir.dispatcher hook;
            Ocamlbuild_js_of_ocaml.dispatcher
              ~oasis_executables:["web.byte"]
              hook;
         )
