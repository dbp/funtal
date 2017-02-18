(* OASIS_START *)
(* OASIS_STOP *)
open Ocamlbuild_plugin

let () = flag ["menhir"; "parser"; "trace"] (A"--trace")

let () = dispatch dispatch_default

let _ =
       Ocamlbuild_plugin.dispatch
         (fun hook ->
            dispatch_default hook;
            Ocamlbuild_js_of_ocaml.dispatcher
              ~oasis_executables:["web.byte"]
              hook;
         )
