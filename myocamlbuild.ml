(* OASIS_START *)
(* OASIS_STOP *)
open Ocamlbuild_plugin

let () = flag ["menhir"; "parser"; "trace"] (A"--trace")

let () = dispatch dispatch_default
