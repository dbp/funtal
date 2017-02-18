SETUP:
   - install opam, and ocaml 4.03
   - opam install oasis menhir pprint ppx_deriving ounit core_kernel

RUN TESTS:
   - make test

DEBUG:
   - `DEBUG=1 make test` will print out debug logging messages.

TODO:
   - do renaming for heap fragment loading
   ...
