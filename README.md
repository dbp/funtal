SETUP:
   - install opam, and ocaml 4.03
   - make install-deps
     (if this were to fail,
      see the local `opam` file for dependencies)

RUN TESTS:
   - make test

DEBUG:
   - `DEBUG=1 make test` will print out debug logging messages.

TODO:
   - do renaming for heap fragment loading
   ...
