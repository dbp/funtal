## Install via opam

SETUP:

- install opam, and via opam, install ocaml 4.03 with `opam init --comp 4.03`.
- `make install-deps`
  (if this were to fail, see the local `opam` file for dependencies)

BUILD:

- `make`

EDITOR:

- Open `artifact/index.html` in a browser.

RUN TESTS:

- `./test.native`


## Install via docker

SETUP

- install docker
- `docker build -t funtal .`

EDITOR:

- Copy built javascript file: `docker run --rm funtal cat /funtal/artifact/web.js > artifact/web.js`
- Open `artifact/index.html` in a browser.

RUN TESTS:

- `docker run funtal`
