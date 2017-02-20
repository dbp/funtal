FROM ocaml/opam:debian-9_ocaml-4.03.0
ADD Makefile /funtal/Makefile
ADD opam /funtal/opam
ADD _oasis /funtal/_oasis
ADD _tags /funtal/_tags
WORKDIR /funtal
USER opam
ADD *.ml* /funtal/
ADD artifact /funtal/artifact
RUN sudo chown -R opam /funtal
ADD build.sh /funtal/build.sh
RUN sudo -u opam bash ./build.sh
CMD ./test.native