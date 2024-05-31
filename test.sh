#!/bin/sh
set -xe
dune build _build/default/src/ocaml_of_llvm.exe
make -C linkopt all
echo '---running ocaml_of_llvm---'
OCAMLRUNPARAM=b ./_build/default/src/ocaml_of_llvm.exe ./linkopt/build/combined.bc > testprog.ml
echo '---compiling testprog.ml---'
ocamlfind ocamlc -linkpkg -package num -g testprog.ml -o testprog
#Native compilation does work eventually, it just takes a lot of stack space and needs to happen with ocamlopt.byte.
#OCAMLRUNPARAM=l=29999999 OCAMLFIND_COMMANDS='ocamlc=ocamlc.byte ocamlopt=ocamlopt.byte' ocamlfind ocamlopt -linkpkg -package num -g testprog.ml -o testprog.byte.opt
echo '---running test.ml---'
OCAMLRUNPARAM=b ./testprog 55
echo '---success!---'
