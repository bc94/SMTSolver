# Instructions

Compilation of the solver is done with 'ocamlbuild'. 
Required installations are listed below:

 - 'opam' (the OCaml package manager)
 - 'ocamlbuild' (compilation tool that can be installed using 'opam')
 - 'core' (OCaml core package, can be installed using 'opam')
 - 'menhir' (a parser generator for OCaml, can be installed using 'opam')
 - 'zarith' (package needed for the theory solver 'Simplex_Inc.ml', can be installed using 'opam')

After all these required tools are installed, compilation can be done 
with the commands:

~~~~ 
eval `opam config env` 
ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg core -pkg zarith run_solver.native
~~~~

To run the solver use:

~~~~
./run_solver.native file option
~~~~

where `file` is a placeholder for the file containing the problem/formula that 
the solver is supposed to solve and `option` is a placeholder for the solver 
variant to be used.

`file` is allowed to have either xml format (see examples/example.xml) or a 
subset of the smt2 format (see examples/example.smt2).

`option` can be one of the following:

- `simple`
- `twl`
- `incremental`
- `indexed`

The option `simple` calls the slowest version of the solver while 
`indexed` calls the fastest and most efficient one. More information 
on the techniques used in each version can be found in Chapter 8 of the thesis.
