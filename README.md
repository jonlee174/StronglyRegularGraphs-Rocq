# Strongly Regular Graphs in Rocq

A small library formalizing strongly regular graphs (SRGs) in Rocq, built on MathComp and coq-graph-theory.

## What's here

- `main.v` — core definitions (neighborhood, degree, common neighbors, the SRG predicate) and the complement closure theorem
- `paley.v` — Paley graphs over finite fields are SRG, plus self-complementarity for $q \cong 1 \mathrm{mod} 4$
- `hamming.v` — the Hamming graph H(2,q) is SRG with parameters $(q^2,~2(q−1),~q−2,~2)$
- `extract.v` — OCaml extraction of everything above
- `demo.v` — concrete adjacency matrices via extraction (see Demo below)
- `main.ml` — OCaml CLI that computes and prints adjacency matrices

## Dependencies

- Rocq 9.1
- MathComp 2.5 (ssreflect, fingroup, algebra, field)
- coq-graph-theory 0.9.7

See `srg-deps.opam` for the full list. Install with:

```
opam install . --deps-only
```

## Building

On macOS/Linux (where `make` is available):

```
rocq makefile -f _CoqProject -o Makefile
make
```

On Windows, or without `make`:

```
opam exec -- rocq c -R . SRG main.v
opam exec -- rocq c -R . SRG paley.v
opam exec -- rocq c -R . SRG hamming.v
```

## Demo

Extract OCaml code and build the CLI:

```
opam exec -- rocq c -R . SRG extract.v
opam exec -- rocq c -R . SRG demo.v
opam exec -- ocamlfind ocamlopt -c srg.mli
opam exec -- ocamlfind ocamlopt -c srg.ml
opam exec -- ocamlfind ocamlopt -c demo_srg.mli
opam exec -- ocamlfind ocamlopt -c demo_srg.ml
opam exec -- ocamlfind ocamlopt -c main.ml
opam exec -- ocamlfind ocamlopt -o demo srg.cmx demo_srg.cmx main.cmx
```

Then produce adjacency matrices:

```
./demo hamming 4     # H(2,4):  16 x 16
./demo hamming 42    # H(2,42): 1764 x 1764
./demo paley  13     # Paley(13): 13 x 13
./demo paley  17     # Paley(17): 17 x 17
```

The output is a 0/1 matrix (one row per line). Both graph families use the formally verified adjacency tests extracted from `hamming.v` and `paley.v`.

## Authors

Ejean Kuo, Jonathan Lee

Advised by Prof. Dmitrii Pasechnik, Northwestern University.
