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
- coq-mathcomp-finmap 2.2.2 (see note below)

See `srg-deps.opam` for the full list. Install with:

```
opam install . --deps-only
```

`coq-graph-theory` 0.9.7 does not bound `coq-mathcomp-finmap`, so opam will
otherwise select finmap 2.2.4, which adds fset-comprehension lemmas to the
`inE` database and breaks graph-theory's own `edges_atE` rewrites in
`theories/core/open_confluence.v`. `srg-deps.opam` therefore constrains finmap
to `>= 2.2.2 & < 2.2.4`, the newest release compatible with both MathComp 2.5
and graph-theory 0.9.7. If you already have 2.2.4 installed, opam will
downgrade it as part of `--deps-only`.

## Building

```
make          # compile the proofs
make demo     # extract to OCaml and build the ./demo CLI
make clean    # remove all build artifacts
```

On Windows, `make` is available via [Chocolatey](https://chocolatey.org/).

## Demo

```
make demo
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
