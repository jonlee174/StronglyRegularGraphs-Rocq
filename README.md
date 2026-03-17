# Strongly Regular Graphs in Rocq

A small library formalizing strongly regular graphs (SRGs) in Rocq, built on MathComp and coq-graph-theory.

## What's here

- `main.v` — core definitions (neighborhood, degree, common neighbors, the SRG predicate) and the complement closure theorem
- `paley.v` — Paley graphs over finite fields are SRG, plus self-complementarity for $q \cong 1 mod 4$
- `hamming.v` — the Hamming graph H(2,q) is SRG with parameters $(q^2, 2(q−1), q−2, 2)$
- `extract.v` — OCaml extraction of everything above

## Dependencies

- Rocq 9.1
- MathComp 2.5 (ssreflect, fingroup, algebra, field)
- coq-graph-theory 0.9.7

See `srg-deps.opam` for the full list. Install with:

```
opam install . --deps-only
```

## Building

```
rocq makefile -f _CoqProject -o Makefile
make
```

## Authors

Ejean Kuo, Jonathan Lee

Advised by Prof. Dmitrii Pasechnik, Northwestern University.