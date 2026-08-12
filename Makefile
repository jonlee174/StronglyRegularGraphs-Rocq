#   make         compile the proofs
#   make demo    extract to OCaml and build the ./demo CLI
#   make clean   remove all build artifacts

ROCQ      := opam exec -- rocq
OCAMLFIND := opam exec -- ocamlfind
VFILES    := main.v paley.v hamming.v

.PHONY: all clean install

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(ROCQ) makefile -f _CoqProject -o $@

srg.ml: extract.v $(VFILES) | all
	$(ROCQ) c -R . SRG extract.v

demo_srg.ml: demo.v $(VFILES) | all
	$(ROCQ) c -R . SRG demo.v

srg.cmx: srg.ml
	$(OCAMLFIND) ocamlopt -c srg.mli
	$(OCAMLFIND) ocamlopt -c srg.ml

demo_srg.cmx: demo_srg.ml
	$(OCAMLFIND) ocamlopt -c demo_srg.mli
	$(OCAMLFIND) ocamlopt -c demo_srg.ml

main.cmx: main.ml srg.cmx demo_srg.cmx
	$(OCAMLFIND) ocamlopt -c main.ml

demo: srg.cmx demo_srg.cmx main.cmx
	$(OCAMLFIND) ocamlopt -o $@ $^

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d .filestoinstall
	rm -f srg.ml srg.mli demo_srg.ml demo_srg.mli
	rm -f extract.vo* extract.glob .extract.aux demo.vo* demo.glob .demo.aux
	rm -f *.cmi *.cmx *.o demo
