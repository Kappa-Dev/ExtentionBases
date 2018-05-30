BIN = test

test:
	ocamlbuild -use-ocamlfind $(BIN).native

debug:
	ocamlbuild -use-ocamlfind $(BIN).d.byte

profile:
	ocamlbuild -use-ocamlfind $(BIN).p.native

clean:
	rm -f _build/* $(BIN).d.byte $(BIN).native $(BIN).p.native
