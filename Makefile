BIN = test

test:
	ocamlbuild -use-ocamlfind $(BIN).native

debug:
	ocamlbuild -use-ocamlfind $(BIN).d.byte

profile:
	OCAML_LANDMARKS=auto ocamlbuild -use-ocamlfind $(BIN).native


clean:
	rm -f _build/* $(BIN).d.byte $(BIN).native
