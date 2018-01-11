BIN = test

test:
	ocamlbuild -use-ocamlfind $(BIN).native

debug:
	ocamlbuild -use-ocamlfind $(BIN).d.byte

clean:
	rm -f _build/* $(BIN).d.byte $(BIN).native
