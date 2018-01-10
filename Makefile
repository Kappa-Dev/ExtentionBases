BIN = test

test:
	ocamlbuild -use-ocamlfind $(BIN).native

clean:
	rm -f _build/*
