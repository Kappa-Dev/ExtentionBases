SOURCES := lib.ml bijection.ml node.ml graph.ml homomorphism.ml cat.ml basis.ml model.ml shape.ml
RESULT := ExtentionBases
LIBINSTALL_FILES := $(RESULT).cma $(RESULT).cmxa $(RESULT).a $(SOURCES:.ml=.cmi) $(SOURCES:.ml=.cmx)

.DEFAULT_GOAL := all

test: ExtentionBases.cma test.ml
	$(OCAMLC) -o $@ $^

test-debug: ExtentionBases.cma test.ml
	$(OCAMLC) -g -o $@ $^


all: native-code-library test

debug: debug-code test-debug

clean::
	rm -f test

-include OCamlMakefile
