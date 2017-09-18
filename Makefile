SOURCES := lib.ml bijection.ml node.ml graph.ml homomorphism.ml cat.ml basis.ml model.ml shape.ml test.ml
RESULT := ExtentionBases
LIBINSTALL_FILES := $(RESULT).cma $(RESULT).cmxa $(RESULT).a $(SOURCES:.ml=.cmi) $(SOURCES:.ml=.cmx)

.DEFAULT_GOAL := all

test: ExtentionBases.cma test.ml
	$(OCAMLC) -o $@ $^

all: native-code-library test

clean::
	rm -f test

-include OCamlMakefile
