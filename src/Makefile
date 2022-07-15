OCAMLC := dune
OPTS := build
NAME := jasmine
EXEC_NAME := $(NAME).exe

preproc_files := parser.mly
opam_files := common.opam syntax.opam mir.opam lir.opam

.PHONY: all
all: $(EXEC_NAME)

%.mly: %.mly.m4
	m4 $< > $@

%.opam:
	touch $@

$(EXEC_NAME): $(preproc_files) $(opam_files)
	$(OCAMLC) $(OPTS) $(EXEC_NAME)

.PHONY: clean
clean:
	rm $(preproc_files)
	rm $(opam_files)
	rm -r _build
