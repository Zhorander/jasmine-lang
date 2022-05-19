OCAMLC := dune
OPTS := build
NAME := jasmine
EXEC_NAME := $(NAME).exe

preproc_files := parser.mly

.PHONY: all
all: $(EXEC_NAME)

%.mly : %.mly.m4
	m4 $< > $@

$(EXEC_NAME): $(preproc_files)
	$(OCAMLC) $(OPTS) $(EXEC_NAME)

.PHONY: clean
clean:
	rm $(preproc_files)
	rm -rf _build
