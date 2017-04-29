.PHONY: all

.DEFAULT_GOAL := all

export

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

all: Makefile.coq
	make -f Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq
