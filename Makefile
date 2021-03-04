COQMODULE    := PromisingArch
COQDIRS      := lib promising axiomatic equiv lcertify
COQTHEORIES  := lib/sflib/*.v lib/hahn/*.v $(foreach dir, $(COQDIRS), src/$(dir)/*.v)

.PHONY: all theories clean

all: sflib hahn Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: sflib-quick hahn-quick Makefile.coq
	$(MAKE) -f Makefile.coq vio

sflib: lib/sflib
	$(MAKE) -C lib/sflib

sflib-quick: lib/sflib
	$(MAKE) -C lib/sflib quick

hahn: lib/hahn
	$(MAKE) -C lib/hahn

hahn-quick: lib/hahn
	$(MAKE) -C lib/hahn quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R lib/sflib sflib"; \
   echo "-R lib/hahn hahn"; \
   \
   echo $(foreach dir, $(COQDIRS), "-R src/$(dir) $(COQMODULE).$(dir)"); \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq Makefile.coq.conf
