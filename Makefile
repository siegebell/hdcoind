
# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.



.PHONY: coq clean

include Makefile.coq

Makefile.coq: Makefile _CoqProject 
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean-all: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq


