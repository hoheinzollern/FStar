VERFILES=Ex01a.fst \
Ex02a.fst \
Ex03a.fst \
Ex03b.fst \
Ex03c.fst \
Ex04a.fst \
Ex04b.fst \
Ex04c.fst \
Ex04e.fst \
Ex04f.fst \
Ex04g.fst \
Ex04h.fst \
Ex05a.fst \
Ex05b.fst \
Ex06a.fst \
Ex06b.fst \
Ex06c.fst \
Ex06d.fst \
Ex06e.fst \
Ex07a.fst \
Ex07b.fst \
Ex07c.fst \
Ex07d.fst \
Ex10a.fst \
Ex10b.fst \
Ex12a.Cap.fst \
Ex12b.RPC.fst \
Ex12d.Pad.fst \
Ex12e.Pad.fst \
Ex12f.TMAC.fst \
Ex12g.TMAC2.fst

VERFILES_HH=Ex11a.fst

FSTAR_HOME=../../../../
HINTS_ENABLED=--use_hints  # CH: seems like overkill to me
include ../Makefile.include

HYPERHEAP=$(FSTAR_HOME)/ulib/hyperheap

verify-%: __force__
	$(FSTAR) --include $(FSTAR_HOME)/ucontrib/Platform/fst --include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst $*

verify_hh-%: __force__
	$(FSTAR) --include $(HYPERHEAP) $*


all: uall sall Ex01a-ocaml

sall:

uall: $(VERFILES:%=verify-%) $(VERFILES_HH:%=verify_hh-%)


# Importing targets for simplified extraction to Ocaml

include $(FSTAR_HOME)/ulib/ml/Makefile.include

out:
	mkdir -p out

Ex01a-ocaml: out Ex01a.fst
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Ex01a.fst
	$(OCAMLOPT) out/Ex01a.ml -o Ex01a.exe
	-./Ex01a.exe
