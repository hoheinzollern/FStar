
include Makefile.include

CRYPTOLIB=$(FSTAR_HOME)/examples/crypto
FSTAR= ../../bin/fstar.exe


STDLIB_ADMITS=--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi FStar.SeqProperties --admit_fsi FStar.IO
STDLIB=$(addprefix $(FSTAR_HOME)/lib/, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi \
       FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.String.fst FStar.List.fst seq.fsi FStar.SeqProperties.fst)  FStar.IO.fsti \
       $(STDLIB_ADMITS)

outlineLeia: outlineLeia.fst
	$(FSTAR) --z3timeout 10 --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
	  $(STDLIB) \
	  $(FSTAR_HOME)/contrib/Platform/fst/Bytes.fst \
	  $(FSTAR_HOME)/contrib/CoreCrypto/fst/CoreCrypto.fst \
	  $(CRYPTOLIB)/sha1.fst $(CRYPTOLIB)/mac.fst outlineLeia.fst \
          --verify_module OutlineLeia \


problem: problem.fst
	$(FSTAR) --z3timeout 100 --verify_module Problem problem.fst
