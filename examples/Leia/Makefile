
include Makefile.include

CRYPTOLIB=$(FSTAR_HOME)/examples/crypto
FSTAR=mono ../../bin/fstar.exe

outlineLeia: outlineLeia.fst
	$(FSTAR) --z3timeout 10 --admit_fsi FStar.Seq --admit_fsi FStar.IO --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
	  --verify_module SHA1 --verify_module MAC --verify_module OutlineLeia \
          $(addprefix $(FSTAR_HOME)/lib/, ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst all.fst \
					string.fst list.fst \
					seq.fsi seqproperties.fst io.fsti ) \
	  $(FSTAR_HOME)/contrib/Platform/fst/Bytes.fst \
	  $(FSTAR_HOME)/contrib/CoreCrypto/fst/CoreCrypto.fst \
	  $(CRYPTOLIB)/sha1.fst $(CRYPTOLIB)/mac.fst outlineLeia.fst


problem: problem.fst
	$(FSTAR) --z3timeout 100 --verify_module Problem problem.fst
