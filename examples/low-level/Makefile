# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) $(FSTAR_DEFAULT_ARGS) # from the included Makefile

KREMLIN_HOME=../../../kremlin
KREMLIN=$(KREMLIN_HOME)/Kremlin.native
KREMLIN_ARGS=-tmpdir kremlin -verbose --lax

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info

CHACHA_ODIR=chacha
POLY_ODIR=poly
AEAD_ODIR=aead

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26

REALIZED_MLI=
REALIZED=Low_Bytes
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , FStar.Buffer SInt $(REALIZED_MODULE))

CHACHA_EXTRACTED=Buffer_Utils.ml Crypto_Symmetric_Chacha20.ml
POLY_EXTRACTED=FStar_List_Tot.ml FStar_Ghost.ml FStar_Seq.ml FStar_SeqProperties.ml Buffer_Utils.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305.ml
AEAD_EXTRACTED= FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml Buffer_Utils.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Chacha20.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_BlockCipher.ml FStar_Ghost.ml Plain.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305.ml FStar_HST_Monotonic_RRef.ml Crypto_Symmetric_Poly1305_MAC.ml Crypto_AEAD_Chacha20Poly1305.ml
CHACHA_AEAD_EXTRACTED= FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml Buffer_Utils.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Chacha20.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_BlockCipher.ml FStar_Ghost.ml Plain.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305.ml FStar_HST_Monotonic_RRef.ml Crypto_Symmetric_Poly1305_MAC.ml Crypto_Symmetric_Chacha20_PRF.ml Crypto_AEAD_Chacha20Poly1305_Ideal.ml

.PHONY: lib-ver chacha-ver chacha-ml ulib

#16-09-18 lib-ver works but is too slow/brittle? 
all: uall sall

uall:
	+make clean
	+make chacha-test poly-test aead-test aes-test aesgcm-test chacha-aead-test
	+make -C crypto all-lax all-ver

sall:

ulib: $(FSTAR_HOME)/ulib/ml/fstarlib.cmxa

$(FSTAR_HOME)/ulib/ml/fstarlib.cmxa:
	make -j 1 -C $(FSTAR_HOME)/ulib/ml clean all

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) FStar.HyperStack.fst FStar.HST.fst FStar.Buffer.fst

# AES targets
chacha-ver:
	$(FSTAR) Chacha.fst 

chacha-extract: ulib
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Crypto.Symmetric.Chacha20.fst --odir $(CHACHA_ODIR) 

chacha-compile: chacha-extract
	$(OCAMLOPT) -I crypto/ml -I $(CHACHA_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) crypto/ml/test_chacha.ml -o test_chacha.exe

chacha-test: chacha-compile
	./test_chacha.exe

poly-extract: ulib
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Crypto.Symmetric.Poly1305.fst --odir $(POLY_ODIR) #2> /dev/null
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(POLY_ODIR)/Crypto_Symmetric_Poly1305.ml

poly-compile: poly-extract
	$(OCAMLOPT) -I crypto/ml -I $(POLY_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) crypto/ml/test_poly.ml -o test_poly.exe

poly-test: poly-compile
	./test_poly.exe

ideal-extract: ulib
	mkdir -p $(AEAD_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Test.fst --odir $(AEAD_ODIR)
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(AEAD_ODIR)/Crypto_Symmetric_Poly1305.ml

ideal-compile: ideal-extract
	$(OCAMLOPT) -I crypto/ml -I $(AEAD_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(AEAD_ODIR)/,$(AEAD_EXTRACTED)) -o test_ideal.exe

ideal-test: ideal-compile
	./test_ideal.exe

aead-extract: ulib
	mkdir -p $(AEAD_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst --odir $(AEAD_ODIR) #2> /dev/null
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(AEAD_ODIR)/Crypto_Symmetric_Poly1305.ml

aead-compile: aead-extract
	$(OCAMLOPT) -I crypto/ml -I $(AEAD_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(AEAD_ODIR)/,$(AEAD_EXTRACTED)) crypto/ml/test_aead.ml -o test_aead.exe

aead-test: aead-compile
	./test_aead.exe

chacha-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst -skip-compilation

chacha-kremlin-test:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst $(addprefix $(KREMLIN_HOME)/test/, main-Chacha.c testlib.c) -o test_chacha.exe
	./test_chacha.exe

poly-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Poly1305.fst -skip-compilation

poly-kremlin-test:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Poly1305.fst $(addprefix $(KREMLIN_HOME)/test/, main-Poly1305.c testlib.c) -o test_poly.exe
	./test_poly.exe

aead-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst -skip-compilation

aead-kremlin-test:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst $(addprefix $(KREMLIN_HOME)/test/, main-Aead.c testlib.c) -o test_aead.exe
	./test_aead.exe

aes-ver:
	$(FSTAR) Crypto.Symmetric.AES.fst 

AES_ODIR=aes
AES_EXTRACTED=Crypto_Symmetric_AES.ml

aes-extract: ulib
	mkdir -p $(AES_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Crypto.Symmetric.AES.fst --odir $(AES_ODIR) 

aes-compile: aes-extract
	$(OCAMLOPT) -I crypto/ml -I $(AES_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED)) crypto/ml/test_aes256.ml -o test_aes256.exe

aes-test: aes-compile
	./test_aes256.exe


AESGCM_ODIR=aesgcm
AESGCM_EXTRACTED=Crypto_Symmetric_AES.ml Crypto_Symmetric_GF128.ml Crypto_Symmetric_GCM.ml Crypto_AEAD_AES256GCM.ml

aesgcm-extract: ulib
	mkdir -p $(AESGCM_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Crypto.AEAD.AES256GCM.fst --odir $(AESGCM_ODIR) 

aesgcm-compile: aesgcm-extract
	$(OCAMLOPT) -I crypto/ml -I $(AESGCM_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(AESGCM_ODIR)/,$(AESGCM_EXTRACTED)) crypto/ml/test_aes_gcm.ml -o test_aes_gcm.exe

aesgcm-test: aesgcm-compile
	./test_aes_gcm.exe


CHACHA_AEAD_ODIR=chacha_aead

chacha-aead-extract: ulib
	mkdir -p $(CHACHA_AEAD_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include $(FSTAR_HOME)/ulib/hyperheap --include crypto crypto/Test.fst --odir $(CHACHA_AEAD_ODIR)

chacha-aead-compile: chacha-aead-extract
	$(OCAMLOPT) -I crypto/ml -I $(CHACHA_AEAD_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_AEAD_ODIR)/,$(CHACHA_AEAD_EXTRACTED)) $(CHACHA_AEAD_ODIR)/Test.ml -o test_chacha_aead.exe

chacha-aead-test: chacha-aead-compile
	./test_chacha_aead.exe

bignum-ver:
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.fst --include crypto


# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix crypto/ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(AEAD_ODIR) $(AES_ODIR) $(AESGCM_ODIR) $(CHACHA_AEAD_ODIR) kremlin *~ *.exe ./crypto/*~
