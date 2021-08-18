include ../Makefile.common

# F* app base files (that should be checked/compiled before LIB_FILES and APP_FILES), e.g., Application.Predicates
# WITHOUT ".fst"! These are assumed to be in the same directory as this Makefile
APP_BASE_FILES=ACME.Data Application.Predicates

# F* app files (checked/compiled AFTER all other F* modules)
# WITHOUT ".fst"! These are assumed to be in the same directory as this Makefile
APP_FILES=ACME.Data.SerializationHelpers ACME.Data.SerializationLemmas ACME.Data.Predicates Application.Predicates Application.Predicates.Lemmas ACME.Client.HelperLemmas ACME.Client.HelperFunctions ACME.Client.ReceiveMessage ACME.Client.AskChallenge ACME.Client.ChallengeResponse ACME.Client.OrderCertificate ACME.Client.PollOrderEndpoint ACME.Client.RetrieveCertificate ACME.Client.SaveCertificate ACME.Client.SendCSR.Helper ACME.Client.SendCSR ACME.Client.TriggerChallenge ACME.Client.RequestNonce ACME.Client.GetNonce ACME.Client ACME.Server.HelperFunctions ACME.Server.ChallengeResponse ACME.Data.SerializationLemmas ACME.Server.ChallengeResponse ACME.Server.FinalizeOrder ACME.Server.NewNonce ACME.Server.NewOrder ACME.Server.ReceiveChallengeVerification ACME.Server.TriggerChallengeVerification ACME.Server.KeyRollover ACME.Server ACME.SecurityProperties ACME.Test.Init ACME.Test

# Convert the FILES lists to fst and cmx file lists
APP_BASE_FST_FILES=$(addsuffix .fst,$(APP_BASE_FILES))
APP_BASE_CMX_FILES=$(addprefix ocaml/,$(addsuffix .cmx, $(subst .,_,$(APP_BASE_FILES))))

APP_FST_FILES=$(addsuffix .fst,$(APP_FILES))
APP_CMX_FILES=$(addprefix ocaml/,$(addsuffix .cmx, $(subst .,_,$(APP_FILES))))

ALL_FST_FILES=$(LIB_BASE_FST_FILES) $(APP_BASE_FST_FILES) $(LIB_FST_FILES) $(APP_FST_FILES)
ALL_CMX_FILES=$(LIB_BASE_CMX_FILES) $(APP_BASE_CMX_FILES) $(LIB_CMX_FILES) $(APP_CMX_FILES)

extract: $(ALL_FST_FILES) $(ALL_CMX_FILES)

test: $(ALL_FST_FILES) $(ALL_CMX_FILES) ocaml/test.exe

ifeq ($(OS),Windows_NT)
  export OCAMLPATH := $(FSTAR_HOME)/bin;$(OCAMLPATH)
else
  export OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif

OCAMLOPT = ocamlfind opt -package fstarlib -linkpkg -g -I ocaml -w -8-20-26
OCAMLSHARED = ocamlfind opt -shared -package fstar-tactics-lib -g -I ocaml -w -8-20-26

ocaml/test.exe: $(ALL_CMX_FILES)
	$(OCAMLOPT) $^ -o $@
