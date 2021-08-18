.PHONY: extract_all verify_all all clean ocaml

export OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)

# Default: Re-check all F* code, extract all F* modules and build dune project
all: verify_all extract_all _build/default/main.exe doc

# Check all F* code
verify_all:
	@$(MAKE) -C fstar
	@$(MAKE) -C fstar/acme

# Make sure that all relevant F* modules are extracted
extract_all:
	@$(MAKE) -C fstar/acme extract

ocaml:
	dune build

doc:
	dune build @doc

_build/default/main.exe:
	dune build

clean:
	dune clean
	@$(MAKE) -C fstar clean
	@$(MAKE) -C fstar/acme clean
