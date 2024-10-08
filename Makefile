TEMPLATES ?= ../templates
TARGETS = .github/workflows/docker-action.yml coq-json.opam dune-project README.md

all:
	dune build

test: all
	dune test

meta:
	$(TEMPLATES)/generate.sh $(TARGETS)

publish%:
	opam publish --packages-directory=released/packages \
		--repo=coq/opam --tag=v$* -v $* liyishuai/coq-json

.PHONY: all test meta publish
