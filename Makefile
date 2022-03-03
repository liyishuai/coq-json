COQMAKEFILE ?= Makefile.coq
MENHIR      ?= menhir
MENHIRFLAGS ?= --coq

ifneq ($(MAKECMDGOALS),clean)
	-include $(COQMAKEFILE)
endif

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

.PHONY: clean test
clean::
	@ rm -f `cat .gitignore`

Parser.v: Parser.vy
	$(MENHIR) $(MENHIRFLAGS) $<

test:
	$(MAKE) -C test

publish%:
	opam publish --packages-directory=released/packages \
		--repo=coq/opam-coq-archive --tag=v$* -v $* liyishuai/coq-json
