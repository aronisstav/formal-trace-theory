.PHONY: coq
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< > $@

_CoqProject: Makefile update_coq_project
	@echo -n "Updating $@... "
	@find -name "*.v" -print > $@.tmp
	@cmp -s $@.tmp $@ > /dev/null || cp $@.tmp $@
	@rm $@.tmp
	@echo "ok"

.PHONY: update_coq_project
update_coq_project:

.PHONY: clean
clean: Makefile.coq _CoqProject
	$(MAKE) -f Makefile.coq clean
	rm -f $^
