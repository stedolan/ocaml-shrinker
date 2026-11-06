.PHONY: run

run: shrink
	./shrink testcase.ml

shrink: shrink.ml
	ocamlopt -w +A-40-41-42-70-4 -I +compiler-libs ocamlcommon.cmxa $^ -o $@

