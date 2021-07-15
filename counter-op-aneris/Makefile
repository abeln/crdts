
all: ccddb

# Compile Interfaces:
%.cmi: %.mli
	ocamlc $<

# Compile programs
ccddb: ccddb.ml
	ocamlc   -thread unix.cma threads.cma  -o $@ ccddb.ml
	ocamlopt -thread unix.cmxa threads.cmxa -o $@ ccddb.ml

clean:
	rm *.cmx *.o *.cmi *.out *.log *.cmo ccddb
