# not yet editted
# supports : make byte/native(default)/clean/test/test1/test2 (each test moves files generated in it)

.PHONY: all
all: native

.PHONY: byte
byte:
	ocamlc str.cma sat_check.ml -o sat_check.exe

.PHONY: native
native:
	ocamlopt str.cmxa sat_check.ml -o sat_check.exe

.PHONY:clean
clean:
	rm -rf sat_check.exe sat_check.o sat_check.cmx sat_check.cmi sat_check.cmo result_input.txt result_output.txt result_maps.txt output*.txt input.txt ignored.txt temp_cnf.txt temp_out.txt


.PHONY:test
test:
	cp testdata1.txt rule.txt
	./sat_check.exe
