

main: htlexer.mll htparser.mly
	ocamllex htlexer.mll
	ocamlyacc htparser.mly
	ocamlc -I ../datastructure/ -c htparser.mli
	ocamlc -I ../datastructure/ -c htlexer.ml
	ocamlc -I ../datastructure/ -c htparser.ml
	ocamlc -I ../datastructure/ -c parser-test.ml
	ocamlc -I ../datastructure/ -o parser-test darray.cmo hol_type.cmo term.cmo signature.cmo htlexer.cmo htparser.cmo parser-test.cmo

clean:
	rm -f htlexer.ml
	rm -f htparser.mli
	rm -f htparser.ml
	rm -f *.cm[iox]
	rm parser-test
