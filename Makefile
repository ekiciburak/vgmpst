PARAM = -use-menhir -I src
CMD   = ocamlbuild $(PARAM)

main = native 

native:
	$(CMD) main.ml main.native

clean:
	$(CMD) -clean
