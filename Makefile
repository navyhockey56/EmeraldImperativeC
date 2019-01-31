.PHONY = all,clean

all:
	rm -f *.naitve *.byte
	ocamlbuild -cflag -g -lflag -g main.byte
