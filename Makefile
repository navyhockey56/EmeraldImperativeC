rm -f *.cmi *.o *.cmx *.naitve *.byte
ocamlbuild -cflag -g -lflag -g main.byte
mv main.byte emeraldc
