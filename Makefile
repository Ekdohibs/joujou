SHELL      := bash
TARGET     := Main.native
JOUJOU     := joujou
DIRS       := kremlin,alphalib
OCAMLBUILD :=\
  ocamlbuild \
    -classic-display \
    -j 4 \
    -use-ocamlfind \
    -use-menhir \
    -menhir "menhir -lg 1 -la 1 --explain" \
    -Is $(DIRS) \

.PHONY: all test clean

all:
	@ $(OCAMLBUILD) -quiet $(TARGET)
	@ ln -sf $(TARGET) $(JOUJOU)

test: all
	@ make -C test test

clean:
	rm -f *~
	rm -f tests/*.c tests/*.out
	$(OCAMLBUILD) -clean
	rm -f $(TARGET) $(JOUJOU)
	$(MAKE) -C test clean
