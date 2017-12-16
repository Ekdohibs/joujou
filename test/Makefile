OCAMLBUILD := ocamlbuild -use-ocamlfind -classic-display
TARGET     := test.native
TESTS      := ../tests

.PHONY: all test expected clean

all:
	@ $(OCAMLBUILD) $(TARGET)

test: all
	@ $(MAKE) -C ..
	@ ./$(TARGET) --verbosity 1

expected: all
	@ $(MAKE) -C ..
	@ ./$(TARGET) --verbosity 1 --create-expected

clean:
	@ rm -f *~ *.native *.byte
	@ $(OCAMLBUILD) -clean
	@ rm -f $(TESTS)/*.c $(TESTS)/*.exe $(TESTS)/*.out $(TESTS)/*.err $(TESTS)/*~
