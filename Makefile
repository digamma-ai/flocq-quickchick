LIBNAME := flocq-quickchick

.SUFFIXEC:

.PHONY: install

SRC = Generators.v
VO = Generators.vo
COQC = coqc
COQEXEC="coqtop" -q -w none -batch -load-vernac-source


all: flocqQuickChick

flocqQuickChick: $(SRC)
	$(COQEXEC) Extract.v

install: all
	cp 
