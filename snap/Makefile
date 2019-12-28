# -*- Makefile -*-

# --------------------------------------------------------------------
export PATH      := ${PWD}/scripts:${PATH}
export BIBINPUTS := .:${BIBINPUTS}
export TEXINPUTS := ${PWD}/images:${TEXINPUTS}

# --------------------------------------------------------------------
MAIN    := main
CUTAT   := 14
LATEXMK := latexmk -bibtex -output-directory=_build
LATEXMK += -pdflatex="pdflatex -synctex=1 -file-line-error"
EXTRAMK ?=
LINKS   := log synctex.gz
MAIN    := main

ifneq (${DRAFT},)
KO      := -
LATEXMK += -e '$$max_repeat = 5' -interaction=nonstopmode
endif

LATEXMK += $(EXTRAMK)

# --------------------------------------------------------------------
.PHONY: all links force scratch clean purge cut __force__

define latex
	$(LATEXMK) -pdf $* $(MAIN); err=$$?; \
	[ -f _build/$(MAIN).pdf ] && cp _build/$(MAIN).pdf $(MAIN).pdf; \
	exit $$err
endef

all: prepare __force__
	$(KO)$(call latex)

force: prepare __force__
	$(KO)$(call latex,-g)

prepare: __force__
	for i in $(LINKS); do ln -sf _build/$(MAIN).$$i .; done
	rm -f _build/$(MAIN).pdf

scratch: purge all
	@true

clean:
	rm -rf _build/ $(LINKS:%=$(MAIN).%)

purge: clean
	rm -f $(MAIN).pdf

cut: all
	pdftk $(MAIN).pdf cat 1-$(CUTAT) \
	  output $(MAIN)-core.pdf
	pdftk $(MAIN).pdf cat $$(($(CUTAT) + 1))-end \
	  output $(MAIN)-appendix.pdf
