DOC = efx

.PHONY: all clean

all: $(DOC).pdf

$(DOC).pdf: $(DOC).tex $(DOC).bib
	pdflatex -interaction=nonstopmode -halt-on-error $(DOC).tex
	biber $(DOC)
	pdflatex -interaction=nonstopmode -halt-on-error $(DOC).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(DOC).tex

clean:
	rm -f $(DOC).aux $(DOC).bbl $(DOC).bcf $(DOC).blg $(DOC).log \
	      $(DOC).out $(DOC).run.xml $(DOC).toc
