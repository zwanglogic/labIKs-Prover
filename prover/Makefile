SCRIPT = main.py

PYTHON = python3

LATEX = pdflatex
LATEX_FLAGS = -interaction=nonstopmode -halt-on-error

TEX_SOURCES := $(wildcard *.tex)
PDF_OBJECTS := $(TEX_SOURCES:.tex=.pdf)

.PHONY: all pdf clean help

all: pdf


pdf: $(PDF_OBJECTS)
	@echo "--- All PDFs generated successfully! ---"


%.pdf: %.tex
	@echo "--- Compiling $< ---"
	$(LATEX) $(LATEX_FLAGS) $<


clean:
	@echo "--- Cleaning auxiliary files ---"
	rm -f *.aux *.log *.tex *.pdf *.out


help:
	@echo "make pdf    - compile all .tex to .pdf"
	@echo "make clean  - remove LaTeX auxiliary files(Be careful!)"