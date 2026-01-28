SCRIPT = main.py
PYTHON = python3

LATEX = pdflatex
LATEX_FLAGS = -interaction=nonstopmode -halt-on-error


.PHONY: run clean wipe help


run:
	@echo "--- Running IK Prover ---"
	$(PYTHON) $(SCRIPT)


clean:
	@echo "--- Cleaning auxiliary files ---"
	rm -f *.aux *.log *.out *.toc


wipe:
	@echo "--- WIPING all generated files ---"
	rm -f *.aux *.log *.out *.toc *.tex *.pdf


help:
	@echo "make run   - run prover"
	@echo "make clean - remove auxiliary LaTeX files"
	@echo "make wipe  - remove ALL generated files (Be careful!)"