options = -file-line-error -halt-on-error

all:
	mkdir -p build
	latexmk -outdir=build -bibtex -pdf report.tex

run: all
	cp build/report.pdf $(HOME)/dropbox/public/report.pdf

clean:
	latexmk -outdir=build -c

.PHONY: clean all
