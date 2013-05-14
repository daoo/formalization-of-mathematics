options = -file-line-error -halt-on-error

all:
	mkdir -p build
	TEXINPUTS=.:src: latexmk -outdir=build -bibtex -pdf report.tex

run: all
	cp build/report.pdf $(HOME)/dropbox/public/report.pdf

clean:
	rm build/*.*

.PHONY: clean all
