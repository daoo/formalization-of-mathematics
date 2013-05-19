options = -file-line-error -halt-on-error

all: build

build:
	mkdir -p build
	TEXINPUTS=.:src: latexmk -outdir=build -bibtex -pdf report.tex

run: dropbox

dropbox:
	cp build/report.pdf $(HOME)/dropbox/public/report.pdf

www:
	cp build/report.pdf $(HOME)/www/report.pdf

clean:
	rm build/*.*

.PHONY: clean build dropbox www
