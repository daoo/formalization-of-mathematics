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

chalmers:
	cp build/report.pdf /mnt/chalmers/report.pdf

clean:
	rm build/*.*

countlabels:
	grep --no-file -R '\label' src | sed 's@^.*\\label{@@' | sed 's@}.*$\@@' | sort | uniq -c

.PHONY: clean build dropbox www
