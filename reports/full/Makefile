sources = report.tex src/**/*.tex

all: build/report.pdf

build/report.pdf: $(sources)
	mkdir -p build
	TEXINPUTS=.:src: latexmk -outdir=build -bibtex -pdf report.tex

run: ${HOME}/dropbox/public/report.pdf

www: ${HOME}/www/report.pdf

${HOME}/dropbox/public/report.pdf: build/report.pdf
	cp $< $@

${HOME}/www/report.pdf: build/report.pdf
	cp $< $@

clean:
	rm -rf build/*

countlabels:
	grep --no-file -R '\label' src | sed 's@^.*\\label{@@' | sed 's@}.*$\@@' | sort | uniq -c

.PHONY: clean
