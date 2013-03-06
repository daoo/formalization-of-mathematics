outdir  = build
options = -file-line-error -halt-on-error -output-directory $(outdir)

sources = report.tex
pdfs    = $(patsubst %.tex,$(outdir)/%.pdf, $(sources))

all: $(pdfs)

$(outdir)/%.pdf: %.tex build
	pdflatex $(options) $<

$(outdir):
	mkdir -p $(outdir)

clean:
	$(RM) $(outdir)/*

.PHONY: clean all
