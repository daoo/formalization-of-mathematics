outdir  = build
options = -file-line-error -halt-on-error

all: $(outdir)/report.pdf

$(outdir)/report.pdf: $(outdir) $(outdir)/report.tex $(outdir)/report.bib
	cd $(outdir); \
		pdflatex $(options) report.tex; \
		bibtex report.aux; \
		pdflatex $(options) report.tex; \
		pdflatex $(options) report.tex

$(outdir)/report.tex: report.tex
	cp report.tex $(outdir)/report.tex

$(outdir)/report.bib: report.bib
	cp report.bib $(outdir)/report.bib

$(outdir):
	mkdir -p $(outdir)

clean:
	$(RM) $(outdir)/*

.PHONY: clean all
