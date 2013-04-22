outdir  = build
options = -file-line-error -halt-on-error

sources = report.tex inledning.tex metod.tex resultat.tex karatsuba-proof.tex \
		toomcook-nat.tex toomcook-coq.tex

target_tex = $(patsubst %,$(outdir)/%, $(sources))
target_pdf = $(patsubst %.tex,$(outdir)/%.pdf, $(sources))

all: $(outdir) $(target_tex) $(outdir)/report.bib $(outdir)/report.pdf

$(outdir)/%.pdf:
	cd $(outdir); \
		pdflatex $(options) report.tex; \
		bibtex report.aux; \
		pdflatex $(options) report.tex; \
		pdflatex $(options) report.tex

$(outdir)/%.tex: %.tex
	cp $< $@

$(outdir)/report.bib: report.bib
	cp report.bib $(outdir)/report.bib

$(outdir):
	mkdir -p $(outdir)

clean:
	$(RM) $(outdir)/*

.PHONY: clean all
