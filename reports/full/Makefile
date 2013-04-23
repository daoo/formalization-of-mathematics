outdir  = build
options = -file-line-error -halt-on-error

sources = report.tex inledning.tex metod.tex resultat.tex karatsuba-proof.tex \
		toomcook-nat.tex toomcook-coq.tex

target_tex = $(patsubst %,$(outdir)/%, $(sources))
target_pdf = $(patsubst %.tex,$(outdir)/%.pdf, $(sources))

all: $(outdir)
	latexmk -outdir=$(outdir) -pdf report.tex

$(outdir):
	mkdir -p $(outdir)

clean:
	latexmk -outdir=$(outdir) -c

.PHONY: clean all
