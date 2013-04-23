outdir  = build
options = -file-line-error -halt-on-error

sources = report.tex inledning.tex metod.tex resultat.tex karatsuba-proof.tex \
		toomcook-nat.tex toomcook-coq.tex

target_tex = $(patsubst %,$(outdir)/%, $(sources))
target_pdf = $(patsubst %.tex,$(outdir)/%.pdf, $(sources))

all: $(outdir)
	latexmk -auxdir=$(outdir) report.tex

$(outdir):
	mkdir -p $(outdir)

clean:
	$(RM) $(outdir)/*

.PHONY: clean all
