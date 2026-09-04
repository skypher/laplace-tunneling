.PHONY: pdf numerics audit arxiv

pdf: paper.pdf

paper.pdf: paper.tex references.bib
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	bibtex paper
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex

numerics:
	python3 -u tools/check_asymptotics.py

audit: paper.pdf
	python3 -u tools/audit_release.py

arxiv: audit
	mkdir -p dist
	tar --sort=name --mtime='UTC 2026-09-04' --owner=0 --group=0 --numeric-owner \
		-czf dist/laplace-tunneling-arxiv.tar.gz \
		paper.tex paper.bbl references.bib README.md Makefile \
		tools/audit_release.py tools/check_asymptotics.py \
		requirements-numerics.txt \
		numerics/asymptotics_180.txt
