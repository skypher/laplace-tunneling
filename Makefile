.PHONY: pdf numerics audit arxiv

ARXIV_ARCHIVE := dist/laplace-tunneling-arxiv.tar.gz
ARXIV_MTIME := UTC 2026-09-04

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

arxiv: audit anc/README.txt
	mkdir -p dist
	staging_dir=$$(mktemp -d); \
		trap 'rm -rf "$$staging_dir"' EXIT; \
		install -m 0644 paper.tex paper.bbl references.bib "$$staging_dir"; \
		install -d -m 0755 "$$staging_dir/anc"; \
		install -m 0644 anc/README.txt "$$staging_dir/anc/README.txt"; \
		install -m 0644 tools/check_asymptotics.py \
			"$$staging_dir/anc/check_asymptotics.py"; \
		install -m 0644 requirements-numerics.txt \
			"$$staging_dir/anc/requirements-numerics.txt"; \
		install -m 0644 numerics/asymptotics_180.txt \
			"$$staging_dir/anc/asymptotics_180.txt"; \
		tar --sort=name --mtime='$(ARXIV_MTIME)' --owner=0 --group=0 \
			--numeric-owner -C "$$staging_dir" -czf "$(CURDIR)/$(ARXIV_ARCHIVE)" \
			paper.tex paper.bbl references.bib anc
