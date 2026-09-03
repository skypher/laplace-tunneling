# Algebraic tunneling for the fractional Laplacian

This repository develops spectral asymptotics for the restricted fractional
Laplacian on distant components.  The manuscript quantifies the double-well
splitting and identifies the entire ground-state cluster for finitely many
congruent wells through an explicit effective interaction matrix.

The manuscript is `paper.tex`.  Build it with the tools available in this
workspace:

```sh
make pdf
```

Reproduce the interval tables with:

```sh
python3 -m pip install -r requirements-numerics.txt
make numerics
```

The reference output from the 180-cell run is
`numerics/asymptotics_180.txt`.
It was replayed with Python 3.12.3, NumPy 1.26.4, and SciPy 1.11.4.

Run the mechanical release checks with:

```sh
make audit
```

After a successful audit, create the deterministic arXiv source archive with:

```sh
make arxiv
```

The archive is written to `dist/laplace-tunneling-arxiv.tar.gz` and includes the
manuscript source, generated bibliography, release and numerical audit scripts,
pinned dependencies, and reference numerical output.

The version tag for the reviewed manuscript is
`paper-2026-09-03-r2`.

The project-specific target and progress criteria are recorded in
`AGENTS.md` and `ROADMAP.md`.
