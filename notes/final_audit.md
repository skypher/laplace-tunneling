# Final theorem and release audit

Audit date: 2026-09-01.

## Final-facing theorem checks

### Two-well splitting

- The form norm is explicitly identified with the inherited fractional
  Sobolev norm, so the manuscript now states closedness of the form and the
  associated self-adjoint operator before using it.  Compactness of the
  cited form embedding is explicitly converted into compact resolvent.
- The unitary map identifies both the `L^2` space and the form domain with
  two copies of the one-well space; positive separation makes the cross term
  bounded.
- Direct form expansion displays the cancellation
  `|u-v|^2-|u|^2-|v|^2=-2 Re(u conjugate(v))`, giving the negative
  off-diagonal kernel and no diagonal correction.
- Lemma 3.1 states the form domain for the Rayleigh vectors, displays the
  full `W`-term expansion, and bounds the isolated-eigenvalue error by
  `2 beta_L^2/g`.
- Lemma 3.2 uses the Hessian bound
  `kappa (kappa+3) |Le-z|^(-kappa-2)` and evenness of the ground state to
  remove the linear Taylor term.
- The ordering condition in (3.8) separates the two branch ground states
  from both branch second eigenvalues and fixes the signs in (3.6)--(3.7).
- Multiplication by `L^kappa` leaves errors of orders `L^(-2)` and
  `L^(-kappa)`, both tending to zero in the ordinary topology of the real
  numbers.

### Finite multi-well cluster

- Section 4 now restarts with an arbitrary bounded Lipschitz reference
  domain.  Its proof uses translations and the algebraic `x-y` moment
  cancellation, so central symmetry is not a hypothesis of Theorem 4.6.
  Corollary 4.7 restores `D=-D` exactly where comparison with the reflected
  two-well construction uses it.
- Lemma 4.2 identifies the direct-sum form domain and obtains the full block
  norm from the Schur bounds and the symmetric row-sum estimate.
- Lemma 4.3 was checked from the min--max principle on the ground-state
  subspace and its orthogonal complement.  The displayed inequality
  `eta_N-2b^2/g <= b-2b^2/g < g/2-b` places the entire compressed block
  below the complement when `b <= g/4`.
- Lemma 4.5 cancels the linear Taylor term exactly and bounds the matrix
  remainder in Euclidean operator norm by its largest absolute row sum.
- Theorem 4.6 combines the cluster error and compression error without
  changing their hypotheses.  After multiplication by `L^kappa`, the two
  errors are `O(L^(-2))` and `O(L^(-kappa))`.
- Corollaries 4.7--4.9 follow from the explicit finite matrix: the two-well
  specialization, the sign and simplicity of its lowest eigenvector, and
  the regular-simplex spectrum were each checked directly.  The Gram-matrix
  argument in Corollary 4.9 also records the necessary bound `N <= d+1`.

### Applications and fixed-mesh computation

- Corollary 3.4 specializes the upper member of the doublet to the distant
  equal-ball minimizing sequence and now states the volume convention
  `|Omega_L|=2|B_R|` explicitly.
- Proposition 5.1 evaluates every cell-pair integral and the zero-exterior
  diagonal integral exactly for `0 < s < 1/2`.
- Corollary 5.2 repeats the block, gap, and Taylor estimates in the fixed
  finite-dimensional Galerkin space and states its own remainder.
- The saved 180-cell run completed in 57.123 seconds.  Its constant-function
  form identity passed before any eigensolve, and every number printed in
  Tables 1--2 agrees with the saved output after the displayed rounding.
- A fresh unbuffered replay on 2026-09-01 with Python 3.12.3, NumPy 1.26.4,
  and SciPy 1.11.4 completed in 11.145 seconds and again matched every saved
  value after removing the machine-dependent elapsed-time line.

## Source-specific checks

| Manuscript use | Primary-source statement checked |
|---|---|
| Zero-exterior/completion form-domain identification | Djitte--Fall--Weth, Section 2, equation (2.1) |
| One-well extension and compactness | Di Nezza--Palatucci--Valdinoci, Theorems 5.4 and 7.1 |
| Positivity and simplicity | Brasco--Parini, Theorem 2.8, at `p=2` |
| Nonlocal Hong--Krahn--Szego sequence | Brasco--Parini, Theorem 6.2, at `p=2` |
| Mixed local/nonlocal Hong--Krahn--Szego sequence | Biagi--Dipierro--Valdinoci--Vecchi, Theorem 1.1 |
| Distant-component dichotomy | Parini--Salort, Theorems 1.1 and 1.2 |
| Mutual-position observation | Abatangelo--Felli--Noris, Introduction, p. 3 |
| Exact translated cross-energy and point-mass toy | Zahl, Section 10, equations (10.3) and (10.7) |
| Disconnected-domain generalized superposition problem | Dipierro--Proietti Lippi--Sportelli--Valdinoci, Theorems 1.4--1.7 |
| No-local-minimum result for Zahl's discrete energy | Wu, abstract |
| Interval eigenvalue and eigenfunction estimates | Kwasnicki, Theorem 1 and Propositions 1--2 |
| Sharper interval asymptotics and uniform eigenfunction bound | Zhang, Theorems 1 and 2 |

The priority search covered exact-phrase web searches, arXiv title/abstract
queries, the forward literature of Brasco--Parini indexed by OpenAlex, and
the closest primary sources listed in `notes/literature_audit.md`.  The final
exact-terminology sweep on 2026-08-26 returned only unrelated fractional
Allen--Cahn uses of “double well.”  The manuscript therefore uses the bounded
priority wording “we are not aware of an earlier result.”

## Release checks

The final `make audit` run checks the last LaTeX build, which produced a
14-page PDF with no unresolved citation, unresolved
reference, multiply-defined label, overfull box, or underfull box.  Visual
inspection of all 14 pages confirms that the abstract qualification, eigenvalue
convention, form-domain perturbation argument, related-work additions, expanded
corollary proofs, fixed-mesh geometry, effective spectra, tables, disclosure,
code-availability metadata, and linked references are legible.  The title
page lists Leslie P. Polzer, Independent Researcher, and
`polzer@fastmail.com`; the PDF Author field is `Leslie P. Polzer`.  A
source-to-source and rendered-page comparison with the Virasoro reference
paper confirms the same two-sided article geometry, Latin Modern font set,
title stack, section and theorem typography, running-head convention,
caption treatment, link palette, and ruled-table presentation.  Page 13
contains the AI-use disclosure naming OpenAI GPT-5.6 Sol
(`gpt-5.6-sol`) and specifying its research uses.  The manuscript source and extracted
PDF text contain no prohibited product-name reference.

`python3 -u tools/audit_release.py` reports:

```text
release audit passed: citations=11 labels=50 results=14 numerical_rows=11 pages=14
```

Artifact hashes after the referee-revision build are:

```text
4174303304a7ec6d1283dbc2de72af9a25dd627963f04ce0284d3cd68d2a631c  paper.pdf
e21dd479130531495791b6adb7fb665e9f871adc73d9bb016d418ef387c87589  dist/laplace-tunneling-arxiv.tar.gz
6f2d9d3acfa7b7a6c659399ac06f0a30fcc6788c51582681ffeb59775a4facc3  numerics/asymptotics_180.txt
```

The source archive passed `gzip -t` and contains the manuscript, generated
bibliography, BibTeX database, README, Makefile, release and numerical audit
scripts, pinned dependencies, and saved 180-cell output.  Every extracted
payload byte-matched its working-tree source.  The `make arxiv` prerequisite
ran the release audit and returned the result shown above.

## Final double-check before closure

The last mathematical pass recomputed the signs and coefficients in the
two-well block, the multi-well row-sum constants, the two error exponents in
each scaled limit, and the exact cell integrals.  The last source pass matched
every cited theorem, proposition, section, page, and equation to the use made
in the manuscript.  The last release pass checked the generated bibliography,
all labels, every numbered result/proof pair, all displayed numerical rows,
the PDF diagnostics, and the archive manifest.  These checks meet all four
acceptance conditions in `ROADMAP.md`.
