# Final theorem and release audit

Audit date: 2026-09-03.

## Final-facing theorem checks

### Two-well splitting

- The singular-integral normalization is now explicit:
  `c_(d,s)=4^s s Gamma(d/2+s)/(pi^(d/2) Gamma(1-s))`.  Its `d=1`
  specialization agrees with the constant used in Section 5 and in the
  numerical script.
- The form norm is explicitly identified with the inherited fractional
  Sobolev norm, so the manuscript now states closedness of the form and the
  associated self-adjoint operator before using it.  Compactness of the
  cited form embedding is explicitly converted into compact resolvent.
- The unitary map identifies both the `L^2` space and the form domain with
  two copies of the one-well space.  The cutoff step now includes the direct
  fractional multiplier estimate: the near-diagonal integral is finite
  because `s<1`, and the far-field integral is finite because `s>0`.
  Positive separation makes the cross term bounded.
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
  Corollary 4.7 states the resulting symmetry-free two-well asymptotic.
  Corollary 4.8 restores `D=-D` exactly where comparison with the reflected
  scalar branches uses it.
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
- The upper cluster comparison gives
  `lambda_N <= mu_1+gamma_L`, while Lemma 4.3 gives
  `lambda_(N+1) >= mu_1+g-gamma_L`.  Their difference is therefore at least
  `g-2 gamma_L >= g/2` under the theorem's stated size condition.
- Corollaries 4.7--4.10 follow from the explicit finite matrix: the
  symmetry-free two-well specialization, the recovery of the reflected
  remainder, the sign and simplicity of the lowest effective eigenvector,
  and the regular-simplex spectrum were each checked directly.  The
  Gram-matrix argument in Corollary 4.10 also records the necessary bound
  `N <= d+1`.
- Corollary 4.9 now separates the two mechanisms: Brasco--Parini Theorem 2.8
  gives simplicity of the full-domain first eigenvalue for every admissible
  separation, while Theorem 4.6 gives the strict inequalities relative to
  `mu_1` for sufficiently large separation.

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
- A fresh unbuffered replay on 2026-09-03 with Python 3.12.3, NumPy 1.26.4,
  and SciPy 1.11.4 completed in 13.551 seconds and again matched every saved
  value after removing the machine-dependent elapsed-time line.

## Source-specific checks

| Manuscript use | Primary-source statement checked |
|---|---|
| Zero-exterior/completion form-domain identification | Djitte--Fall--Weth, Section 2, equation (2.1) |
| One-well extension and compactness | Di Nezza--Palatucci--Valdinoci, Theorems 5.4 and 7.1 |
| Positivity and simplicity | Brasco--Parini, Theorem 2.8, at `p=2` |
| Nonlocal Hong--Krahn--Szego sequence | Brasco--Parini, Theorem 6.2, at `p=2` |
| Mixed local/nonlocal Hong--Krahn--Szego sequence | Biagi--Dipierro--Valdinoci--Vecchi, Theorem 1.1 |
| Local plus compact-kernel nonlocal Hong--Krahn--Szego sequence | Goel--Sreenadh, Theorem 1.4 |
| Distant-component dichotomy | Parini--Salort, Theorems 1.1 and 1.2 |
| Principal eigenvalue versus separation for two one-dimensional patches | L\'eculier--Roquejoffre, Theorem 1 |
| Mutual-position observation | Abatangelo--Felli--Noris, Introduction, p. 3 |
| Exact translated cross-energy and point-mass toy | Zahl, Section 10, equations (10.3), (10.7), and Conjecture 10.9 |
| Disconnected-domain generalized superposition problem | Dipierro--Proietti Lippi--Sportelli--Valdinoci, Theorems 1.4--1.7 |
| No-local-minimum result for Zahl's discrete energy | Wu, Introduction |
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
15-page PDF with no unresolved citation, unresolved
reference, multiply-defined label, overfull box, or underfull box.  Visual
inspection of all 15 pages confirms that the abstract radius, cutoff estimate,
normalization, cluster-edge bounds, symmetry-free corollary, fixed-mesh
geometry, effective spectra, tables, disclosure, code-availability metadata,
and linked references are legible.  The introduction no longer breaks after
an isolated word, and all thirteen bibliography entries remain on the
final page.  The title
page lists Leslie P. Polzer, Independent Researcher, and
`polzer@fastmail.com`; the PDF Author field is `Leslie P. Polzer`.  A
source-to-source and rendered-page comparison with the Virasoro reference
paper confirms the same two-sided article geometry, Latin Modern font set,
title stack, section and theorem typography, running-head convention,
caption treatment, link palette, and ruled-table presentation.  Page 14
contains the AI-use disclosure naming OpenAI GPT-5.6 Sol
(`gpt-5.6-sol`) and specifying its research uses.  The manuscript source and extracted
PDF text contain no prohibited product-name reference.

`python3 -u tools/audit_release.py` reports:

```text
release audit passed: citations=13 labels=52 results=15 numerical_rows=11 pages=15
```

Artifact hashes after the referee-revision build are:

```text
8d6c2ce31f79ce51dbc57e2ea32bc741b30a54a1d2a6fc3fef47101531766fee  paper.pdf
d46ef1341025c0cbb8d95b8c6ccdad2b0b20b65212f323308bada46a824aa826  dist/laplace-tunneling-arxiv.tar.gz
6f2d9d3acfa7b7a6c659399ac06f0a30fcc6788c51582681ffeb59775a4facc3  numerics/asymptotics_180.txt
```

The source archive passed `gzip -t` and contains the manuscript, generated
bibliography, BibTeX database, README, Makefile, release and numerical audit
scripts, pinned dependencies, and saved 180-cell output.  Every extracted
payload byte-matched its working-tree source.  The `make arxiv` prerequisite
ran the release audit and returned the result shown above.  The revised
release is named `paper-2026-09-03-r2` in the manuscript and README.  A second
archive created from the same inputs byte-matched the release archive, and a
fresh extracted-source build passed the same 15-page audit.

## Final double-check before closure

The last mathematical pass recomputed the signs and coefficients in the
two-well block, the multi-well row-sum constants, the two error exponents in
each scaled limit, and the exact cell integrals.  The last source pass matched
every cited theorem, proposition, section, page, and equation to the use made
in the manuscript.  The last release pass checked the generated bibliography,
all labels, every numbered result/proof pair, all displayed numerical rows,
the PDF diagnostics, and the archive manifest.  These checks meet all four
acceptance conditions in `ROADMAP.md`.
