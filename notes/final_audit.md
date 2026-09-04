# Final theorem and release audit

Audit date: 2026-09-04.

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
- Lemma 3.2 computes the Hessian exactly: its radial eigenvalue is
  `kappa (kappa+1) |Le-z|^(-kappa-2)` and every transverse eigenvalue is
  `-kappa |Le-z|^(-kappa-2)`.  Evenness of the ground state removes the
  linear Taylor term in the reflected coordinates.
- Theorem 3.3 gives an explicit `L_0`.  Its second term yields
  `beta_L <= g/4`, while its third term and `L+2R <= 3L/2` yield the strict
  branch-ordering inequality.
- The branch comparison separates both ground states from both branch second
  eigenvalues.  The theorem therefore states that `lambda_1` and `lambda_2`
  are simple, `lambda_3 >= mu_1+3g/4`, and
  `lambda_3-lambda_2 >= g/2`.
- Multiplication by `L^kappa` leaves errors of orders `L^(-2)` and
  `L^(-kappa)`, both tending to zero in the ordinary topology of the real
  numbers.

### Finite multi-well cluster

- Section 4 now restarts with an arbitrary bounded Lipschitz reference
  domain.  Its proof uses translations and the algebraic `x-y` moment
  cancellation, so central symmetry is not a hypothesis of Theorem 4.6.
  Corollary 4.7 states the resulting symmetry-free two-well asymptotic.
  Corollary 4.8 restores `D=-D` exactly where comparison with the reflected
  scalar branches uses it.  The abstract, introduction, repository summary,
  and Section 4's fixed-data statement now advertise exactly the proved
  geometry: identically oriented translates `D+La_j`, not independently
  rotated copies.
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
- Corollary 4.8 now states the common condition `L >= L_0`, verifies that it
  supplies the size hypotheses of Theorem 4.6, and displays the exact identity
  between `epsilon_L+2 gamma_L^2/g` and the right-hand side of each two-well
  bound.
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
- The Galerkin assembly constructs one local stiffness block and reuses it
  exactly on every translated component.  This removes cancellation caused
  by forming within-component distances from large translated coordinates;
  an exact block-equality check runs before any eigensolve.
- The saved corrected 180-cell run completed in 27.019 seconds.  Its
  constant-function form identity and translated-block check passed, and
  every number printed in Tables 1--2 agrees with the saved output after the
  displayed rounding.  At `L=3`, the two- and three-well norm bounds are
  respectively `0.10858` and `0.21716`, both below `g_h/4=0.22424`.
- A fresh unbuffered replay on 2026-09-04 with Python 3.12.3, NumPy 1.26.4,
  and SciPy 1.11.4 completed in 27.104 seconds and again matched every saved
  value after removing the machine-dependent elapsed-time line.

## Source-specific checks

| Manuscript use | Primary-source statement checked |
|---|---|
| Zero-exterior/completion form-domain identification | Djitte--Fall--Weth, Section 2, equation (2.1) |
| One-well extension and compactness | Di Nezza--Palatucci--Valdinoci, Theorems 5.4 and 7.1 |
| Positivity and simplicity | Brasco--Parini, Theorem 2.8, at `p=2` |
| Nonlocal Hong--Krahn--Szego sequence | Brasco--Parini, Theorem 6.2, at `p=2` |
| Mixed local/nonlocal Hong--Krahn--Szego sequence | Biagi--Dipierro--Valdinoci--Vecchi, Theorem 1.1 |
| Local plus nonlocal Hong--Krahn--Szego sequence, with a compactly supported kernel in the nonlocal term | Goel--Sreenadh, Theorem 1.4 |
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
16-page PDF with no unresolved citation, unresolved
reference, multiply-defined label, overfull box, or underfull box.  Visual
inspection of all 16 pages confirms that the abstract radius, cutoff estimate,
normalization, cluster-edge bounds, symmetry-free corollary, fixed-mesh
geometry, effective spectra, revised table labels, disclosure,
code-availability metadata, and linked DOI/arXiv references are legible.  The
revised abstract and the contribution, geometry-scope, and symmetry
clarifications are also legible.  Page 15 contains the fixed-mesh table,
disclosure, code information, and the first bibliography entry; the remaining
twelve entries fit legibly on page 16.  The title page lists Leslie P. Polzer,
Independent Researcher, and `polzer@fastmail.com`; the PDF Author field is
`Leslie P. Polzer`.  A
source-to-source and rendered-page comparison with the Virasoro reference
paper confirms the same two-sided article geometry, Latin Modern font set,
title stack, section and theorem typography, running-head convention,
caption treatment, link palette, and ruled-table presentation.  Page 15
contains the AI disclosure naming OpenAI GPT-5.6 Sol
(`gpt-5.6-sol`) and specifying its research uses.  The manuscript source and extracted
PDF text contain no prohibited product-name reference.

`python3 -u tools/audit_release.py` reports:

```text
release audit passed: citations=13 labels=55 results=15 numerical_rows=11 abstract_chars=1537 pages=16
```

Artifact hashes after the arXiv-readiness revision are:

```text
ef7e1090e0126e48ce6b223b7280c120b48ff4771b6d17345713ea0fcc84fb89  paper.pdf
29de10e7a2e6a04907d6f0e64da27a1d27c694bebeada44b604b21020ea9af20  dist/laplace-tunneling-arxiv.tar.gz
af38fe65daf22e5f08a1ea7df85937d2931162b0e52a993f5419d74c826879e9  numerics/asymptotics_180.txt
```

The source archive passed `gzip -t`.  Its root contains only `paper.tex`,
`paper.bbl`, and `references.bib`; `anc/` contains its README, the numerical
script, pinned dependencies, and saved 180-cell output.  The manifest has seven
files and one directory, and every extracted payload byte-matched its
working-tree source.  The `make arxiv` prerequisite ran the release audit and
returned the result shown above.  The revised release is named
`paper-2026-09-04-r5` in the manuscript and README.  A second archive
generation byte-matched the release archive.

## Final double-check before closure

The last mathematical pass recomputed the signs and coefficients in the
two-well block, the multi-well row-sum constants, the two error exponents in
each scaled limit, and the exact cell integrals.  The last source pass matched
every cited theorem, proposition, section, page, and equation to the use made
in the manuscript.  The last release pass checked the generated bibliography,
all labels, every numbered result/proof pair, all displayed numerical rows,
the PDF diagnostics, and the archive manifest.  These checks meet all four
acceptance conditions in `ROADMAP.md`.
