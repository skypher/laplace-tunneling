# Referee report

Review date: 2026-08-26.

Manuscript: *Algebraic tunnelling for the restricted fractional Laplacian on
distant domains*.

Version reviewed: commit `ac7b745c0d918294d152abbad5b7a042c8832567`.

## Recommendation

Pre-recommendation double-check: I recomputed the analytic constants and
orders, matched the external inputs to their primary sources, replayed the
numerics and release build, and inspected the rendered manuscript.

Accept in its present form.

The paper gives an explicit two-component splitting, an ordered
finite-component ground-state cluster governed by a weighted interaction
matrix, and a reproducible fixed-mesh illustration.  The operator reduction,
signs, leading coefficients, spectral-gap errors, Taylor errors, and limiting
scales are mutually consistent.  I found no major or minor mathematical
error, no missing hypothesis used by a caller, and no citation whose checked
statement differs from its use in the manuscript.

The recommendation follows the object-by-object checks below rather than the
repository's earlier audit declarations.  The last independent checks were:

1. recomputation of every cross-form coefficient, Hessian remainder, Schur
   constant, Young inequality, eigenvalue ordering, and scaled error exponent;
2. comparison of every external citation with the cited primary-source
   theorem, proposition, section, equation, page, or abstract;
3. exact reproduction of all numerical output, followed by a fresh archive
   build and a deterministic-archive hash comparison; and
4. inspection of the rendered 13-page manuscript and its final LaTeX log.

These checks support the recommendation above.

## Scope and general assessment

The principal contribution is a clean spectral perturbation argument for the
restricted fractional Laplacian on mutually distant copies of one bounded
domain.  The paper makes the nonlocal interaction explicit at the operator
level instead of treating it only through qualitative convergence.  The
leading interaction is algebraic, with exponent κ = d + 2s, and the
complementary one-well modes contribute only at quadratic order in the block
coupling.  For finitely many wells, the resulting matrix is the complete
weighted graph with entries

`−c_{d,s} m₁² |aᵢ−aⱼ|^(−κ)` for `i ≠ j`.

The manuscript is concise and logically ordered: exact operator reduction,
one-dimensional perturbation estimate, kernel expansion, two-well theorem,
degenerate-cluster estimate, finite-dimensional compression, multi-well
theorem, applications, and computation.  The numerical section is correctly
presented as a fixed-mesh check rather than as evidence used in the analytic
argument.

The novelty wording is appropriately bounded.  The checked nearby literature
contains qualitative distant-component convergence, the exact translated
cross-energy in a different shape-optimization setting, and a discrete
point-mass model, but the searches performed for this review did not locate an
earlier ordered two-well coefficient with the stated remainder or the full
finite-well spectral-cluster estimate.  The sentence “we are not aware” states
search evidence without converting it into a universal priority theorem.

## Review of each mathematical object

### Preliminary one-well construction

The form in (2.1) has the correct factor `c_{d,s}/2`; polarization therefore
produces an off-diagonal block with coefficient `−c_{d,s}`.  The space
`H̃ˢ(G)` is a closed form domain, and the cited Lipschitz extension and compact
embedding give compact resolvent for bounded `D`.  The cited positivity and
simplicity theorem applies at `p = 2`, including without a connectedness
assumption.  Reflection commutes with `A_D`; simplicity and positivity fix the
sign and give `φ₁(−x) = φ₁(x)`.  Thus `g > 0`, `m₁ > 0`, and the later symmetry
cancellation all have suppliers already present in Section 2.

Double-check: the primary-source statements are Di Nezza--Palatucci--Valdinoci
Theorems 5.4 and 7.1 and Brasco--Parini Theorem 2.8, specialized exactly as
above.  No unsupported preliminary spectral fact remains.

### Lemma 2.1: exact reflection reduction

The left coordinate is `x−Le/2` and the reflected right coordinate is
`−y+Le/2`; their displacement is `x+y−Le`.  Expanding the full-space
Gagliardo form over both orientations of the cross-region gives

`−2 c_{d,s} Re ∬ u(x) overline(v(y)) |Le−x−y|^(−κ) dx dy`.

This equals `2 Re ⟨u,B_Lv⟩` for the stated `B_L`.  The kernel is symmetric in
`x,y`, so `B_L` is self-adjoint.  Positive separation permits component
cutoffs, proving equality of the form domain with the direct sum.  A bounded
form perturbation then gives the operator block, and the standard symmetric
and antisymmetric unitary gives `(A_D+B_L) ⊕ (A_D−B_L)`.

Double-check: expanding the form with two test functions supported on
different components gives the displayed coefficient and no diagonal
correction.  Lemma 2.1 is correct as written.

### Lemma 3.1: ground-state perturbation bound

For `ψ = aφ+η`, `t = ||η||`, the gap supplies `μ+gt²`.  After subtracting
`μ+w`, the three perturbation contributions are bounded below by
`−bt²`, `−bt²`, and `−2bt`; hence the total lower comparison is
`(g−2b)t²−2bt`.  Its unrestricted minimum is `−b²/(g−2b)`, and
`b ≤ g/4` makes this at least `−2b²/g`.  Testing with `φ` gives the upper
bound zero.

Double-check: the normalization identity `|a|²+t²=1` accounts for the first
`−bt²`; omitting it would change the calculation, but it is included in the
manuscript's `−2bt²` term.  Lemma 3.1 is correct as written.

### Lemma 3.2: interaction-kernel expansion

For `F_L(z)=|Le−z|^(−κ)`, the segment condition gives distance at least
`L/2`.  The Hessian operator norm is bounded by
`κ(κ+3)|Le−z|^(−κ−2)`.  Taylor's factor `1/2`, the bound `|z|≤2R`, and the
distance estimate combine to

`2^(κ+3) κ(κ+3) R² L^(−κ−2)`.

The derivative at zero is `κL^(−κ−1)e`; because the two-well coordinate uses
`z=x+y`, evenness of `φ₁` makes its integral vanish.  Positivity converts the
pointwise remainder to the stated `m₁²` bound.  The Schur test gives
`||B_L|| ≤ c_{d,s}|D|(L−2R)^(−κ) ≤ β_L`.

Double-check: the Taylor sign, the use of `x+y` rather than `x−y`, the factor
`1/2`, and both powers of two were recomputed.  Lemma 3.2 and its explicit
constant are correct as written.

### Theorem 3.3: two-well algebraic splitting

The two branch compressions are `t_L=−c_{d,s}I_L<0` and `−t_L`.  Lemma 3.1
places each branch ground state within `2β_L²/g` of its compression.  Weyl's
bound leaves the second level of each branch above `μ₁+3g/4` and both branch
ground states below `μ₁+g/4`, so the first two full eigenvalues are exactly
the branch ground states.

The second condition in (3.8) dominates the worst allowed difference of the
two perturbation errors and fixes their order.  Lemma 3.2 then gives (3.6) and
(3.7).  After subtracting, multiplication by `L^κ` leaves errors
`O(L^(−2))` and `O(L^(−κ))`, both tending to zero.

Double-check: the lower bound
`I_L ≥ m₁²(L+2R)^(−κ)` supplies the strict ordering, and the leading gap is
`2c_{d,s}m₁²L^(−κ)`.  Theorem 3.3 is correct as written.

### Corollary 3.4: distant-ball minimizing sequence

For total volume `2|B_R|`, the comparison ball in the nonlocal
Hong--Krahn--Szegő statement has volume `|B_R|`.  Substitution of
`D=B_R(0)` into the upper doublet formula gives exactly the displayed limit.

Double-check: Brasco--Parini Theorem 6.2 states the strict inequality and the
sharp sequence of two radius-`R` balls at diverging mutual distance.  The
volume convention and limiting eigenvalue match Corollary 3.4.

### Definition 4.1 and the block setup

`δ_a` guarantees disjointness, while `Σ_p(a)` is precisely the largest row
sum required by the later symmetric-matrix norm estimate.  Translation, not
reflection, produces the denominator
`|L(aᵢ−aⱼ)+x−y|`.  The off-diagonal blocks satisfy
`B_{ji,L}=B_{ij,L}*`.

Double-check: swapping `i,j` and then `x,y` recovers the same real kernel, so
the block operator and the later compression are self-adjoint.

### Lemma 4.2: exact multi-well reduction and norm bound

The direct form expansion gives one cross term for each unordered pair and
no diagonal correction.  Under `Lδ_a ≥ 4R`, the distance is at least
`L|aᵢ−aⱼ|/2`.  The Schur test gives the displayed block norm.  For component
norms `r_j`, the estimate `||(V_Lu)_i|| ≤ Σ_j G_ij r_j` reduces the full
operator norm to the Euclidean norm of a symmetric nonnegative matrix `G`,
which is at most its largest row sum.

Double-check: the factor `2^κ`, the factor `|D|`, and the absence of an extra
factor `N` were recomputed from the row-sum estimate.  Lemma 4.2 is correct as
written.

### Lemma 4.3: isolated spectral-cluster bound

The upper inequality follows from the first `k` eigenvectors of `PWP`.  On
writing `ψ=p+q`, the gap, the `qWq` estimate, and the cross estimate give the
first line of (4.8).  Young's inequality

`2b||p||||q|| ≤ 2b²g^(−1)||p||² + (g/2)||q||²`

gives the comparison direct sum.  Its `P` block has largest eigenvalue at
most `μ+b−2b²/g`, while the complementary block begins at
`μ+g/2−b`; `b≤g/4` therefore places all first `N` comparison eigenvalues in
the `P` block.  Form ordering and min--max give the lower inequality.  The
`N+1` bound follows independently from `A+W≥A−bI`.

Double-check: 20,000 random finite-dimensional instances with ground-space
multiplicities one through five and `b≤g/4` produced no violation; this was a
diagnostic after the min--max derivation, not a replacement for it.  Lemma
4.3 is correct as written.

### Definition 4.4: effective interaction matrix

Compression onto the copied normalized ground states gives zero diagonal and
the exact entries (4.10).  Freezing the kernel at `Laᵢ−Laⱼ` yields precisely
`L^(−κ)M_a`, with the stated negative off-diagonal sign.

Double-check: the quadratic form of `M_a` counts each unordered pair twice,
matching the two oriented off-diagonal matrix entries and the cross-form
coefficient.

### Lemma 4.5: compression error

For `F(z)=|La+z|^(−κ)` and `z=x−y`, the same Hessian calculation gives the
entrywise error with the factor `|a|^(−κ−2)`.  Here the linear integral
cancels identically because

`∬ φ₁(x)φ₁(y)(x−y) dx dy = 0`.

This cancellation does not need an additional moment hypothesis.  The largest
absolute row sum then gives `ε_L` in Euclidean operator norm.

Double-check: the domain and codomain are the `N`-dimensional copied
ground-state space, and the matrix norm is the same norm used in Weyl's
ordered-eigenvalue estimate.  Lemma 4.5 is correct as written.

### Theorem 4.6: finite multi-well effective Hamiltonian

The direct sum has an `N`-fold eigenvalue `μ₁` and complementary spectrum at
least `μ₁+g`.  Lemma 4.3 compares the ordered full cluster with the ordered
eigenvalues of the exact compression, with error `2γ_L²/g`.  Lemma 4.5 and
the finite-dimensional min--max principle compare that compression with
`L^(−κ)M_a`, with error `ε_L`.  The triangle inequality gives (4.13), and the
same cluster lemma gives (4.14).  Scaling leaves `O(L^(−2))` and
`O(L^(−κ))`.

Double-check: both size assumptions in (4.12) supply the hypotheses of the
two invoked lemmas, and `κ=d+2s>0`.  Theorem 4.6 is correct as written.

### Corollary 4.7: recovery of the doublet

For centers `−e/2,e/2`, both row sums equal one, so `γ_L=β_L`; the effective
matrix has eigenvalues `±c_{d,s}m₁²`.  Reflection of the second local
coordinate changes the translated kernel from the `x−y` form to the `x+y`
form used in Section 3.  Symmetry of `D` and evenness of `φ₁` preserve the
integral.

Double-check: the exact compressions and the explicit remainder constants,
not only the leading limits, coincide.  Corollary 4.7 is correct as written.

### Corollary 4.8: collective ground state

The matrix has strictly negative entries on every off-diagonal position.  The
absolute-value Rayleigh argument gives a one-sign lowest eigenvector; the
eigenvalue equation excludes zero components.  A two-dimensional lowest
eigenspace would contain a nonzero vector with a zero component, so the
lowest eigenvalue is simple.  Its Rayleigh quotient on the all-ones vector is
negative.  Trace zero then forces the largest eigenvalue to be positive.

The theorem error `r_L` satisfies `L^κr_L→0`; comparison with the positive
effective spectral gap and the nonzero extreme eigenvalues gives simplicity
and the signs relative to `μ₁` for large `L`.

Double-check: the chosen threshold in the proof controls the factor two in
`λ₂−λ₁` and separately controls `λ₁−μ₁` and `λ_N−μ₁`.  Corollary 4.8 is
correct as written.

### Corollary 4.9: regular-simplex cluster

With equal pair distance `r`, the matrix is `−w(J−I)`.  The all-ones vector
has eigenvalue `−(N−1)w`, and its orthogonal complement has eigenvalue `w`.

Double-check: the multiplicities sum to `N` and the trace is zero, agreeing
with Definition 4.4.  Corollary 4.9 is correct as written.

### Proposition 5.1: exact cell-integral matrix

For two length-`h` cells at center distance `r≥h`, two integrations of
`|x−y|^(−1−2s)` give the second difference in (5.2), divided by
`2s(1−2s)`.  For one cell, integration against its full exterior gives
`2h^(1−2s)/(2s(1−2s))`.  Polarization supplies the negative off-diagonal
sign, and normalization of each indicator supplies the factor `1/h`.

Double-check: at adjacent cells `r=h`, the term `(r−h)^(1−2s)` is zero and
the integral remains finite exactly when `s<1/2`.  Proposition 5.1 is correct
as written.

### Corollary 5.2: fixed-mesh cluster asymptotic

Every off-diagonal one-well matrix entry is strictly negative, so the finite
matrix has a simple positive ground vector and a positive discrete gap.  On a
fixed mesh, the multi-block expansion is exact.  Its norm is
`O(L^(−1−2s))`; the compression Taylor error is `O(L^(−3−2s))`; and Lemma
4.3 contributes `O(L^(−2−4s))`.  The effective coefficient uses the exact
discrete mass `m_{1,h}`.

Double-check: the linear compression term cancels by the same `x−y`
identity as in Lemma 4.5, and all constants may depend on the fixed mesh,
configuration, and `s` as stated.  Corollary 5.2 is correct as written.

## Citation audit

The following primary-source statements were compared directly with their
uses:

- Di Nezza--Palatucci--Valdinoci, Theorems 5.4 and 7.1: Lipschitz extension
  and compact embedding;
- Brasco--Parini, Theorems 2.8 and 6.2: sign/simplicity and the strict, sharp
  nonlocal Hong--Krahn--Szegő statement;
- Parini--Salort, Theorems 1.1 and 1.2: compactness/dichotomy and its shape
  optimization consequence;
- Abatangelo--Felli--Noris, Introduction, p. 3: dependence on mutual
  component position;
- Zahl, Section 10, (10.3) and (10.7): translated cross-energy and the signed
  point-mass toy model;
- Wu, abstract: resolution of Zahl's no-local-minimum conjecture for the
  discrete model;
- Dipierro--Proietti Lippi--Sportelli--Valdinoci, Theorems 1.4--1.7: a
  distinct generalized eigenproblem with lower-order superposition;
- Kwaśnicki, Theorem 1 and Propositions 1--2: interval eigenvalue and
  eigenfunction estimates; and
- Zhang, Theorems 1--2: the newer interval eigenvalue expansion and a bound
  uniform in eigenfunction index and fractional order.

Double-check: author names, titles, dates, journal data, arXiv identifiers,
and DOI data in `references.bib` agree with the accessed records.  I found no
citation correction to request.

## Numerical and release audit

The independent run of `python3 -u tools/check_asymptotics.py` reproduced
every saved numerical line exactly except for elapsed time.  This includes
the three mesh rows, both effective spectra, and all fourteen separation
rows.  The constant-function identity passed before the eigensolves.

`make audit` reports:

```text
release audit passed: citations=9 labels=50 results=14 numerical_rows=11 pages=13
```

The source archive was extracted into a fresh directory.  `make audit`
rebuilt the 13-page PDF with no final warning matched by the release audit.
Running `make arxiv` in that directory produced the same archive hash as the
repository artifact:

```text
2ff605919e8abea8e8637c52f888042f74bb78ba723e32de76192fa32b52a004
```

Rendered-page inspection found no clipping, collision, unreadable table,
broken running head, or malformed bibliography entry.  The PDF metadata,
author information, code link, AI-use disclosure, and source archive are
present and internally consistent.

Double-check: the public code URL returned HTTP 200 and the remote `main`
reference matched the reviewed commit before this report was added.  The
computational and release claims are supported by the checked artifacts.

## Paper-level conclusion

The three advertised parts are all supplied in the manuscript:

1. Theorem 3.3 gives the signed two-well coefficient and a quantified
   remainder.
2. Theorem 4.6 gives every ordered eigenvalue in the finite ground-state
   cluster and separates that cluster from the rest of the spectrum.
3. Corollary 3.4, the source-specific introduction, Proposition 5.1,
   Corollary 5.2, and the saved computation supply the stated application,
   comparison, and reproducibility components.

Final double-check: each conclusion above was traced to its immediate lemma,
each lemma's constants and hypotheses were recomputed, all invoked external
statements were checked in context, and the executable artifacts were replayed.
No required revision remains; acceptance in the present form is recommended.
