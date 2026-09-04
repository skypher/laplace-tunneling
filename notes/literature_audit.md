# Literature audit for distant-component spectral splitting

Audit date: 2026-09-03.

## Scope and search routes

The search target was an asymptotic formula, with an explicit leading
coefficient or finite-dimensional effective matrix, for eigenvalues of the
restricted fractional Laplacian on translated components whose mutual
distance tends to infinity.

The following routes were checked:

1. arXiv API title/abstract searches combining `fractional Laplacian`,
   `restricted fractional Laplacian`, `disconnected`, `distant`, `mutual
   distance`, `two balls`, `eigenvalue splitting`, and `eigenvalue
   asymptotics`;
2. targeted web searches for the same phrases and for `effective interaction
   matrix` and `effective Hamiltonian`;
3. the 166 works indexed by OpenAlex as citing Brasco--Parini's paper on the
   second fractional eigenvalue, with title and abstract filtering for
   distance, disconnectedness, splitting, interaction, spectral asymptotics,
   and shape optimization; and
4. reference and forward-context checks around the closest primary sources
   listed below.

A final exact-terminology web sweep on 2026-08-26 combined `restricted
fractional Laplacian`, `distant`, `eigenvalue splitting`, `effective
interaction matrix`, and `double well`.  Its apparent matches used “double
well” for nonlinear Allen--Cahn potentials rather than for the spectrum of a
restricted operator on translated components.

A follow-up source check on 2026-09-01 added the mixed local/nonlocal
Hong--Krahn--Szeg\H{o} theorem of Biagi--Dipierro--Valdinoci--Vecchi as a
close qualitative analogue and the form-space identification of
Djitte--Fall--Weth as a direct source for the manuscript's zero-exterior
convention.

A referee follow-up on 2026-09-03 identified and checked the directly relevant
paper of L\'eculier--Roquejoffre.  Its Theorem 1 treats the principal
eigenvalue of two one-dimensional patches as their separation varies.  The
manuscript now cites that result and distinguishes it from the ordered
large-separation doublet and finite-well cluster proved here.  The same
follow-up checked Wu's Introduction, which identifies its no-local-minimum
result as the resolution of Zahl's Conjecture 10.9.

A second referee follow-up on 2026-09-03 added the Hong--Krahn--Szeg\H{o}
analogue of Goel--Sreenadh.  Their Theorem 1.4 gives the strict bound and the
sharp distant-equal-ball sequence for a local $p$-Laplacian coupled to a
nonlocal $p$-Laplacian whose kernel is compactly supported.  The manuscript
now records this close comparison and distinguishes its finite-range kernel
from the algebraic long-range kernel studied here.

No search result supplied the fixed-domain eigenvalue asymptotics proved in
Theorems 3.3 and 4.6.  This is search evidence, not a theorem that no such
paper exists; the manuscript therefore uses the bounded phrase “we are not
aware of an earlier result.”

## Closest primary sources

### Brasco--Parini (2016)

- Theorem 2.8 gives positivity and simplicity of the first eigenvalue,
  including disconnected bounded domains.
- Theorem 6.2 proves the strict nonlocal Hong--Krahn--Szegő inequality and
  qualitative convergence of the second eigenvalue for two equal balls whose
  center distance tends to infinity.
- The sharpness proof bounds a cross term by its decay with separation.  It
  does not extract the first coefficient, provide a two-sided remainder, or
  identify a multi-component cluster.

Primary source: arXiv:1409.6284; DOI 10.1515/acv-2015-0007.

### Biagi--Dipierro--Valdinoci--Vecchi (2023)

- Theorem 1.1 proves the strict Hong--Krahn--Szeg\H{o} inequality and the
  distant-equal-ball limiting sequence for the mixed operator
  `-Delta_p + (-Delta)^s_p`.
- This extends the qualitative shape-optimization picture to a mixed
  local/nonlocal operator.  It does not extract a separation-scale
  coefficient or a finite-dimensional interaction matrix for the ordinary
  restricted fractional Laplacian.

Primary source: arXiv:2110.07129; DOI 10.3934/mine.2023014.

### Goel--Sreenadh (2019)

- Theorem 1.4 proves the strict Hong--Krahn--Szeg\H{o} lower bound for the
  second eigenvalue and sharpness along two equal balls whose mutual distance
  tends to infinity.
- The operator is the sum of a local $p$-Laplacian and a nonlocal
  $p$-Laplacian with a radially symmetric, nonnegative, continuous,
  compactly supported kernel.  Consequently this model has no algebraic
  interaction beyond the kernel range and does not supply the coefficient or
  effective matrix studied in the manuscript.

Primary source: arXiv:1901.03444; DOI 10.1090/proc/14542.

### Parini--Salort (2020)

- Theorem 1.1 gives the compactness/vanishing/dichotomy trichotomy for bounded
  fractional Sobolev sequences.
- Theorem 1.2 gives the quasi-open-set compactness/dichotomy alternative and
  operator-norm resolvent approximation by two pieces at diverging distance.
- Theorem 1.3 applies the dichotomy to shape functionals.  The manuscript
  cites Theorems 1.1 and 1.2 for the first two statements.
- These results are qualitative with respect to the separation scale and do
  not give an interaction coefficient or effective matrix.

Primary source: arXiv:1806.01165; DOI 10.1002/mana.201800234.

### L\'eculier--Roquejoffre (2023)

- Theorem 1 proves that the principal eigenvalue for a union of two
  one-dimensional patches is increasing and continuous as their separation
  varies, including continuity when the patches meet.
- The theorem concerns the principal eigenvalue over the full range of
  separations.  It does not give the leading large-separation coefficient,
  the second member of the doublet, a two-sided remainder, or a finite-well
  effective matrix.

Primary source: arXiv:2004.14771; DOI 10.1007/s00526-022-02374-6.

### Abatangelo--Felli--Noris (2020)

- The Introduction, p. 3, explicitly notes that the spectrum on a
  disconnected domain depends on the mutual position of its components and
  points to Brasco--Parini, Section 2.3.
- The paper's asymptotic problem is removal of sets of small fractional
  capacity (Theorems 1.2 and following), rather than large translation of
  fixed components.

Primary source: arXiv:1902.03550; DOI 10.1142/S0219199719500718.

### Zahl (2026)

- Section 10, equation (10.3), isolates the exact cross-energy between
  translated pieces of an eigenfunction in a shape-optimization problem.
- Equation (10.7) replaces the pieces by signed point masses and proposes the
  kernel `|x_i-x_j|^(-n-2s)` as a discrete toy energy.
- The paper does not prove that the low spectrum of fixed distant congruent
  domains is approximated by that discrete matrix, nor does it control the
  discarded one-well modes.

Primary source: arXiv:2504.09840; DOI 10.1007/s00526-026-03270-z.

### Dipierro--Proietti Lippi--Sportelli--Valdinoci (2026)

- Theorems 1.4--1.7 analyze disconnected domains for a different generalized
  eigenproblem: a positive superposition of fractional operators appears on
  the left and a lower-order superposition on the right.
- There is no large-separation eigenvalue expansion for the ordinary
  restricted fractional Laplacian.

Primary source: arXiv:2602.18035.

### Wu (2026)

- The Introduction studies equilibrium and stability of Zahl's discrete
  signed-mass toy model and identifies the no-local-minimum conclusion as the
  resolution of Zahl's Conjecture 10.9.
- The object is the discrete energy itself, not the spectrum of the
  restricted fractional operator on distant domains.

Primary source: DOI 10.1016/j.amc.2026.130195.

## Manuscript positioning supported by the audit

The source-supported distinction is:

- qualitative distant-component convergence was known;
- the exact cross-energy and its point-mass analogue were known in a related
  shape-optimization discussion; but
- no located source derives the ordered two-well coefficient with a
  quantified remainder or the finite-well effective matrix with an
  operator-norm control of the complementary modes.

## Background citation verification

- Djitte--Fall--Weth, Section 2, equation (2.1), identifies the completion of
  compactly supported smooth functions in the global fractional energy norm
  with the finite-energy functions that vanish outside a continuous-boundary
  domain.  This applies to the bounded Lipschitz domains used in the
  manuscript.
- Di Nezza--Palatucci--Valdinoci, Theorem 5.4, gives the fractional Sobolev
  extension property for Lipschitz sets with bounded boundary; Theorem 7.1
  gives the compact embedding used at `p=q=2`.
- Kwasnicki, Theorem 1, gives the interval eigenvalue asymptotic, while
  Propositions 1 and 2 contain the cited eigenfunction estimates.
- Zhang, Theorem 1, gives the sharper interval eigenvalue expansion and
  Theorem 2 gives an `L-infinity` eigenfunction bound uniform in the index and
  fractional order.  The checked version is arXiv:2608.23457v1, submitted
  2026-08-24.
