# Literature audit for distant-component spectral splitting

Audit date: 2026-08-26.

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

### Parini--Salort (2020)

- Theorem 1.1 gives the compactness/dichotomy alternative and operator-norm
  resolvent approximation by two pieces at diverging distance.
- Theorem 1.2 applies the dichotomy to spectral shape functionals.
- These results are qualitative with respect to the separation scale and do
  not give an interaction coefficient or effective matrix.

Primary source: arXiv:1806.01165; DOI 10.1002/mana.201800234.

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

- The published abstract studies equilibrium and stability of Zahl's
  discrete signed-mass toy model and settles its no-local-minimum conjecture.
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

- Di Nezza--Palatucci--Valdinoci, Theorem 5.4, gives the fractional Sobolev
  extension property for Lipschitz sets with bounded boundary; Theorem 7.1
  gives the compact embedding used at `p=q=2`.
- Kwasnicki, Theorem 1, gives the interval eigenvalue asymptotic, while
  Propositions 1 and 2 contain the cited eigenfunction estimates.
- Zhang, Theorem 1, gives the sharper interval eigenvalue expansion and
  Theorem 2 gives an `L-infinity` eigenfunction bound uniform in the index and
  fractional order.  The checked version is arXiv:2608.23457v1, submitted
  2026-08-24.
