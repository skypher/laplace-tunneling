# Lean promotion ledger

## 2026-09-29 — spine reset: unconditional capstones on `ℝ^d` (receipt `euclid-spine-2026-09-29`)

Audit of the previous capstones (2026-09-29, main agent):
1. `FinalTheoremL2`: the one-well form integrated only over `X × X` with every
   point of `X` in the ball of radius `R` (`hX`), i.e. the regional form on `D`,
   not the paper's `eq:form` over `ℝ^d × ℝ^d`.  Its `lambda` were branch
   Rayleigh infima, not eigenvalues of `A_{Ω_L}`.  The lifted form
   (`restrictedZeroExteriorFormLift`) is extended to all of `L²` through an
   algebraic complement, so `hgapq` on all unit vectors is not satisfiable by
   the actual form.
2. `multiWellConclusion`: the cluster edges used indices `card ι` and
   `card ι + 1` (the `(N+1)`st and `(N+2)`nd eigenvalues) instead of
   `card ι - 1` and `card ι`; `hupper` was unsatisfiable for true
   eigenvalues.  Fixed in `MultiWell.lean`.
3. `sigmaKappa` was the double sum `Σ_i Σ_{j≠i}`, not the paper's maximal row
   sum `Σ_p(a) = max_i Σ_{j≠i}`.  Fixed in `MultiWell.lean` (`⨆ i`), with
   `row_le_sigmaKappa`; all dependent proofs recompile.

New spine (statements locked 2026-09-29; frozen copies and
`logs/skeleton/stmtcheck.py` detect statement drift):
- final-facing theorems: `Tunneling.multiWell_main` (paper Theorem 4.3) and
  `Tunneling.twoWell_main` / `twoWell_main_centrallySymmetric` (paper
  Theorem 3.3, including simplicity `λ₁ < λ₂ < λ₃`), in
  `Tunneling/Euclid/Main.lean`;
- eigenvalues: `eigenvalue c κ G k = MinMax.level (formQ c κ G) k`, the
  Courant--Fischer levels of the zero-exterior form `eq:form` on
  `H^s_0(G) ⊆ L²(ℝ^d)` (`Tunneling/Euclid/FormDomain.lean`);
- one-well data derived, not assumed: `μ₁, μ₂` are levels 0 and 1 of `Q_D`,
  `φ` is any `IsPositiveGroundState`, `m₁ = ∫ φ` (`oneWellConstants`);
- suppliers: `Spectral/MinMax`, `Spectral/Cluster` (Lemma 4.2),
  `Euclid/{FormDomain, Translate, Bump, CellAverage, Compactness, Sign,
  GroundState, Decomp, DecompForm, DecompBound, Compression, MainAux}`.
- acceptance check: full `lake build`, zero `sorry` in the Euclid/Spectral
  spine, `stmtcheck.py` clean, and `#print axioms` of the capstones listing
  only `propext`, `Classical.choice`, `Quot.sound`.
- credit on success: the two final-facing theorem slots (two-well,
  multi-well), unconditional.

Skeleton state at lock: 73 `sorry` in 15 files; full package builds (2993
jobs).  Assignments: one read-only `gpt-6-luna` (max effort) agent per file,
cards in `logs/agents/cards/`.


### Final acceptance — receipt `euclid-spine-2026-09-29` closed (18:45)

Acceptance check (`logs/skeleton/final_check.sh`): full `lake build` passes
(3035 jobs); no `declaration uses sorry` warning in any module; no `sorry`
token in any source except the word inside the `Statements.lean` docstring; no
`axiom` declaration; `stmtcheck.py` reports every locked statement unchanged;
`#print axioms` gives only `[propext, Classical.choice, Quot.sound]` for:
`multiWell_main` (Thm 4.3), `twoWell_main` and
`twoWell_main_centrallySymmetric` (Thm 3.3, with simplicity),
`multiWell_cluster` (eq:exact-cluster-comparison), `exists_positiveGroundState`,
`IsPositiveGroundState.unique`, `eigenvalue_zero_lt_one`,
`exists_orthonormal_eigenfunctions`, `eigenvalue_monotone_tendsto`,
`exists_eigenvalue_eq_of_weakEigenfunction`, `finrank_weakEigenspace`
(levels = weak eigenvalues of `A_G` with multiplicity), `distantBall_rate`
(Cor 3.4), `symmetryFree_twoWell` (Cor 4.4), `multiTwo_remainder` (Cor 4.6),
`collectiveGround_matrix` and `collectiveGround_spectrum` (Cor 4.7),
`simplex_cluster` (Cor 4.8), `cellVec_mem_formDomain`, `cellMatrix_diag`,
`cellMatrix_offdiag` (Prop 5.1), `fixedMesh_cluster` (Cor 5.2).

Scope notes: the theorems hold for every bounded open `D ⊆ B_R(0)` (the
paper's Lipschitz hypothesis and, for Thm 3.3, central symmetry are not
needed) and every `c > 0` (in particular `c_{d,s}`).  The strict positivity of
`φ₁` cited in paper Section 2 is not formalized and not used; the Lean
hypothesis `φ ≥ 0` a.e. identifies the same function by uniqueness.  Weakened
intermediate requirement (demand sheet): `MinMax.cluster_levels_bounds` drops
the `(N+1)`-dimensional hypothesis of `cluster_levels`, which only the
separation bound uses; Cor 5.2 needs only the bounds (one-cell case `n = 1`).
The earlier conditional capstones (`FinalTheorem`, `FinalTheoremL2`) are kept
and documented as superseded in `Final.lean`.

### Acceptance result — capstones (13:40)

`Tunneling.multiWell_main` (paper Theorem 4.3) and `Tunneling.twoWell_main`
/ `twoWell_main_centrallySymmetric` (paper Theorem 3.3 with simplicity
`λ₁ < λ₂ < λ₃`) are proved in `Tunneling/Euclid/Main.lean` with no `sorry`
anywhere in their dependency cone: `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for both capstones,
`multiWell_cluster` and `oneWellConstants`.  Full `lake build` passes (3031
jobs); `stmtcheck.py` reports the locked statements unchanged.  This earns both
final-facing theorem slots (two-well, multi-well), unconditional for every
bounded open `D ⊆ B_R(0)`, `d ≥ 1`, `0 < s < 1`, `c > 0` (the paper's Lipschitz
and, for Theorem 3.3, central-symmetry hypotheses are not needed).
Remaining (not in the capstones' cone): Spectrum (levels = weak eigenvalues
with multiplicity), Corollaries 3.4/4.4/4.6/4.7/4.8, FixedMesh (Cor 5.2).

### Progress under receipt `euclid-spine-2026-09-29` (13:15)

Accepted (compiled with `lake env lean`, no `sorry`, statements unchanged per
`stmtcheck.py`): Spectral/MinMax, Spectral/Cluster (paper Lemma 4.2),
Spectral/MatrixLevels, Spectral/PerronFrobenius, Euclid/FormDomain,
Euclid/Translate, Euclid/Bump, Euclid/CellAverage + Euclid/Compactness
(replace [DNPV12, Thms 5.4, 7.1]), Euclid/Sign, Euclid/GroundState (existence,
uniqueness, `μ₁ < μ₂`, gap inequality, `m₁ > 0`; replaces [BP16, Thm 2.8] as
used), Euclid/Decomp + DecompForm + DecompBound (paper Lemma 4.1),
Euclid/Compression (Lemma 4.3), Euclid/MainAux, Euclid/CellMatrix
(Proposition 5.1).  Full `lake build` passes (3031 jobs).

Open (proofs in progress; statements locked): Euclid/Main (3: the capstone
assembly), Euclid/Spectrum (4: levels = weak eigenvalues with
multiplicity), Euclid/Corollaries (6: Cors 3.4, 4.4, 4.6, 4.7, 4.8),
Euclid/FixedMesh (3: Cor 5.2).

Independent statement audit (checker agent, 12:35): definitions, indices,
constants and hypotheses faithful to the paper.  Note recorded:
`IsPositiveGroundState` asks `φ ≥ 0` a.e.; the paper's `φ₁` is strictly
positive (cited background).  Since the normalized nonnegative ground state is
unique (`IsPositiveGroundState.unique`), the paper's `φ₁` satisfies the Lean
hypothesis, so the Lean theorems apply to it; strict positivity itself is not
used by any proof and is not formalized.

## 2026-09-27 — promotion receipt `multiwell-exact-compression-2026-09-27`

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: a concrete compression-matrix wrapper of
   `FinalTheoremMultiWell`, supplying the matrix `T_L` used by its `hnorm` and
   ordered-cluster slots.
3. Exact paper source: `paper.tex`, equation `eq:exact-compression`, where the
   compression of `P_1 V_L P_1` has zero diagonal and off-diagonal entries
   `-c_{d,s} integral integral phi(x) phi(y) / |L(a_i-a_j)+x-y|^kappa`.
4. Promotion event: define the finite-well cross kernel
   `|center+x-y|^(-kappa)`, define the exact matrix `T_L`, prove its diagonal
   and real-symmetry properties by product-measure swap and negated center,
   and consume those properties in a wrapper of `FinalTheoremMultiWell`.
   Acceptance is the focused `Tunneling/MultiWell.lean` replay.
5. Sole credit expected: caller-consumed exact compression-matrix construction
   and symmetry slot.  The entrywise Taylor norm bound and block-unitary
   realization remain separate analytic obligations.

### Acceptance result — exact compression matrix construction

`multiWellCrossKernel`, `multiWellCompressionMatrix`, its diagonal identity,
and its real-symmetry/Hermitian proofs are accepted by the focused
`Tunneling/MultiWell.lean` replay.  The wrapper
`FinalTheoremMultiWell_exactCompression` consumes this exact matrix and its
Hermitian witness in `FinalTheoremMultiWell`.  The full package replay passes
(`Build completed successfully (2972 jobs)`), the literal scan has no project
`axiom` or proof `sorry`, and `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for all four capstones.

This earns the caller-consumed exact compression-matrix construction and
symmetry slot.  The matrix norm estimate `hnorm`, its Taylor entrywise bounds,
and the block-unitary construction remain open.

## 2026-09-27 — promotion receipt `multiwell-taylor-remainder-2026-09-27`

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell_exactCompression`.
2. Immediate Lean consumer: the `hnorm` hypothesis of
   `FinalTheoremMultiWell_exactCompression`, through the entrywise compression
   estimate for `multiWellCompressionMatrix`.
3. Exact paper source: `paper.tex`, Lemma 4.3, equation `eq:multi-taylor`,
   where `F(z)=|L(a_i-a_j)+z|^(-kappa)` has second-order remainder bounded by
   `C_{kappa,R} L^(-kappa-2) |a_i-a_j|^(-kappa-2)` and the linear term cancels
   after integration against `phi_1(x) phi_1(y)`.
4. Promotion event: prove the product-measure cancellation
   `integral u(x) u(y) inner a (x-y) = 0`, formalize the finite-well Taylor
   remainder and its entrywise bound for `multiWellCrossKernel`, and consume
   those bounds in the exact compression matrix norm estimate.
5. Sole credit expected: caller-consumed finite-well Taylor/entrywise
   compression bound.  The finite-well block-unitary and cluster realization
   remain separate.

## 2026-09-27 — promotion receipt `multiwell-epsilon-bridge-2026-09-27`

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: `multiWellConclusion_of_clusterCompression_matrix`,
   followed by the `hcompress` slot in `FinalTheoremMultiWell`.
3. Exact paper source: `paper.tex`, Lemma 4.3 and equation
   `eq:compression-error`, where
   `epsilon_L = c C phiMass^2 Sigma_{kappa+2}(a) L^(-kappa-2)` is a product of
   nonnegative factors and supplies the operator-norm error budget.
4. Promotion event: prove `sigmaKappa_nonneg` and
   `multiWellEpsilon_nonneg`, make `L` explicit in the matrix consumer, and
   replace the failing local positivity placeholder with the named
   nonnegativity theorem.  The acceptance check is the unchanged focused
   `lake env lean --threads=4 -DmaxErrors=500 Tunneling/MultiWell.lean` replay.
5. Sole credit expected: source-faithful `epsilon_L` nonnegativity repair for
   the compression bridge; this is a zero final-facing theorem-slot credit
   until the matrix consumer is actually invoked by `FinalTheoremMultiWell`.

### Acceptance result — multi-well matrix compression integration

`sigmaKappa_nonneg` and `multiWellEpsilon_nonneg` are accepted, and the
focused `MultiWell.lean` replay passes.  `FinalTheoremMultiWell` now invokes
`multiWellConclusion_of_clusterCompression_matrix`, so the ordered Weyl
comparison is consumed by the named capstone and the scalar `hcompress`
placeholder has been removed.  The full package replay passes
(`Build completed successfully (2972 jobs)`), the literal scan has no project
`axiom` or proof `sorry`, and `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for all three capstones.

This earns the caller-consumed matrix-compression slot.  It does not construct
the block compression matrix `T_L`, prove its entrywise Taylor bounds, or
discharge the isolated-cluster and cluster-edge inputs `hcluster`, `hupper`,
and `hnext`; those remain analytic obligations for an unconditional theorem.

## 2026-09-27 — eventual multi-well size conditions

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: `multiWellStatement`,
   `multiWellLimit_of_conclusion`, and `FinalTheoremMultiWell`.
3. Exact paper source: `paper.tex`, equation `eq:multi-size-conditions`, with
   fixed distinct sites `a_i` and `L -> infinity`.
4. Promotion event: assume only pairwise distinct sites and derive
   `0 < L`, `4 * A.R <= L * ‖a i - a j‖` for `i != j`, and
   `multiWellGamma A a L <= A.gap / 4` eventually in `L`, then replace the
   raw `hcond` hypothesis in `FinalTheoremMultiWell` by the geometric
   distinctness hypothesis.

Acceptance requires the focused `MultiWell.lean` replay, a full `lake build`,
the literal no-`axiom`/no-`sorry` scan, and the kernel axiom audit.  This
closes the asymptotic size-condition derivation only; the isolated-cluster
and compression inputs remain separate analytic obligations.

### Acceptance result — eventual multi-well size conditions

`multiWellCondition_eventually` derives the separation and smallness
conditions from pairwise distinct sites, and `FinalTheoremMultiWell` now takes
that geometric distinctness hypothesis instead of raw `hcond`.  The focused
`MultiWell.lean` replay and full `lake build` pass (2972 jobs).  The literal
scan has no project `axiom` or proof `sorry`, and all three capstones depend
only on `[propext, Classical.choice, Quot.sound]`.

This closes the asymptotic size-condition derivation only.  The isolated
cluster, compression, and remaining finite-well spectral inputs are still
open.

## 2026-09-27 — normalized two-well parity identity

1. Named final-facing theorem: `Tunneling.FinalTheorem` and
   `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `GroundStatePerturbation.branchRayleigh`,
   `GroundStatePerturbation.twoWellBlockEnergy`, `Tunneling.branchEnergy`,
   and the symmetric/antisymmetric branch split used by `twoWellLambda` and
   `FinalTheorem`.
3. Exact paper source: `paper.tex`, Lemma 2.1 and equation `eq:direct-sum`,
   where the unitary change of variables
   `(x,y) -> ((x+y)/sqrt(2), (x-y)/sqrt(2))` converts the block form into
   `A_D+B_L` and `A_D-B_L`.
4. Promotion event: prove the normalized parity identity
   `twoWellBlockEnergy q W x y = branchRayleigh q W ((sqrt(2))^-1 * (x+y)) +
   branchRayleigh q (-W) ((sqrt(2))^-1 * (x-y))` from the accepted
   unnormalized identity, with the branch Rayleigh homogeneity made explicit.

Acceptance requires the focused `Perturbation.lean` and `Final.lean` replays,
a full `lake build`, the literal no-`axiom`/no-`sorry` scan, and the kernel
axiom audit.  This is the normalized algebraic change of variables only; the
concrete form-domain unitary and the operator spectral realization remain
separate obligations.

### Acceptance result — normalized two-well parity identity

`branchRayleigh_smul` and
`twoWellBlockEnergy_parity_normalized` are accepted by the focused
`Perturbation.lean` replay.  The normalized identity feeds the same
`branchRayleigh` integrand used by `branchEnergy`, `twoWellLambda`, and the
branch split in `FinalTheorem`.  The focused `Final.lean` replay passes, and
the full `lake build` completes successfully (2972 jobs).  The literal scan
has no project `axiom` or proof `sorry`, and all three capstones depend only
on `[propext, Classical.choice, Quot.sound]`.

This closes the normalized algebraic change of variables only.  The concrete
form-domain unitary, the compact-resolvent spectral realization, and the
finite-well cluster and compression estimates remain open.

## 2026-09-27 — exact two-well block-parity identity

1. Named final-facing theorem: `Tunneling.FinalTheorem` and
   `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `branchEnergy`, `twoWellLambda`, the two branch
   estimates in `FinalTheorem`, and the concrete `L2TwoWellAux` cross-kernel
   interface.
3. Exact paper source: `paper.tex`, Lemma 2.1 and equation `eq:direct-sum`,
   where expanding the block quadratic form and applying the symmetric versus
   antisymmetric change of variables gives `A_D+B_L` and `A_D-B_L`.
4. Promotion event: define the block quadratic energy and parity components,
   prove the exact identity
   `blockEnergy(p+r,p-r) = 2 * (branchEnergyAt(p) + branchEnergyAt(-W,r))`,
   and rewrite `branchEnergy` through the same parity Rayleigh integrand used
   by `twoWellLambda` and `FinalTheorem`.

Acceptance requires the focused `Final.lean` replay, a full `lake build`, the
literal no-`axiom`/no-`sorry` scan, and the kernel axiom audit.  This is the
algebraic block reduction only; the concrete unitary identification of the
restricted fractional Laplacian form domains remains separate.

### Acceptance result — exact two-well block-parity identity

`GroundStatePerturbation.branchRayleigh`,
`GroundStatePerturbation.twoWellBlockEnergy`, and
`GroundStatePerturbation.twoWellBlockEnergy_parity` are accepted by the
perturbation-module replay.  `Tunneling.branchEnergy` and the `ciInf`
estimates in `branch_energy_bounds` now use the same qualified Rayleigh
integrand.  The focused `Final.lean` replay passes, and the full `lake build`
completes successfully (2972 jobs).  The literal scan has no project `axiom`
or proof `sorry`, and all three capstones depend only on
`[propext, Classical.choice, Quot.sound]`.

This closes the algebraic block-parity identity only.  The concrete unitary
identification of restricted fractional Laplacian form domains, the
compact-resolvent spectral realization, and the finite-well cluster and
compression estimates remain open.

## Latest acceptance — 2026-09-27

The nonnegative lifted Gagliardo form and the second Rayleigh infimum
interface are accepted.  `restrictedZeroExteriorFormLift_nonneg` and
`oneWellForm_nonneg` provide form positivity; `orthogonalRayleighInf` and
`quadratic_gap_of_orthogonalRayleighInf` identify the orthogonal second
Rayleigh infimum with `A.mu2`, and `hgapOrthFromForm` derives the universal
gap inequality.  The full `lake build` completes successfully (2972 jobs),
the literal scan has no project `axiom` or proof `sorry`, and all three
capstones depend only on `[propext, Classical.choice, Quot.sound]`.

This closes only the source-level positivity and one-well min-max
representation.  The compact-resolvent realization of the restricted
fractional Laplacian and the finite-well spectral reductions remain open.

## 2026-09-27 — second Rayleigh infimum interface

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.hgapOrthFromForm`, `hgapEnergy`,
   `hgapq`, `toSpectralInput`, and `FinalTheoremL2`.
3. Exact paper source: `paper.tex`, Section 2, the variational definition of
   `lambda_2(D)` as the lowest Rayleigh energy on the orthogonal complement
   of the normalized ground state, together with `g = mu_2 - mu_1`.
4. Promotion event: define the orthogonal second Rayleigh infimum and replace
   `honeWellGap` by the scalar identity `honeWellSecond : secondInf = A.mu2`,
   deriving the universal orthogonal gap inequality from form positivity.

Acceptance requires the focused form/capstone replay, a full `lake build`,
the literal no-`axiom`/no-`sorry` scan, and the kernel axiom audit.  This is
the source-faithful min-max interface only; the compact-resolvent spectral
realization of the restricted fractional Laplacian remains open.

## 2026-09-27 — nonnegative lifted Gagliardo form

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.oneWellForm`, the second-energy
   infimum interface, and the `honeWellGap` realization in `Final.lean`.
3. Exact paper source: `paper.tex`, equation `eq:form`, where
   `c_{d,s} > 0` and the squared Gagliardo seminorm make the zero-exterior
   quadratic form nonnegative on its finite-energy domain.
4. Promotion event: prove `restrictedZeroExteriorFormLift_nonneg` and
   `oneWellForm_nonneg`, then use positivity to supply the lower bound needed
   for the orthogonal second Rayleigh infimum.

Acceptance requires the focused form/capstone replay, a full `lake build`,
the literal no-`axiom`/no-`sorry` scan, and the kernel axiom audit.  This is a
source-level positivity bridge, not a construction of the fractional
Laplacian or its spectral theorem.

## 2026-09-27 — gap-first one-well interface

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.hgroundPolar`, `hgroundMin`,
   `hgapEnergy`, `hgapq`, `toSpectralInput`, and `FinalTheoremL2`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:form`, together
   with equation `eq:mass`, where the normalized ground state satisfies the
   first-variation identity and the orthogonal spectral-gap inequality.
4. Promotion event: replace the independent global-minimization field
   `honeWellMin` by the source-level first-variation field `honeWellPolar`,
   then derive `hgroundMin` from `honeWellPolar` and `honeWellGap` while
   replaying the unchanged `FinalTheoremL2` caller.

Acceptance requires the focused `Final.lean` replay, a full `lake build`, the
literal no-`axiom`/no-`sorry` scan, and the kernel axiom audit.  This event
removes one analytic assumption and identifies the orthogonal spectral-gap
inequality as the remaining one-well spectral obligation; it does not claim
construction of the restricted fractional Laplacian itself.

### Acceptance result — gap-first one-well interface

`L2TwoWellAux.honeWellMin` has been removed as an independent field and
replaced by `honeWellPolar`, the first-variation identity on the ground-state
line.  The theorem `hgroundMin` is now derived from `honeWellPolar` and
`honeWellGap` through `hgapEnergy`; `hgroundPolarFromSource` feeds the
unchanged `hgroundPolar`, `hqEnergyGroundAdd`, `hgapq`, `toSpectralInput`, and
`FinalTheoremL2` chain.  The focused `Final.lean` replay passes, and the full
`lake build` completes successfully (2972 jobs).  The literal scan has no
project `axiom` or proof `sorry`, and the kernel audit reports only
`[propext, Classical.choice, Quot.sound]` for `FinalTheorem`,
`FinalTheoremL2`, and `FinalTheoremMultiWell`.

This closes the global-minimization redundancy only.  The field
`honeWellGap`, its source-level realization for the restricted fractional
Laplacian, and the finite-well spectral constructions remain open.

## 2026-09-24 — source extraction for the two-well theorem

1. Named final-facing theorem: `Tunneling.FinalTheorem`.
2. Immediate Lean consumer: `Tunneling.FinalTheorem`, to be defined after
   the one-well operator and spectral interfaces are available.
3. Exact paper source: `paper.tex`, Theorem 3.3 and equations
   `eq:explicit-L0`, `eq:lambda1`, `eq:lambda2`,
   `eq:two-well-third-level`, and `eq:gap-limit`.
4. Promotion event: exact paper-source extraction for the two-well splitting
   theorem slot; the next edit must integrate this extraction into the named
   consumer rather than add an unconsumed sibling lemma.

The first file `Tunneling/Statements.lean` records the parameters and the
conclusion as a single proposition.  It intentionally contains no operator
construction yet: that is the next source-extraction and interface bridge.

### Acceptance repair

The first compile of this source extraction failed on real-power elaboration
and implicit constant binders.  The repair keeps the same paper source and
consumer, makes the constants explicit parameters, and imports mathlib's real
power and topology interfaces.  No new theorem slot is claimed by this repair.

The second compile identified two remaining extraction defects: the real-power
definitions must be `noncomputable`, and the eigenvalue family in `gapLimit`
is indexed first by the separation and then by the eigenvalue index.  This is
also a source-extraction repair with no theorem-slot credit.

## 2026-09-24 — Lemma 3.1 promotion spine

1. Named final-facing theorem: `Tunneling.FinalTheorem`.
2. Immediate Lean consumer: `Tunneling.FinalTheorem`, whose two-well branch
   will instantiate the symmetric and antisymmetric perturbations `B_L` and
   `-B_L`.
3. Exact paper source: `paper.tex`, Lemma 3.1 and equations `eq:perturb` and
   the Rayleigh decomposition in its proof.
4. Promotion event: caller-consumed proof of the ground-state perturbation
   bound.  Success credits the abstract perturbation ingredient of the
   two-well theorem slot; it does not close the theorem slot until the actual
   two-well operator consumes it.

The new file `Tunneling/Perturbation.lean` contains the exact real-Hilbert
Rayleigh estimate.  The next integration step is to instantiate it with the
two-well block operators and verify the caller hypotheses in `FinalTheorem`.

### Lemma 3.1 acceptance repair

The first proof build failed on four local representation issues: the
Pythagorean identity needed a fixed scalar/residual decomposition, real inner
products required `real_inner_smul_*` rewrites after additivity expansion, the
subtracted ground-state term is `‖η‖^2 * inner (W φ) φ`, and the absolute-value
bounds needed `abs_le` before scalar elimination.  These repairs retain the
same paper source, supplier statement, consumer, and acceptance event.

## 2026-09-24 — FinalTheorem integration spine

1. Named final-facing theorem: `Tunneling.FinalTheorem`.
2. Immediate Lean consumer: `Tunneling.FinalTheorem`, through the exact
   branch ground-energy interface `Tunneling.branchEnergy`.
3. Exact paper source: `paper.tex`, the applications of Lemma 3.1 to `B_L`
   and `-B_L` in Theorem 3.3, followed by the remainder, third-level, and
   limiting-gap conclusions.
4. Promotion event: caller-consumed application of
   `GroundStatePerturbation.lower_bound` to both two-well branches.  Success
   credits the branch-estimation link toward the two-well theorem slot; the
   fractional block construction and kernel expansion remain separate
   source-extraction obligations.

The edited file `Tunneling/Final.lean` defines the branch Rayleigh infima and
states `FinalTheorem` over an explicit two-well spectral input.  That input is
the remaining bridge to the restricted fractional Laplacian; it is not an
axiom or a replacement theorem.

### FinalTheorem acceptance repair

The first integration compile found local representation defects in the
branch infimum, the `A.L0` positivity argument, negative-branch inner-product
normalization, and the two triangle-inequality calculations.  These repairs
retain the same paper source, consumer, and promotion event.

## 2026-09-24 — fractional form source extraction

1. Named final-facing theorem: `Tunneling.FinalTheorem`.
2. Immediate Lean consumer: `Tunneling.FinalTheorem`, through the future
   construction of `TwoWellSpectralInput` from the restricted fractional
   quadratic form.
3. Exact paper source: `paper.tex`, Section 2, equations `eq:form`,
   `eq:mass`, and the zero-exterior Gagliardo seminorm preceding them.
4. Promotion event: concrete source extraction of the Gagliardo integrand and
   zero-exterior form.  Success credits the analytic-form bridge toward the
   two-well theorem slot; it does not close the theorem slot until the form is
   linked to the operator and spectral data consumed by `FinalTheorem`.

The new file `Tunneling/FractionalForm.lean` records the kernel, integrand,
zero-exterior support condition, and their first pointwise identities.

## 2026-09-24 — exact cross-term bridge for Lemma 2.1

1. Named final-facing theorem: `Tunneling.FinalTheorem`.
2. Immediate Lean consumer: `Tunneling.FinalTheorem`, through the two-well
   branch interaction term in its `B_L` and `-B_L` applications.
3. Exact paper source: `paper.tex`, Lemma 2.1 and the displayed identity
   `|u(x)-v(y)|^2-|u(x)|^2-|v(y)|^2=-2 u(x)v(y)` in its proof.
4. Promotion event: caller-consumed integral form of the Gagliardo cross-term
   cancellation.  Success credits the cross-term bridge toward the two-well
   theorem slot; operator-domain identification and the kernel expansion
   remain separate obligations.

The next edit specializes `crossTerm_identity` to the Gagliardo kernel and
integrates the resulting pointwise identity against a product measure.  The
consumer is the same `FinalTheorem` bridge; no separate leaf theorem is
accepted without that consumer check.

### Acceptance result

`Tunneling.FinalTheorem` compiled after importing the integral cross-term
identity and consuming its scalar specialization in the negative-branch
remainder algebra.  This earns the cross-term bridge credit; the remaining
unconsumed spine item is the bounded cross-pairing operator in Lemma 2.1.

## 2026-09-24 — Riesz operator for the cross pairing

1. Named final-facing theorem: `Tunneling.FinalTheorem`.
2. Immediate Lean consumer: `Tunneling.FinalTheorem`, through the symmetric
   and antisymmetric branch operators `B_L` and `-B_L`.
3. Exact paper source: `paper.tex`, Lemma 2.1 and equation `eq:B`, including
   the statement that the real symmetric cross kernel defines a bounded
   self-adjoint integral operator.
4. Promotion event: caller-consumed construction of a self-adjoint operator
   from a bounded symmetric cross pairing by Fréchet-Riesz representation.

The next edit adds this operator construction and makes `FinalTheorem` derive
the branch symmetry from it.  Kernel measurability and the `L²` integral
representation remain the following source bridge.

### Acceptance result

`Tunneling.FinalTheorem` compiled with `SymmetricCrossPairing.operator_symm`
as the source of branch symmetry.  The next unconsumed source item is the
`L²` kernel representation and its swap symmetry.

## 2026-09-24 — L² representation of the Gagliardo cross pairing

1. Named final-facing theorem: `Tunneling.FinalTheorem`.
2. Immediate Lean consumer: `Tunneling.FinalTheorem`, through the `cross`
   field feeding the branch operators `B_L` and `-B_L`.
3. Exact paper source: `paper.tex`, Lemma 2.1 and equation `eq:B`, together
   with the real symmetric kernel representation of the cross term.
4. Promotion event: caller-consumed `L²` kernel representation and symmetry
   of the cross pairing.  Success credits the concrete form-to-pairing link;
   the boundedness estimate and spectral construction remain separate.

The next edit adds an `L²` pairing structure whose kernel equation is the
Gagliardo `crossPairing`, and derives its symmetry from
`crossPairing_symm`.

### Acceptance result and repair

`Tunneling.FractionalForm` compiles with the `L²` kernel equation and swap
symmetry.  The consumer declarations were initially placed before
`TwoWellSpectralInput` and `FinalTheorem`; this is a declaration-order defect,
not a mathematical change.  The repair moves `L2TwoWellAux.toSpectralInput`
and `FinalTheoremL2` below those dependencies and reruns the exact caller.

### Acceptance repair — `L²` bridge typeclasses and reductions

The next caller build exposed local interface defects in the `L²` bridge:
the Fréchet-Riesz operator needs `CompleteSpace H`, the Gagliardo swap
symmetry needs `SFinite mu`, and two reductions need explicit unfolding of
the represented form.  This edit propagates those instances and fixes the
reductions without changing the paper source or theorem statement.

## 2026-09-24 — separated-kernel Schur bound for `B_L`

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`, through
   `Tunneling.FinalTheorem` and the two-well conclusion
   `TwoWellConstants.twoWellStatement`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, specifically the
   `hBnorm` field consumed by `FinalTheorem` in both branch perturbations.
3. Exact paper source: `paper.tex`, equation `eq:B`, Lemma 3.2 and equation
   `eq:Bnorm`, including the Schur-test estimate
   `|L e-x-y| >= L-2R >= L/2` and the resulting bound
   `norm B_L <= c_{d,s} 2^kappa |D| L^{-kappa}`.
4. Promotion event: caller-consumed derivation of `hBnorm` from the bounded
   separated cross kernel.  Success credits the kernel-boundedness bridge
   toward the two-well theorem slot; the interaction expansion and spectral
   construction remain separate obligations.

The next edit adds the exact separated cross kernel, proves its Schur-type
form estimate on `L²` for functions supported in the finite-measure component,
and changes `L2TwoWellAux` to consume that estimate instead of assuming the
operator norm bound as a raw field.  The acceptance check is the existing
`FinalTheoremL2` caller build after this replacement.

### Acceptance repair — norm-bound algebra

The first caller check passed the `crossPairing`-to-form conversion but failed
inside `SymmetricCrossPairing.operator_norm_le`: the final contradiction is
quadratic and must explicitly multiply `C * ‖x‖ < ‖χ.operator x‖` by the
positive quantity `‖χ.operator x‖`.  The repair makes that multiplication a
named hypothesis before closing the inequality chain.

### Promotion reset after two failed acceptance checks

The receipt above is closed as **promotion stalled** after two consecutive
uncredited `FinalTheoremL2` checks.

1. Paper formula: Lemma 3.2, `norm B_L <= c_{d,s} 2^kappa |D| L^{-kappa}`,
   obtained from the separated kernel sup bound and the Schur estimate.
2. Current Lean type: `SymmetricCrossPairing.operator_norm_le`, proving
   `norm (chi.operator) <= C` from the uniform bilinear estimate
   `abs (chi.form x y) <= C * norm x * norm y`.
3. Proposed bridge: from the bilinear form `chi.form : H x H -> real` to the
   represented operator `chi.operator : H ->L[real] H`.
4. Smallest identity test: at `y = chi.operator x`, use
   `chi.form x (chi.operator x) = norm (chi.operator x)^2`, multiply the
   strict candidate inequality `C * norm x < norm (chi.operator x)` by the
   positive quantity `norm (chi.operator x)`, and contradict the form bound.
5. Theorem slot: `L2TwoWellAux.toSpectralInput.hBnorm`, consumed immediately
   by `Tunneling.FinalTheorem` and `Tunneling.FinalTheoremL2`.

The current repair changes the identity test from an aggregate nonlinear
cancellation to the named multiplication inequality in item 4.  That is a
changed mathematical input, so the next caller replay is checked under a new
receipt while the paper formula, bridge domain/codomain, and theorem slot stay
fixed.

## 2026-09-24 — squared-norm receipt for the separated-kernel Schur bound

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput.hBnorm`.
3. Exact paper source: `paper.tex`, Lemma 3.2 and equation `eq:Bnorm`.
4. Promotion event: caller-consumed proof that the Riesz operator norm is
   bounded by the uniform cross-form estimate, using the exact squared-norm
   identity above.

### Acceptance repair — multiplication representation

The first check under this receipt failed because `mul_lt_mul_of_pos_right`
returned a product `norm * norm` while the target used `norm ^ 2`, elaborated
as `npowRec`.  The repair represents the squared norm by
`real_inner_self_eq_norm_mul_norm`, matching the exact multiplication in the
identity test without changing the paper statement or theorem slot.

### Acceptance result

`Tunneling.FinalTheoremL2` compiled after the multiplication repair.  This
credits the form-to-Riesz-operator norm bridge used for `hBnorm`; the raw
`hformBound` estimate below it remains the next unconsumed source item.

## 2026-09-24 — separated-kernel Schur form estimate

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput.hformBound`, which
   feeds the accepted `hBnorm` bridge and both branch estimates in
   `Tunneling.FinalTheorem`.
3. Exact paper source: `paper.tex`, Lemma 3.2 and equation `eq:Bnorm`; the
   pointwise separated-kernel estimate is
   `|L e-x-y|^(-kappa) <= 2^kappa L^(-kappa)` for `L >= 4R`, followed by the
   finite-component `L^1`/`L^2` estimate producing `|D|`.
4. Promotion event: caller-consumed derivation of `hformBound` from a bounded
   separated kernel on a finite-measure component.  Success credits the
   concrete Schur form bound toward the two-well theorem slot; the exact
   kernel expansion and spectral construction remain separate obligations.

The next edit adds the generic bounded-kernel product estimate and the exact
translated cross kernel.  The acceptance check is the unchanged
`FinalTheoremL2` caller after `hformBound` is discharged from those supplies.

### Acceptance repair — kernel supplier interfaces

The first supplier check failed before its consumer could be tested:

1. `kernelCrossPairing_le_of_abs_integrable` had the scalar bound typed as
   `C : ℝ → ℝ` instead of `C : ℝ`, so `K` and `C 0` elaborated incorrectly.
2. The pointwise multiplication estimate needs an explicit nonnegative
   multiplier for `mul_le_mul_of_nonneg_right`; `linarith` cannot discover
   that product inequality.
3. `MeasureTheory.integral_prod_mul` needs explicit component functions so
   the product-measure equality unifies with `|u z.1| * |v z.2|`.
4. The Hölder theorem expects `MemLp` at `ENNReal.ofReal 2`, while ordinary
   `MemLp` notation uses `2`; the repair inserts the `ENNReal.ofReal_ofNat`
   conversion and uses `Pi.abs_apply` for pointwise absolute-value functions.
5. The `L²` corollary rewrites `lpNorm ⇑u` and `lpNorm ⇑v` separately instead
   of attempting one multi-hypothesis rewrite.

These are source-interface repairs only.  The paper source, supplier theorem
slot, immediate consumer, and acceptance check remain unchanged.

### Acceptance repair — square-root product

The remaining supplier failure was the final algebraic normalization in
`kernelCrossPairing_Lp_le`: `nlinarith` could not use
`Real.mul_self_sqrt` through the two `L²` norm factors.  The repair makes the
identity `sqrt(m) * sqrt(m) = m` explicit and re-associates the `C` product
before applying the already-proved `L¹`/`L²` estimates.

### Acceptance result

`Tunneling.FractionalForm.lean` compiled after the square-root repair.  This
credits the bounded-kernel product estimate and its `L¹`/`L²` corollary.  The
next caller integration must replace the raw `hformBound` field with this
supplier specialized to the translated cross kernel.

## 2026-09-24 — translated-kernel caller integration

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, specifically the
   `hformBound` field consumed by `FinalTheorem` and the accepted `hBnorm`
   bridge.
3. Exact paper source: `paper.tex`, equation `eq:B`, Lemma 3.2 and equation
   `eq:Bnorm`, with kernel `|L e-x-y|^(-kappa)` and the finite-component
   `L¹`/`L²` estimate.
4. Promotion event: caller-consumed replacement of the raw cross-form bound by
   `kernelCrossPairing_Lp_le` specialized to `translatedCrossKernel`.  The
   unchanged acceptance check is the `FinalTheoremL2` caller build.

The next edit introduces the kernel-parameterized `L²` pairing, preserves its
Riesz symmetry using `translatedCrossKernel_swap`, and makes
`L2TwoWellAux.toSpectralInput` derive `hformBound` from the accepted supplier.

### Acceptance repair — kernel symmetry beta and swap

The kernel symmetry lemma had two representation mismatches before the caller
could be tested: beta-reduction was needed before rewriting `K x y`, and
`integral_prod_swap` needed an explicit integrand whose swapped evaluation
matches `kernelCrossPairing K mu v u`.  The repair makes both representations
explicit and changes no theorem statement.

### Acceptance repair — finite measure and beta sign

The caller build exposed two exact interface gaps after the kernel supplier
was accepted: `kernelCrossPairing_Lp_le` requires `IsFiniteMeasure mu`, and
the Schur constant `A.c * 2^A.kappa * L^(-A.kappa)` needs a nonnegativity
proof.  The repair propagates the finite-measure instance through
`L2TwoWellAux` and derives the constant's sign from `hbetaNonneg`,
`hmeasure`, and `hvolumeD`, without changing the paper statement.

## 2026-09-24 — translated-kernel pointwise bound

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, specifically the
   `hkernelBound` input to `kernelCrossPairing_Lp_le` and the resulting
   `hBnorm` bridge.
3. Exact paper source: `paper.tex`, Lemma 3.2, equation `eq:Bnorm`, and the
   proof estimate `|L e-x-y| >= L-2R >= L/2`, yielding
   `|L e-x-y|^(-kappa) <= 2^kappa L^(-kappa)`.
4. Promotion event: caller-consumed derivation of the pointwise translated
   kernel bound from the lower separation estimate.  The acceptance check is
   the unchanged `FinalTheoremL2` caller build after `hkernelBound` is supplied
   by this theorem and the exact translated kernel definition.

The next edit adds `translatedCrossKernel_le_of_lowerBound` and its
`2^kappa L^(-kappa)` specialization beside `translatedCrossKernel_swap`, then
changes `L2TwoWellAux` to retain the exact separation data and derive
`hkernelBound` rather than assuming it.

### Acceptance repair — real-power division

The pointwise bound required one local normalization before integration:
`(L/2)^(-kappa)` must be rewritten by `Real.div_rpow` and `Real.rpow_neg`
to `2^kappa * L^(-kappa)`.  The repair keeps the paper's exact constants and
changes no theorem statement.

## 2026-09-24 — caller normalization repair

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, specifically the
   `hkernelBound` derivation feeding `kernelCrossPairing_Lp_le` and the accepted
   `hBnorm` bridge.
3. Exact paper source: `paper.tex`, Lemma 3.2 and equation `eq:Bnorm`, with
   `kappa = d + 2s` and the kernel sign `K L x y = -c_{d,s} |L e-x-y|^{-kappa}`.
4. Promotion event: repair of the caller-side nonnegativity and absolute-value
   normalization in `toSpectralInput.hBnorm`; the acceptance check is the
   unchanged `FinalTheoremL2` caller build.

The first failing proof obligations are local algebra only: positivity of
`kappa` from `kappa = d + 2s`, and normalization of
`|(-c_{d,s}) * t|` to `c_{d,s} * t` for nonnegative `t`.  The paper statement,
kernel representation, and downstream theorem slot are unchanged.

### Acceptance repair — explicit real coercion

The first caller replay exposed one elaboration-only defect in that repair:
`Nat.cast_nonneg A.d` left the target ordered ring implicit, so Lean could not
synthesize `IsOrderedRing`.  Pinning the witness as
`(0:ℝ) ≤ (A.d : ℝ)` leaves the paper source, supplier, consumer, and
acceptance check unchanged.

## 2026-09-24 — Euclidean separation bridge

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: the concrete construction of the
   `L2TwoWellAux` separation field `hsep`, and hence the `hkernelBound` input
   to `toSpectralInput.hBnorm`.
3. Exact paper source: `paper.tex`, Lemma 3.2 and equation `eq:Bnorm`, namely
   `|Le-x-y| >= L-2R >= L/2` for `x,y in D subset B_R` and `L >= 4R`.
4. Promotion event: source extraction of the lower separation estimate from
   the actual Euclidean geometry.  The acceptance check is the unchanged
   `FinalTheoremL2` caller build after this theorem is used to discharge
   `hsep`.

The theorem will use only the reverse triangle inequality and the unit-vector
normalization `|e|=1`; no spectral or operator assumption is added.

### Acceptance integration — geometry replaces raw separation

The supplier theorem must be consumed by the exact `L2TwoWellAux` interface,
not left as an isolated lemma.  The integration replaces the raw `center` and
`hsep` fields by a unit direction `e : X`, the component bound
`∀ x : X, ‖x‖ ≤ A.R`, and the exact kernel center `L • e`.  The consumer is
`L2TwoWellAux.toSpectralInput.hBnorm`, whose acceptance check remains the
`FinalTheoremL2` caller build.  Success credits the concrete geometric
discharge of the paper's `|Le-x-y| >= L/2` input.

### Acceptance result

`FinalTheoremL2` compiled with `hsep` derived from `direction`, `hdirection`,
and `hX`.  This credits the Euclidean separation bridge.  The next
unconsumed source item is Lemma 3.2's interaction-kernel expansion in terms
of `I_L`, together with the exact identity `t_L = -c_{d,s} I_L`.

## 2026-09-24 — interaction-mass representation

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput.htApprox`, which
   feeds the branch-shift estimates in `Tunneling.FinalTheorem`.
3. Exact paper source: `paper.tex`, equation `eq:B`, Lemma 3.2 and equation
   `eq:kernel-expansion`, including `t_L = -c_{d,s} I_L`.
4. Promotion event: replace the raw `K L` matrix-element remainder input by
   the paper's `I_L` estimate and derive the signed `t_L` identity through
   kernel scalar multiplication.  The acceptance check is the unchanged
   `FinalTheoremL2` caller build.

The integration adds only the exact kernel congruence and constant-kernel
scaling identities needed to turn `K L = -c_{d,s} |L e-x-y|^{-kappa}` into
`t_L = -c_{d,s} I_L`.

### Acceptance repair — kernel congruence beta reduction

The first supplier replay failed because the pointwise kernel congruence was
still displayed as lambda applications on `(x, y)`.  Spelling out the
evaluated integrand `u x * v y * K_i x y` before applying the pointwise kernel
equality repairs the representation without changing any theorem statement.

### Promotion stalled — interaction-mass receipt

The interaction-mass receipt now has two consecutive uncredited acceptance
checks.  The first failed in `kernelCrossPairing_congr` before the consumer
could run.  The second reached `L2TwoWellAux.toSpectralInput.htApprox` but
failed at the absolute-value normalization because `q` was folded on the
right while the source statement keeps the left-associated product
`A.c * A.phiMass ^ 2 * L ^ (-A.kappa)`.  The receipt is closed as promotion
stalled.

#### Spine reset

- Paper formula: `t_L = -c_{d,s} I_L` and
  `|I_L-m_1^2 L^{-kappa}| <= C m_1^2 L^{-kappa-2}`, hence
  `|t_L+c_{d,s}m_1^2 L^{-kappa}| <=
  c_{d,s}C m_1^2 L^{-kappa-2}`.
- Current Lean type: `hI : |I - m_1^2 L^{-kappa}| <= C m_1^2 L^{-kappa-2}`
  and the goal `|-c I + c m_1^2 L^{-kappa}| <= c C m_1^2 L^{-kappa-2}`.
- Proposed bridge: real scalar normalization from
  `(-c, I, m_1^2 L^{-kappa})` to `c * |I - m_1^2 L^{-kappa}|`, preserving the
  source's left-associated product in the codomain.
- Smallest identity test:
  `|-c * I + c * a * r| = c * |I - a * r|` for `c >= 0`.
- Theorem slot: `TwoWellSpectralInput.htApprox`, consumed by the two branch
  remainder estimates in `FinalTheorem`.

## 2026-09-24 — source-shaped scalar normalization

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput.htApprox`.
3. Exact paper source: `paper.tex`, `eq:B`, Lemma 3.2, equation
   `eq:kernel-expansion`, and `t_L=-c_{d,s}I_L`.
4. Promotion event: a new receipt whose bridge keeps the exact left-associated
   scalar product `c_{d,s}m_1^2L^{-kappa}` from the paper.  The acceptance
   check is the unchanged `FinalTheoremL2` caller build.

### Acceptance result

`FinalTheoremL2` compiled after the source-shaped scalar normalization.  This
credits the exact signed interaction-mass bridge: the `L2TwoWellAux` input is
now the paper's `I_L` estimate, while `toSpectralInput.htApprox` derives the
`B_L` matrix-element remainder using `t_L=-c_{d,s}I_L`.  The first missing
analytic supplier is now Lemma 3.2 itself, `eq:kernel-expansion`, rather than
an abstract kernel-sign interface.

## 2026-09-24 — Taylor-to-interaction-mass reduction

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput.htApprox`.
3. Exact paper source: `paper.tex`, Lemma 3.2 and equation
   `eq:kernel-expansion`; the proof integrates the pointwise Taylor remainder
   for `F_L(z)=|L e-z|^{-kappa}` and cancels the linear term because
   `int x phi_1(x) dx=0`.
4. Promotion event: replace the raw `hIApprox` field by pointwise Taylor,
   mass, first-moment cancellation, and explicit product-integrability data,
   then derive `hIApprox` in `toSpectralInput`.  The acceptance check is the
   unchanged `FinalTheoremL2` caller build.

The new supplier isolates the integrated Taylor remainder as an exact
product-measure identity; the Hessian estimate for the fractional kernel is
the only analytic input left after this bridge.

### Acceptance result

FinalTheoremL2 compiled after the Taylor-to-interaction-mass integration.
This credits the exact product-integral reduction of equation
eq:kernel-expansion: mass normalization and first-moment cancellation now
derive the I_L remainder through interactionMass_taylor_remainder.  The next
unconsumed source item is the pointwise Taylor bound hTaylorBound, supplied by
the Hessian estimate for F_L(z)=|L e-z|^(-kappa).

## 2026-09-24 — scalar Lagrange remainder for the kernel line

1. Named final-facing theorem: FinalTheoremL2.
2. Immediate Lean consumer: L2TwoWellAux.toSpectralInput.htApprox through
   the derived hTaylorBound field.
3. Exact paper source: paper.tex, Lemma 3.2 and the displayed second-order
   Taylor estimate for F_L(z)=|L e-z|^(-kappa) along z=t(x+y).
4. Promotion event: add the scalar Lagrange remainder theorem and derive the
   pointwise remainder bound from a second-derivative bound along the line.
   The acceptance check is the unchanged FinalTheoremL2 caller build.

The theorem specializes to the first-order Taylor polynomial at zero and uses
the exact factorial two in the Lagrange remainder.  The remaining analytic
input after integration is the second-derivative bound for the separated
kernel along each line.

### Promotion stalled — scalar Lagrange receipt

The scalar Lagrange remainder receipt has three consecutive uncredited
acceptance checks.  The first failed on unqualified interval names and
factorial notation.  The second reached the absolute-value normalization but
still used invalid postfix factorial syntax and an unqualified subset lemma.
The third reached the same normalization and failed because abs_of_nonneg
selected the derivative factor instead of the factorial denominator.  The
receipt is closed as promotion stalled.

#### Spine reset

- Paper formula: the Lagrange remainder is
  g(b)-g(a)-(b-a)g'(a) =
  g''(t)(b-a)^2/(2!) for some t in the open interval.
- Current Lean type: the remainder denominator is
  ((1 + 1 : Nat).factorial : Real), while the target constant is two.
- Proposed bridge: normalize the exact Nat factorial cast before applying
  abs_of_nonneg, preserving the derivative factor as an absolute value.
- Smallest identity test:
  |x * y / z| = |x| * y / z for y >= 0 and z > 0, with z the cast of
  Nat.factorial 2.
- Theorem slot: the hTaylorBound field consumed by
  L2TwoWellAux.toSpectralInput.htApprox.

## 2026-09-24 — explicit factorial normalization

1. Named final-facing theorem: FinalTheoremL2.
2. Immediate Lean consumer: L2TwoWellAux.toSpectralInput.htApprox through
   the derived hTaylorBound field.
3. Exact paper source: paper.tex, Lemma 3.2 and the second-order Taylor
   estimate for F_L(z)=|L e-z|^(-kappa).
4. Promotion event: a new receipt whose bridge fixes the factorial
   denominator at the exact Nat.factorial cast emitted by
   taylor_mean_remainder_lagrange.  The acceptance check is the unchanged
   FinalTheoremL2 caller build.

### Acceptance result — exact Taylor remainder slot

Tunneling.Final rebuilt successfully after replacing the arbitrary remainder
field and hTaylorDecomp identity with the exact named function
twoWellTaylorRemainder and its decomposition theorem.  The unchanged
FinalTheoremL2 caller consumes the exact remainder through hTaylorBound and
interactionMass_taylor_remainder.  This closes the Taylor-remainder
representation slot.  The remaining Lean work is the one-well spectral
construction, integrability bridges, and the multi-well and
Hong--Krahn--Szegő/numerical parts of the paper theorem.

### Acceptance integration — line restriction

1. Named final-facing theorem: FinalTheoremL2.
2. Immediate Lean consumer: L2TwoWellAux.toSpectralInput.htApprox through
   the derived hTaylorBound field.
3. Exact paper source: paper.tex, Lemma 3.2, the Taylor expansion of
   F_L(z)=|L e-z|^(-kappa) along z=t(x+y), and equation eq:kernel-expansion.
4. Promotion event: replace the raw hTaylorBound field by ContDiffOn,
   first-derivative, and second-derivative bounds for translatedCrossLine,
   then derive hTaylorBound with scalar_taylor_remainder_bound.  The
   acceptance check is the unchanged FinalTheoremL2 caller build.

The integration uses the exact endpoint identities at t=0 and t=1, so the
remaining unconsumed analytic input is only the second-derivative estimate
for the separated fractional kernel along each line.

### Acceptance result

FinalTheoremL2 compiled after the line-integration repair.  This credits the
scalar Lagrange remainder and its caller consumption: hTaylorBound is now
derived from translatedCrossLine ContDiffOn, first-derivative, and
second-derivative data.  The first missing analytic supplier is therefore the
exact derivative calculation for translatedCrossLine that discharges
hlineDeriv and hlineSecond.

## 2026-09-24 — derivative formulas for the separated kernel line

1. Named final-facing theorem: FinalTheoremL2.
2. Immediate Lean consumer: L2TwoWellAux.toSpectralInput.htApprox through
   hlineDeriv, hlineSecond, and the derived hTaylorBound.
3. Exact paper source: paper.tex, Lemma 3.2, the gradient and Hessian formulas
   for F_L(z)=|L e-z|^(-kappa), and the displayed bound
   ||nabla^2 F_L||=kappa(kappa+1)|L e-z|^(-kappa-2).
4. Promotion event: derive the first and second scalar derivatives of
   translatedCrossLine along t, including the exact radial factor
   kappa(kappa+1), and use them to prove hlineDeriv and hlineSecond.  The
   acceptance check is the unchanged FinalTheoremL2 caller build.

The bridge specializes to an inner-product-space line, where
|c-t z|^2 is quadratic in t and the chain rule gives the paper's exact radial
and transverse factors.

### Acceptance repair — first derivative representation

The first derivative supplier failed before reaching the paper formula.
The square was represented as a natural-number power while Real.rpow_mul
expects a real power; rpow_const was called through a projected
HasFDerivAtFilter field; and the zero-line nonvanishing argument needed
center - 0 • z to be rewritten to center.  These are representation repairs
only.  The paper formula, consumer, and acceptance check are unchanged.

### Acceptance integration — first line derivative

1. Named final-facing theorem: FinalTheoremL2.
2. Immediate Lean consumer: L2TwoWellAux.toSpectralInput.htApprox through
   the derived hlineDeriv used in hTaylorBound.
3. Exact paper source: paper.tex, Lemma 3.2, the gradient formula for
   F_L(z)=|L e-z|^(-kappa), and the coefficient
   kappa L^(-kappa-1) e dot (x+y).
4. Promotion event: tie the linear field to inner direction and derive
   hlineDeriv from translatedCrossLine_hasDerivAt_zero at t=0.  The
   acceptance check is the unchanged FinalTheoremL2 caller build.

The remaining analytic field after this integration is hlineSecond, the
second-derivative bound with radial factor kappa(kappa+1).

### Acceptance repair — first line derivative caller

The first caller replay failed in L2TwoWellAux.toSpectralInput before the
second-derivative hypothesis was used.  The inner-product instance required by
translatedCrossLine_hasDerivAt_zero was absent from L2TwoWellAux; the
zero-norm contradiction compared L = 0 with 0 = L; and the derivWithin
identity was rewritten syntactically although its left side did not match the
displayed goal.  These are interface and proof-shape repairs only.  The paper
source, derivative supplier, and acceptance check are unchanged.

### Promotion stalled — first line derivative receipt

The first line derivative receipt now has two consecutive uncredited
acceptance checks.  The first failed on the missing inner-product instance,
the reversed zero-norm equality, and the syntactic derivWithin rewrite.  The
second reached the derivative chain but failed because NormedSpace and
InnerProductSpace supplied competing real-module instances; the resulting
Eq.trans had mismatched translatedCrossLine instances, and FinalTheoremL2
still exposed only NormedSpace.  The receipt is closed as promotion stalled.

#### Spine reset

- Paper formula: the derivative at zero of
  |L e - t(x+y)|^(-kappa) is
  kappa |L e|^(-kappa-2) inner(L e, x+y).
- Current Lean type: L2TwoWellAux carries both NormedSpace and
  InnerProductSpace, while translatedCrossLine elaborates through their
  competing Module instances.
- Proposed bridge: use InnerProductSpace as the sole source of the real
  module structure and derive the derivWithin equality through one shared
  instance.
- Smallest identity test: the derivWithin equation for translatedCrossLine
  must elaborate on both sides with the same Module Real X instance.
- Theorem slot: hlineDeriv consumed by
  L2TwoWellAux.toSpectralInput.htApprox.

## 2026-09-24 — inner-product instance coherence

1. Named final-facing theorem: FinalTheoremL2.
2. Immediate Lean consumer: L2TwoWellAux.toSpectralInput.htApprox through
   hlineDeriv.
3. Exact paper source: paper.tex, Lemma 3.2, the gradient formula for
   F_L(z)=|L e-z|^(-kappa), and the coefficient
   kappa L^(-kappa-1) e dot (x+y).
4. Promotion event: replace the redundant NormedSpace parameter by
   InnerProductSpace, align FinalTheoremL2 with that instance, and chain the
   derivWithin identity through the shared real-module structure.  The
   acceptance check is the unchanged FinalTheoremL2 caller build.

### Acceptance result

FinalTheoremL2 compiled after the inner-product instance coherence repair.
This credits the first line derivative and its caller consumption: hlineDeriv
is now derived at t=0 from translatedCrossLine_hasDerivAt_zero, with linear
tied to inner direction.  The first missing analytic supplier is the exact
second derivative formula and bound for translatedCrossLine, discharging
hlineSecond.

## 2026-09-25 — second derivative of the separated kernel line

1. Named final-facing theorem: FinalTheoremL2.
2. Immediate Lean consumer: L2TwoWellAux.toSpectralInput.htApprox through
   hlineSecond and the derived hTaylorBound.
3. Exact paper source: paper.tex, Lemma 3.2, the Hessian formula
   ∇²F_L(z)=κ|L e-z|^(-κ-2)((κ+2)n_z⊗n_z-I), and the bound
   ||∇²F_L(z)||=κ(κ+1)|L e-z|^(-κ-2).
4. Promotion event: derive the scalar second derivative of
   ‖c-t z‖^(-κ), convert it to iteratedDerivWithin 2 on the interval, and
   bound its absolute value by κ(κ+1)|c-t z|^(-κ-2)‖z‖².  The acceptance
   check is the unchanged FinalTheoremL2 caller build.

The bridge uses the quadratic squared-norm line and the exact formula
f''(t)=κ(κ+2)|w|^(-κ-4)⟪w,z⟫²-κ|w|^(-κ-2)‖z‖², whose Cauchy-Schwarz
bound is κ(κ+1)|w|^(-κ-2)‖z‖².

### Acceptance repair — line integration

The first caller replay failed in toSpectralInput.htApprox before the
analytic hypotheses were tested.  The endpoint rewrite for translatedCrossLine
was hidden behind the local definition g; the scalar normalization goal was
already closed by field_simp before the trailing ring tactic; and the
remainder rearrangement used the unqualified projection linear, which Lean
resolved to the L2TwoWellAux structure rather than aux.linear.  These are
representation repairs only.  The paper source, supplier theorem, and
acceptance check remain unchanged.

### Acceptance repair — scalar second-derivative product shape

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.htApprox` through `hlineSecond` and the
   derived `hTaylorBound`.
3. Exact paper source: paper.tex, Lemma 3.2, the Hessian formula for
   `F_L(z)=|L e-z|^{-kappa}`, including the scalar identity
   `f''(t)=p(p-2)|c-t z|^{p-4}<c-t z,z>^2+p|c-t z|^{p-2}|z|^2` at `p=-kappa`.
4. Promotion event: repair `norm_sub_smul_second_deriv` by giving
   `HasDerivAt.inner` its scalar field explicitly, normalizing the radial
   exponent `(p-2)-2=p-4`, and congruence-normalizing the differentiated
   product function before applying the scalar product rule.  The acceptance
   check remains the unchanged `FinalTheoremL2` caller build.

The first supplier compile reached `norm_sub_smul_second_deriv` but failed on
the implicit scalar-field argument of `HasDerivAt.inner` and on the function
shape emitted by `HasDerivAt.const_mul`.  This is a representation repair to
the exact paper derivative formula, not a change of theorem scope or source.

### Acceptance repair — explicit product function

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.htApprox` through `hlineSecond` and
   `hTaylorBound`.
3. Exact paper source: paper.tex, Lemma 3.2, the same scalar second-derivative
   identity for `|L e-z|^{-kappa}`.
4. Promotion event: state `hprod` and `hsecondExpr` on the explicit pointwise
   product function `s ↦ ‖c-s•z‖^(p-2) * inner (c-s•z) z`, so the generated
   derivative is syntactically available to the final rewrite.  The acceptance
   check remains the unchanged `FinalTheoremL2` caller build.

## 2026-09-25 — sharp second-derivative bound and source constant

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.htApprox`, through `hlineSecond` and the
   derived `hTaylorBound`.
3. Exact paper source: paper.tex, Lemma 3.2, the Hessian formula and the
   displayed value `C_{κ,R}=2^{κ+3}κ(κ+1)R²` in `eq:kernel-expansion`.
4. Promotion event: derive the exact second derivative of
   `translatedCrossLine`, prove its sharp absolute bound
   `κ(κ+1)‖c-tz‖^{-κ-2}‖z‖²`, specialize it to the separated geometry
   `‖c-tz‖≥L/2`, `‖x+y‖≤2R`, and replace the raw `hlineSecond` field by that
   derived estimate.  The acceptance check remains the unchanged
   `FinalTheoremL2` caller build.

This edit also replaces the free positive `C` field in `TwoWellConstants` by
the paper's exact source value, so the final theorem has no free
project-defining constant.  The derived bound is
`2^{κ+4}κ(κ+1)R² L^{-κ-2}=2 C_{κ,R}L^{-κ-2}`, exactly the constant consumed by
`scalar_taylor_remainder_bound` before its division by two.

### Acceptance repair — real base for the source constant

The first constant compile inferred `2` through `HPow ℕ ℝ ℕ`, so the real
power expression did not elaborate.  This repair makes the base explicitly
`(2:ℝ)` and supplies the positivity facts for `κ`, `κ+1`, and `R^2`; the
paper constant, consumer, and acceptance check are unchanged.

### Acceptance repair — sign normalization in the line formula

The specialized translated-line second derivative reached the scalar
identity but retained the raw factor `-(κ*(κ+2))` instead of the displayed
paper factor `κ(κ+2)`.  This repair rewrites through
`norm_sub_smul_second_deriv` and closes only the resulting real-algebra
equality with `ring`; the theorem statement, source formula, consumer, and
acceptance check are unchanged.

### Acceptance integration — derive `hlineSecond`

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.htApprox`, through the derived
   `hTaylorBound`.
3. Exact paper source: paper.tex, Lemma 3.2, the Hessian estimate and the
   separation argument `|Le-z|≥L/2`, `|z|≤2R`.
4. Promotion event: replace the raw `hlineSecond` field by a proof obtained
   from `translatedCrossLine_second_deriv_abs_le`,
   `iteratedDerivWithin_eq_iteratedDeriv`, and the explicit source constant
   `C_{κ,R}=2^{κ+3}κ(κ+1)R²`.  The acceptance check is the unchanged
   `FinalTheoremL2` caller build.

### Acceptance repair — caller projections and source-constant unfolding

The first `hlineSecond` caller replay failed on two stale local names,
`aux.hY` instead of `aux.hX`, and on rewriting the definition `A.C` before
the imported supplier was rebuilt.  This repair uses the existing radius
field for both points, unfolds `A.C` through an explicit definitional
equality, and rebuilds `FractionalForm` before replaying `FinalTheoremL2`.
The theorem statement, source estimate, consumer, and acceptance check are
unchanged.

### Acceptance repair — transitivity direction in the second-derivative bound

The caller replay reached the final bound chain but attempted to rewrite the
intermediate geometric estimate after the goal had already reverted to the
original derivative expression.  This repair composes `hprod.trans hconst.le`
directly.  The paper estimate, theorem statement, consumer, and acceptance
check are unchanged.

### Acceptance result — second-derivative theorem slot

`Tunneling.Final` rebuilt successfully after deriving `hlineSecond` from
`translatedCrossLine_second_deriv_abs_le`, the interval iterated-derivative
bridge, and the explicit source constant `C_{κ,R}`.  The raw `hlineSecond`
field has been removed from `L2TwoWellAux`, and the unchanged
`FinalTheoremL2` caller consumes the derived estimate through `hTaylorBound`.
This closes the second-derivative theorem slot.  The remaining Lean work is
the construction of the one-well spectral data and its source bridges, plus
the multi-well and Hong--Krahn--Szegő/numerical parts of the paper theorem.

## 2026-09-25 — smoothness of the separated kernel line

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.htApprox`, through `hTaylorBound` and the
   iterated-derivative bridge used by `hlineSecond`.
3. Exact paper source: paper.tex, Lemma 3.2, smoothness of
   `F_L(z)=|L e-z|^{-κ}` on the separated segment and the Taylor argument.
4. Promotion event: derive `ContDiffOn ℝ 2` for `translatedCrossLine` from
   the affine line map, `ContDiffOn.norm`, and
   `ContDiffOn.rpow_const_of_ne`, then remove the raw `hlineContDiff` field
   from `L2TwoWellAux`.  The acceptance check is the unchanged
   `FinalTheoremL2` caller build.

### Acceptance repair — scalar field for `ContDiffOn.norm`

The smoothness supplier reached `ContDiffOn.norm` but its scalar field was
left implicit, so Lean treated the nonvanishing proof as the type argument.
This repair supplies `𝕜 := ℝ` explicitly.  The theorem statement, paper
source, consumer, and acceptance check are unchanged.

### Acceptance result — line smoothness theorem slot

`Tunneling.Final` rebuilt successfully after deriving `hlineContDiff` from
`translatedCrossLine_contDiffOn` and the full-segment separation estimate.
The raw `hlineContDiff` field has been removed from `L2TwoWellAux`, and the
unchanged `FinalTheoremL2` caller consumes the derived smoothness through the
Taylor and iterated-derivative arguments.  This closes the line-smoothness
theorem slot.  The remaining Lean work is the one-well spectral construction,
the Taylor remainder representation and integrability bridges, and the
multi-well and Hong--Krahn--Szegő/numerical parts of the paper theorem.

## 2026-09-25 — exact Taylor remainder representation

1. Named final-facing theorem: FinalTheoremL2.
2. Immediate Lean consumer: L2TwoWellAux.toSpectralInput.htApprox through
   hTaylorBound and interactionMass_taylor_remainder.
3. Exact paper source: paper.tex, Lemma 3.2 and equation eq:kernel-expansion,
   where the remainder is the difference between the translated kernel and
   its constant plus linear Taylor polynomial.
4. Promotion event: replace the arbitrary remainder field and hTaylorDecomp
   identity by the exact named function twoWellTaylorRemainder and its
   decomposition theorem.  The acceptance check is the unchanged
   FinalTheoremL2 caller build.

## 2026-09-25 — derive beta nonnegativity

1. Named final-facing theorem: FinalTheoremL2.
2. Immediate Lean consumer: TwoWellSpectralInput and
   L2TwoWellAux.toSpectralInput, through hBnorm and the perturbation
   estimates.
3. Exact paper source: paper.tex, Lemma 3.2 and equation eq:Bnorm, where
   beta_L=c_{d,s}2^κ|D|L^{-κ} for positive separation L.
4. Promotion event: derive nonnegativity of beta_L from the positive source
   constants and L ≥ 0, restrict the statement to the nonnegative separations
   used by the theorem, and remove the raw hbetaNonneg field.  The acceptance
   check is the unchanged FinalTheoremL2 caller build.

### Acceptance repair — explicit beta product factors

The beta_nonneg proof reached the final positivity step, but A.beta is a
noncomputable product and positivity did not synthesize its real-power
factors.  This repair unfolds the definition and applies mul_nonneg explicitly
to A.hc, A.hvolumeD, Real.rpow_nonneg, and L ≥ 0.  The source statement,
consumer, and acceptance check are unchanged.

### Acceptance result — beta nonnegativity

`TwoWellConstants.beta_nonneg` is accepted by the full `lake build` after the
explicit factorization repair.  The unchanged `FinalTheoremL2` caller consumes
it in `toSpectralInput.hBnorm` and the perturbation estimates.  The audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` remains empty.

## 2026-09-25 — limiting gap from branch expansions

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `FinalTheorem`'s `gapLimit` conclusion and the corresponding
   `L2TwoWellAux.hgapLimit` constructor field.
3. Exact paper source: `paper.tex`, Theorem 3.3 and equation `eq:gap-limit`,
   obtained by subtracting `eq:lambda1` and `eq:lambda2` and multiplying by
   `L^{d+2s}`.
4. Promotion event: derive `A.gapLimit S.lambda` from
   `hbranchPlus`, `hbranchMinus`, `htApprox`, the two branch stability bounds,
   and `beta_L = O(L^{-kappa})`, then remove the raw `hgapLimit` fields and
   replay the unchanged `FinalTheoremL2` caller build.

### Promotion stalled — limiting gap

The limiting-gap receipt has two consecutive failed acceptance checks.  The
first reached the branch subtraction but failed on real-power and absolute-
value representation.  The repaired proof reached the final bound but failed
on the `L^kappa L^{-kappa}` normalization, the branch symmetry projection,
the final error comparison, and the `Tendsto`/squeeze names.  This receipt is
closed as promotion stalled.

Spine reset:

- Paper formula: equation `eq:gap-limit`,
  `L^kappa (lambda_L,2-lambda_L,1) -> 2 c_{d,s} m_1^2`.
- Current Lean type:
  `Filter.Tendsto (fun L : ℝ => L ^ A.kappa *
    (S.lambda L 1 - S.lambda L 0)) Filter.atTop
    (nhds (2 * A.c * A.phiMass ^ 2))`.
- Proposed bridge domain/codomain: branch energies and `S.t L` on
  `[A.L0, infinity)` to real error bounds tending to zero.
- Smallest identity test:
  `L^kappa * (S.lambda L 1 - S.lambda L 0) - 2*A.c*A.phiMass^2`
  is bounded by the sum of the `t_L` Taylor error and the two perturbation
  remainders.
- Theorem slot: `FinalTheoremL2` conclusion `A.gapLimit`.

## 2026-09-26 — quadratic gap from the orthogonal complement

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.hgapEnergy`, consumed by
   `L2TwoWellAux.toSpectralInput.hgapq` and then `Tunneling.FinalTheorem`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, and the
   orthogonal decomposition in the proof of Lemma 3.1, where the lower bound
   on `phi_1^perp` implies the normalized gap inequality.
4. Promotion event: replace the raw `hgapEnergy` field by the orthogonal-
   complement bound `hgapOrth` and derive `hgapEnergy` from the quadratic
   polarization identity and the residual norm identity.
5. Sole credit expected: caller-consumed quadratic spectral-gap bridge.  The
   ground-state first-variation identity and the one-well operator remain
   separate obligations.

### Acceptance check

Build `Tunneling.Final`, replay `FinalTheoremL2`, and run the literal and
`#print axioms` audits.  The promotion is accepted only when `hgapq` is
derived from `hgapOrth` in the unchanged caller.

### Acceptance result — quadratic gap from the orthogonal complement

The focused `Tunneling.Perturbation` build and the full package replay pass
after rebuilding the imported interface.  `L2TwoWellAux.hgapEnergy` is now
derived by `quadratic_gap_of_polar` from `hgroundPolar` and `hgapOrth`, and
`FinalTheoremL2` consumes it through `hgapq`.  This earns only the quadratic
spectral-gap bridge; the ground-state first-variation identity and one-well
operator remain open.

## 2026-09-26 — ground-state first variation

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.hgroundPolar`, consumed by
   `L2TwoWellAux.hqEnergyGroundAdd` and `hgapEnergy`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, and the
   variational characterization of the first eigenfunction, specialized to
   the quadratic energy `Q` on the unit sphere.
4. Promotion event: replace the raw `hgroundPolar` field by the source-level
   minimization property `hgroundMin`, and derive vanishing of the polar form
   against every `L²`-orthogonal direction from the exact quadratic
   polarization identity.
5. Sole credit expected: caller-consumed ground-state first-variation bridge.
   The one-well operator, compact-resolvent construction, and remaining
   source fields stay separate.

### Acceptance check

Build `Tunneling.Final`, replay `FinalTheoremL2`, and run the literal and
`#print axioms` audits.  The promotion is accepted only when `hgroundPolar`
is derived from `hgroundMin` in the unchanged caller.

### Acceptance result — ground-state first variation

The focused `Tunneling.Perturbation` build and the full package replay pass.
`L2TwoWellAux.hgroundPolar` is now derived by
`quadratic_polar_zero_of_min_unit_sphere` from `hgroundMin`, and the unchanged
`FinalTheoremL2` caller consumes it through `hqEnergyGroundAdd` and
`hgapEnergy`.  This earns only the first-variation bridge; the source-level
ground-state minimization and spectral-gap estimates remain open.

## 2026-09-26 — source-level spectral gap interface

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.hgapEnergy`, consumed by
   `L2TwoWellAux.hgapq` and `toSpectralInput.hgapq`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, and the
   spectral lower bound in Lemma 3.1.
4. Promotion event: replace the pair `hgroundMin` and `hgapOrth` by the single
   source-level normalized gap estimate `hgapEnergy`, derive both the polar
   first-variation identity and the orthogonal-complement bound from it, and
   replay `FinalTheoremL2`.
5. Sole credit expected: caller-consumed source-level spectral-gap bridge.  The
   construction of this estimate from the restricted fractional operator
   remains the next analytic obligation.

### Acceptance check

Build `Tunneling.Final`, replay `FinalTheoremL2`, and run the literal and
`#print axioms` audits.  The promotion is accepted only when both
`hgroundPolar` and `hgapOrth` are derived from `hgapEnergy` in the unchanged
caller.

## 2026-09-26 — primitive one-well spectral interface

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.hgapEnergy`, consumed by
   `L2TwoWellAux.hgapq` and `toSpectralInput.hgapq`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, the
   variational characterization of `phi_1`, and the orthogonal spectral gap
   used in Lemma 3.1.
4. Promotion event: replace the combined raw gap field `hgapEnergySource` by
   the primitive source fields `hgroundMinSource` and `hgapOrthSource`, derive
   `hgroundPolar` from minimization and `hgapEnergy` from the quadratic gap
   lemma, and replay `FinalTheoremL2`.
5. Sole credit expected: caller-consumed primitive one-well spectral interface.
   Construction of `hgroundMinSource` and `hgapOrthSource` from the restricted
   fractional form remains the next analytic obligation.

### Acceptance check

Build `Tunneling.Final`, replay `FinalTheoremL2`, and run the literal and
`#print axioms` audits.  The promotion is accepted only when `hgapEnergy` is
derived from the two primitive fields in the unchanged caller.

### Acceptance result — primitive one-well spectral interface

The focused `Tunneling.Final` build and the full package replay pass.  The
unchanged `FinalTheoremL2` caller consumes `hgroundMinSource` and
`hgapOrthSource` through the derived `hgroundPolar`, `hgapEnergy`, and
`hgapq` theorems.  This earns only the primitive spectral-interface bridge;
construction of the two source fields from the restricted fractional form
remains open.

## 2026-09-26 — eigen-equation first-variation interface

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.hgroundPolar`, consumed by
   `L2TwoWellAux.hqEnergyGroundAdd`, `hgapEnergy`, and `toSpectralInput.hgapq`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, where the
   eigen-equation `A_D phi_1 = mu_1 phi_1` gives vanishing first variation on
   the orthogonal complement.
4. Promotion event: replace the raw global-minimization field
   `hgroundMinSource` by the source-level first-variation field
   `hgroundPolarSource`, derive `hgroundMin` from the normalized gap, and
   replay `FinalTheoremL2`.
5. Sole credit expected: caller-consumed eigen-equation first-variation
   interface.  Construction of `hgroundPolarSource` and `hgapOrthSource` from
   the restricted fractional form remains the next analytic obligation.

### Acceptance check

Build `Tunneling.Final`, replay `FinalTheoremL2`, and run the literal and
`#print axioms` audits.  The promotion is accepted only when `hgroundMin` is
derived from `hgroundPolarSource` and `hgapOrthSource` in the unchanged
caller.

## 2026-09-26 — promotion receipt `kernel-measurability-2026-09-26`

1. Structural bucket and milestone capstone: restricted-fractional one-well
   source extraction feeding `Tunneling.FinalTheoremL2`; the capstone remains
   the caller-consumed two-well theorem.
2. Exact paper source and first unconsumed spine theorem: `paper.tex`,
   Section 2, equation `eq:form`, where the Gagliardo kernel
   `|x-y|^(-kappa)` is the measurable singular kernel of the zero-exterior
   form.  The Lean statement is measurability of
   `fun z : X × X => gagliardoKernel kappa z.1 z.2` on the product measure.
3. Supplier and immediate compiled consumer: a derived kernel-measurability
   theorem in `lean/Tunneling/FractionalForm.lean`, consumed by the
   finite-energy submodule and `restrictedZeroExteriorForm` used in
   `L2TwoWellAux`; the raw `hK` field is removed from that structure.
4. Acceptance check: build `Tunneling.Final`, replay `FinalTheoremL2`, and
   run the literal and `#print axioms` audits.
5. Sole credit expected: caller-consumed measurable singular-kernel bridge.
   The one-well operator, spectral gap, minimizer, fractional block
   reduction, and compression theorem remain separate obligations.

### Acceptance result — `kernel-measurability-2026-09-26`

The first focused attempt failed because `measurable_sub` could not synthesize
`MeasurableSub₂ X`; the repaired proof measures the real-valued composite
`z ↦ ‖z.1 - z.2‖` directly via `continuous_norm.comp continuous_sub`, then
uses `Measurable.pow_const` and `Measurable.aestronglyMeasurable`.  The raw
`hK` field has been removed from `L2TwoWellAux`, and the finite-energy source
form instantiates the derived
`gagliardoKernel_aestronglyMeasurable` theorem.  The focused source and final
caller checks pass, and the full package build is
`Build completed successfully (2968 jobs)` in `build-kernel-full.log`.  The
literal `axiom`/`sorry` audit is empty, and `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for `FinalTheorem`,
`FinalTheoremL2`, and `FinalTheoremMultiWell`.  Sole credit accepted:
caller-consumed measurable singular-kernel bridge.  The form-domain/operator
construction, spectral gap, minimizer, fractional block reduction, and
compression theorem remain open.

## 2026-09-26 — promotion receipt `finite-energy-form-domain-2026-09-26`

1. Structural bucket and milestone capstone: the restricted-fractional
   one-well form-domain bridge feeding `Tunneling.FinalTheoremL2`; the
   capstone remains the caller-consumed two-well theorem.
2. Exact paper source and first unconsumed spine theorem: `paper.tex`,
   Section 2, equation `eq:form`, where the form domain is the finite-energy
   space `H^s(D)` and the Rayleigh form is evaluated on its `L²`
   representative.  The Lean statement is a linear `toLp` map from
   `finiteGagliardoEnergySubmodule` followed by a quadratic map on `L²` whose
   restriction agrees with `restrictedZeroExteriorForm`.
3. Supplier and immediate compiled consumer: `finiteGagliardoEnergy.toLp`
   linearity and the induced retraction in `lean/Tunneling/FractionalForm.lean`,
   consumed by `L2TwoWellAux.hsourceForm` and its derived `hφEnergyValue` in
   `lean/Tunneling/Final.lean`.
4. Acceptance check: replace the raw `hsourceForm` compatibility field by a
   derived theorem from the constructed form-domain map, build
   `Tunneling.Final`, replay `FinalTheoremL2`, and run the literal and
   `#print axioms` audits.
5. Sole credit expected: caller-consumed finite-energy form-domain bridge.
   The one-well operator, spectral gap, minimizer, fractional block
   reduction, and compression theorem remain separate obligations.

## 2026-09-26 — promotion receipt `source-ground-energy-2026-09-26`

1. Structural bucket and milestone capstone: restricted-fractional one-well
   source extraction feeding `Tunneling.FinalTheoremL2`; the capstone remains
   the caller-consumed two-well theorem.
2. Exact paper source and first unconsumed spine theorem: `paper.tex`,
   Section 2, equations `eq:form`, `eq:mass`, and the definition of
   `lambda_1(D)`, specialized to the canonical finite-energy ground-state
   representative.
3. Supplier and immediate compiled consumer: `restrictedZeroExteriorForm` in
   `lean/Tunneling/FractionalForm.lean`, consumed by a source-compatibility
   field in `L2TwoWellAux`, its derived `hφEnergyValue`, and
   `L2TwoWellAux.toSpectralInput`.
4. Acceptance check: replace the raw `hφEnergyValue` field by source-form
   equality and compatibility, build `Tunneling.Final`, replay
   `FinalTheoremL2`, and run the literal and `#print axioms` audits.
5. Sole credit expected: caller-consumed restricted-form ground-energy
   extraction.  The one-well operator, spectral gap, minimizer, fractional
   block reduction, and compression theorem remain separate obligations.

### Acceptance result — `source-ground-energy-2026-09-26`

`L2TwoWellAux.hφEnergyValue` is now a theorem derived from compatibility with
`restrictedZeroExteriorForm` on the finite-energy submodule and the source
energy of the canonical `phiRaw` representative.  The raw ground-energy
equality field has been removed.  The focused `Tunneling.Final` check and the
full package replay pass (`Build completed successfully (2968 jobs)` in
`build-source-ground-full.log`), the literal `axiom`/`sorry` audit is empty,
and `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for `FinalTheorem`,
`FinalTheoremL2`, and `FinalTheoremMultiWell`.  Sole credit accepted:
caller-consumed restricted-form ground-energy extraction.  The all-`L²` form
domain mismatch, one-well operator, spectral gap, minimizer, fractional block
reduction, and compression theorem remain open.

## 2026-09-26 — promotion receipt `polar-ground-cross-2026-09-26`

1. Structural bucket and milestone capstone: the restricted-fractional
   one-well spectral interface feeding `Tunneling.FinalTheoremL2`; the
   capstone remains the caller-consumed two-well theorem.
2. Exact paper source and first unconsumed spine theorem: `paper.tex`,
   Section 2, equation `eq:form`, together with the orthogonal decomposition
   in the proof of Lemma 3.1.  The Lean statement replaces the raw equality
   field in `L2TwoWellAux` by vanishing of
   `QuadraticMap.polar (fun u => oneWellForm u) (t • phiRaw) r` whenever
   `inner ℝ phiRaw r = 0`.
3. Supplier and immediate compiled consumer: the new polar field and its
   derived ground-line additivity theorem in `lean/Tunneling/Final.lean`,
   consumed by `L2TwoWellAux.toSpectralInput` and then `FinalTheoremL2`.
4. Acceptance check: build `Tunneling.Final` and replay `FinalTheoremL2` with
   the unchanged caller hypotheses, then run the literal and `#print axioms`
   audits.
5. Sole credit expected: caller-consumed source-faithful ground-state polar
   orthogonality bridge.  The one-well operator, spectral gap, minimizer, and
   block reduction remain separate obligations.

### Acceptance result — `polar-ground-cross-2026-09-26`

The first focused replay found one representative mismatch: `linarith` saw
`aux.φ` in the derived goal and the explicit
`finiteGagliardoEnergy.toLp` representative in the polar hypothesis.  After
normalizing both terms to that representative, `Tunneling.Final` compiles.
The full replay is `Build completed successfully (2968 jobs)` in
`build-polar-full.log`; the literal `axiom`/`sorry` audit is empty; and
`#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for
`FinalTheorem`, `FinalTheoremL2`, and `FinalTheoremMultiWell`.  The raw
ground-line equality field has been removed from `L2TwoWellAux`, and
`toSpectralInput` consumes the derived additivity theorem.  Sole credit
accepted: caller-consumed source-faithful ground-state polar orthogonality
bridge.  The one-well finite-energy form/operator construction, spectral gap,
minimizer, fractional block reduction, and compression theorem remain open.

## 2026-09-26 — quadratic one-well energy acceptance

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through the
   `hqHomogeneous` field consumed by `FinalTheorem`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:form`, where the
   one-well Rayleigh energy is a quadratic form.
4. Promotion event completed: package `oneWellEnergy` as `oneWellForm`, a
   `QuadraticMap`, derive `hqEnergyHomogeneous` from
   `QuadraticMap.map_smul`, and replay the unchanged `FinalTheoremL2` caller.

### Acceptance result — quadratic one-well energy interface

`L2TwoWellAux.oneWellEnergy` is now represented by
`oneWellForm : QuadraticMap ℝ (MeasureTheory.Lp ℝ 2 mu) ℝ`.  The homogeneity
law is derived from `QuadraticMap.map_smul` and consumed by
`toSpectralInput`; the raw `hqEnergyHomogeneous` field has been removed.  The
full `lake build` passes (`Build completed successfully (2968 jobs)`), the
literal audit is empty, and `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for `FinalTheorem`,
`FinalTheoremL2`, and `FinalTheoremMultiWell`.  Sole credit accepted:
caller-consumed quadratic one-well energy interface.  The ground-state energy
value, spectral gap, and minimizer construction remain open.

## 2026-09-26 — quadratic one-well energy interface

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through the
   `hqHomogeneous` field consumed by `FinalTheorem`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:form`, where the
   one-well Rayleigh energy is a quadratic form.
4. Promotion event: package `oneWellEnergy` as a `QuadraticMap`, derive its
   scalar homogeneity from `QuadraticMap.map_smul`, and replay the unchanged
   `FinalTheoremL2` caller.
5. Sole credit expected: caller-consumed quadratic one-well energy interface.
   The operator realization, spectral gap, and minimizer construction remain
   separate obligations.

## 2026-09-26 — exact L2 mass and normalization identities

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through the
   `hφ` and `hmass` data consumed by `FinalTheorem` and the Taylor mass term.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, where the
   normalized ground state is an `L²` class and `m_1` is its integral.
4. Promotion event completed: replace the raw `eLpNorm φRaw` and `∫ φRaw`
   fields by normalization and mass identities for the canonical
   `finiteGagliardoEnergy.toLp` class, and replay the unchanged
   `FinalTheoremL2` caller.

### Acceptance result — exact L2 mass and normalization identities

`L2TwoWellAux` now states `‖finiteGagliardoEnergy.toLp ...‖ = 1` and the
mass integral of that canonical `L²` class directly.  The derived `hφ` and
`hmass` theorems consume those fields, and the raw `eLpNorm` and integral
assumptions have been removed.  The focused `Tunneling.Final` build and full
`lake build` pass (`Build completed successfully (2968 jobs)`).  The literal
audit `rg -n '^\s*(axiom|sorry)\b' Tunneling` is empty, and `#print axioms`
reports only `[propext, Classical.choice, Quot.sound]` for `FinalTheorem`,
`FinalTheoremL2`, and `FinalTheoremMultiWell`.  Sole credit accepted:
caller-consumed exact `L²` mass/normalization bridge.  The one-well operator,
spectral gap, and minimizer construction remain open.

## 2026-09-26 — exact L2 mass and normalization identities

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through the
   `hφ` and `hmass` data consumed by `FinalTheorem` and the Taylor mass term.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, where the
   normalized ground state is an `L²` class and `m_1` is its integral.
4. Promotion event: replace the raw `eLpNorm φRaw` and `∫ φRaw` fields by
   normalization and mass identities for the canonical
   `finiteGagliardoEnergy.toLp` class, and replay the unchanged
   `FinalTheoremL2` caller.
5. Sole credit expected: caller-consumed exact `L²` mass/normalization bridge.
   The one-well operator, spectral gap, and minimizer construction remain
   separate obligations.

## 2026-09-26 — exact L2 mass and normalization identities

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through the
   `hφ` and `hmass` data consumed by `FinalTheorem` and the Taylor mass term.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, where the
   normalized ground state is an `L²` class and `m_1` is its integral.
4. Promotion event: replace the raw `eLpNorm φRaw` and `∫ φRaw` fields by
   normalization and mass identities for the canonical
   `finiteGagliardoEnergy.toLp` class, derive any representative facts from
   those identities where required, and replay the unchanged
   `FinalTheoremL2` caller.
5. Sole credit expected: caller-consumed exact `L²` mass/normalization bridge.
   The one-well operator, spectral gap, and minimizer construction remain
   separate obligations.

## 2026-09-26 — exact L2 mass and normalization identities

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through the
   `hφ` and `hmass` data consumed by `FinalTheorem` and the Taylor mass term.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, where the
   normalized ground state is an `L²` class and `m_1` is its integral.
4. Promotion event: replace the raw `eLpNorm φRaw` and `∫ φRaw` fields by
   normalization and mass identities for the canonical
   `finiteGagliardoEnergy.toLp` class, derive any representative facts from
   those identities, and replay the unchanged `FinalTheoremL2` caller.
5. Sole credit expected: caller-consumed exact `L²` mass/normalization bridge.
   The one-well operator, spectral gap, and minimizer construction remain
   separate obligations.

## 2026-09-26 — canonical finite-energy ground-state representative

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through the
   `φ`, `hφ`, `hmass`, `heven`, and `hnonneg` data.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, where the
   normalized positive ground state is represented by its finite-energy
   zero-exterior function and its `L²` class.
4. Promotion event completed: make `L2TwoWellAux.φ` the canonical
   `finiteGagliardoEnergy.toLp` image of `φRaw`, remove the raw `φ`/`hφEq`
   fields, and replay `FinalTheoremL2`.

### Acceptance result — canonical finite-energy ground-state representative

`L2TwoWellAux.φ` is now defined directly as
`finiteGagliardoEnergy.toLp A.kappa mu Set.univ φRaw hφEnergy`; the raw `φ`
and `hφEq` fields have been removed.  The representative equalities, norm,
mass, evenness, and nonnegativity fields now refer to this canonical `L²`
class, and the unchanged `FinalTheoremL2` caller consumes the derived
projection.  The focused `Tunneling.Final` build and full `lake build` pass
(`Build completed successfully (2968 jobs)`), the literal audit is empty,
and `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`
for `FinalTheorem`, `FinalTheoremL2`, and `FinalTheoremMultiWell`.  Sole
credit accepted: caller-consumed finite-energy ground-state representative
bridge.  The one-well operator, spectral gap, and minimizer construction
remain open.

## 2026-09-26 — rescaled multi-well error limit acceptance

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: the former `herr` argument of
   `multiWellLimit_of_conclusion`, now supplied by
   `multiWellRescaledError_tendsto_zero` inside `FinalTheoremMultiWell`.
3. Exact paper source: `paper.tex`, Theorem 4.3 and its final paragraph,
   equation `eq:multi-limit`.
4. Promotion event completed: prove that the explicit rescaled error tends
   to zero and remove the `herr` binder from `FinalTheoremMultiWell`.

### Acceptance result — rescaled multi-well error limit

`multiWellRescaledError_tendsto_zero` proves the exact limit from the power
laws in `multiWellEpsilon` and `multiWellGamma`:
`L^A.kappa * multiWellEpsilon A a L` is a constant multiple of `L^(-2)`, and
`L^A.kappa * multiWellGamma A a L ^ 2 / A.gap` is a constant multiple of
`L^(-A.kappa)`, where `0 < A.kappa`.  `FinalTheoremMultiWell` now consumes
this theorem directly and no longer exposes the error-limit hypothesis.  The
focused `Tunneling.MultiWell` build and full `lake build` pass
(`Build completed successfully (2968 jobs)`).  The literal audit
`rg -n '^\s*(axiom|sorry)\b' Tunneling` is empty, and `#print axioms` reports
only `[propext, Classical.choice, Quot.sound]` for `FinalTheorem`,
`FinalTheoremL2`, and `FinalTheoremMultiWell`.  Sole credit accepted:
caller-consumed rescaled-error limit.

The analytic fractional block reduction and the restricted fractional
one-well spectral construction remain open.  The current final theorems use
their explicit spectral/form interfaces as hypotheses; this acceptance does
not claim either analytic construction has been formalized.

### Acceptance result — finite multi-well capstone source extraction

`Tunneling.MultiWell` now records `sigmaKappa`, `multiWellGamma`,
`multiWellEpsilon`, `multiWellConclusion`, `multiWellLimit`, and
`multiWellStatement` from paper Theorem 4.3, together with the caller-facing
algebraic implication `multiWellLimit_of_conclusion`.  The focused build and
the full `lake build` both pass (`Build completed successfully (2968 jobs)`).
The literal audit remains empty, and `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for `FinalTheorem` and
`FinalTheoremL2`.  This accepts finite multi-well source extraction and the
limiting algebra only; the block reduction, cluster perturbation, and
compression-error proof remain open.

## 2026-09-26 — isolated spectral-cluster bound

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: `Tunneling.FinalTheoremMultiWell`, through the
   multi-well eigenvalue and cluster-edge conclusions in
   `multiWellConclusion`.
3. Exact paper source: `paper.tex`, Lemma 4.2, equations
   `eq:cluster-bound` and `eq:cluster-separation`, with the min--max argument
   in its proof.
4. Promotion event: formalize the finite-multiplicity perturbation estimate
   for an isolated spectral cluster, using the compressed perturbation
   eigenvalues and the supplied form gap, and expose the exact bounds consumed
   by the finite multi-well theorem.
5. Sole credit expected: caller-consumed isolated spectral-cluster estimate.
   The fractional block unitary and compression matrix remain separate.

## 2026-09-26 — finite-energy one-well representative bridge

1. Structural bucket and milestone capstone: restricted fractional one-well
   spectral construction, culminating in `Tunneling.FinalTheoremL2`.
2. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, including
   the normalized positive ground state and the mass identity
   `m_1 = integral_D phi_1(x) dx`.  Exact first Lean statement:
   map `u` with `finiteGagliardoEnergy kappa mu G u` to the `L²` class of
   `zeroExtension G u`, identify its almost-everywhere representative and
   norm, and transport the pointwise mass integral to that class.
3. Supplying file and immediate compiled consumer:
   `Tunneling/FractionalForm.lean` supplies `finiteGagliardoEnergy.toLp` and
   its representative, norm, and integral bridges; the immediate consumer is
   `L2TwoWellAux.toSpectralInput` in `Tunneling/Final.lean`, through the
   `hphi` and `hmass` evidence used by the interaction expansion.
4. Acceptance check: the unchanged `Tunneling.FinalTheoremL2` caller must
   compile after `L2TwoWellAux` derives its normalized ground-state and mass
   data from the finite-energy representative rather than retaining those as
   unrelated raw fields.
5. Sole credit expected: one-well ground-state representative bridge toward
   the `FinalTheoremL2` theorem slot; the operator, spectral, block-reduction,
   and multi-well obligations remain separate.

Promotion event: bridge the zero-exterior finite-energy representative into
`MeasureTheory.Lp`, prove the representative and integral identities needed by
the exact caller, and replay `FinalTheoremL2` unchanged.

## 2026-09-26 — cluster lemma integration into branch energies

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `branch_energy_bounds`, used by
   `Tunneling.FinalTheorem` and `Tunneling.FinalTheoremL2` in both branch
   perturbation estimates.
3. Exact paper source: `paper.tex`, Lemma 4.2 and the quadratic-form splitting
   in its proof, specialized to the one-dimensional ground-state cluster via
   `psi = (inner phi psi) • phi + residual phi psi`.
4. Promotion event: add the exact orthogonal additivity and homogeneity
   properties of the one-well Rayleigh energy, invoke
   `GroundStatePerturbation.cluster_form_lower_bound`, and replay the unchanged
   `FinalTheoremL2` caller.
5. Sole credit expected: caller-consumed isolated-cluster form estimate.  The
   finite-dimensional multi-well block and compression bounds remain separate.

### Acceptance result — cluster lemma integration into branch energies

`TwoWellSpectralInput` and `L2TwoWellAux` now expose the exact Rayleigh-form
laws `q 0 = 0`, orthogonal additivity, and quadratic homogeneity.  The lower
branch-energy proof splits a normalized vector as
`psi = (inner phi psi) • phi + residual phi psi`, derives the cluster values
`q p = mu * ‖p‖ ^ 2` and `(mu + gap) * ‖r‖ ^ 2 ≤ q r`, and invokes
`GroundStatePerturbation.cluster_form_lower_bound`.  A direct real-algebra
comparison then yields the unchanged `branch_energy_bounds` target consumed
by `FinalTheorem` and `FinalTheoremL2`.

The exact consumer build, full `lake build`, and literal audit all pass:
`Build completed successfully (2968 jobs)` and
`rg -n '^\s*(axiom|sorry)\b' Tunneling` is empty.  `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for both `FinalTheorem` and
`FinalTheoremL2`.  Sole credit accepted: caller-consumed isolated-cluster form
estimate.  The concrete one-well spectral construction, fractional block
unitary reduction, compression error, and complete finite multi-well theorem
remain open.

## 2026-09-26 — ground-state form orthogonality correction

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `branch_energy_bounds` and
   `L2TwoWellAux.toSpectralInput`, through the `q` splitting used by
   `GroundStatePerturbation.cluster_form_lower_bound`.
3. Exact paper source: `paper.tex`, Lemma 4.2 and the first line of its
   proof, where `p` lies in the isolated ground-state cluster and
   `r` is orthogonal to it; the form cross term vanishes because the
   cluster vector is an eigenstate.  The source does not assert
   additivity for every pair of merely L²-orthogonal vectors.
4. Promotion event: replace the overly strong global orthogonal-additivity
   fields by the exact ground-state-line identity
   `q (t • φ + r) = q (t • φ) + q r` for `inner φ r = 0`, derive
   `q 0 = 0` from quadratic homogeneity, and replay the unchanged
   `FinalTheoremL2` caller.
5. Sole credit expected: corrected source-faithful one-well form interface.
   The operator realization, spectral gap, and minimizer remain separate.

### Acceptance result — ground-state form orthogonality correction

`TwoWellSpectralInput` and `L2TwoWellAux` now use the exact ground-state
identity `q (t • φ + r) = q (t • φ) + q r` for `inner φ r = 0`, while
quadratic homogeneity supplies `q 0 = 0`.  The lower branch-energy proof
consumes this identity through `cluster_form_lower_bound`; the overstrong
global L²-orthogonal additivity fields have been removed.  The exact
`Final.lean` consumer, full `lake build`, literal `axiom`/`sorry` audit, and
`#print axioms` checks all pass, with only Lean's standard foundations
`[propext, Classical.choice, Quot.sound]` for `FinalTheorem` and
`FinalTheoremL2`.  Sole credit accepted: corrected source-faithful one-well
form interface.  The one-well operator, spectral gap, minimizer, fractional
block reduction, and compression theorem remain open.

## 2026-09-26 — finite-dimensional compression comparison

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: `multiWellConclusion`, through the finite
   eigenvalue comparison in the proof of `multiWellStatement`.
3. Exact paper source: `paper.tex`, Lemma 4.3 and Theorem 4.3, equations
   `eq:compression-error`, `eq:exact-cluster-comparison`, and
   `eq:multi-eigenvalue-bound`; the paper combines the cluster comparison
   with the entrywise compression error by the triangle inequality.
4. Promotion event: prove the caller-facing bridge from the isolated-cluster
   comparison and compression estimate to `multiWellConclusion`, including
   the cluster-edge and gap inequalities, and replay the full `lake build`.
5. Sole credit expected: caller-consumed finite-dimensional compression
   comparison.  The analytic block unitary and entrywise Taylor estimate
   remain separate.

## 2026-09-26 — finite multi-well capstone assembly

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: `multiWellStatement`, through its quantitative
   conclusion and `multiWellLimit_of_conclusion`.
3. Exact paper source: `paper.tex`, Theorem 4.3 and its final paragraph,
   equations `eq:multi-size-conditions`, `eq:multi-eigenvalue-bound`,
   `eq:multi-cluster-edges`, `eq:multi-cluster-gap`, and `eq:multi-limit`.
4. Promotion event: consume the proved finite-dimensional compression bridge
   at every valid separation, assemble `multiWellConclusion`, and invoke the
   existing limiting theorem to obtain `multiWellStatement`.
5. Sole credit expected: caller-consumed finite multi-well capstone assembly.
   The analytic block unitary, compact-resolvent cluster theorem, and
   entrywise Taylor compression estimate remain separate.

### Acceptance result — finite multi-well capstone assembly

`FinalTheoremMultiWell` now consumes
`multiWellConclusion_of_clusterCompression` at every valid separation and
assembles `multiWellStatement` through `multiWellLimit_of_conclusion`.  The
focused `Tunneling.MultiWell` build and full `lake build` both pass
(`Build completed successfully (2968 jobs)`).  The literal audit
`rg -n '^\s*(axiom|sorry)\b' Tunneling` is empty, and `#print axioms` reports
only `[propext, Classical.choice, Quot.sound]` for `FinalTheorem`,
`FinalTheoremL2`, and `FinalTheoremMultiWell`.  Sole credit accepted:
caller-consumed finite multi-well capstone assembly.  This does not discharge
the analytic block unitary, compact-resolvent cluster theorem, entrywise
Taylor compression estimate, or the one-well operator and ground-state
construction.

## 2026-09-26 — rescaled multi-well error limit

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: `FinalTheoremMultiWell`, through the
   `herr` argument of `multiWellLimit_of_conclusion`.
3. Exact paper source: `paper.tex`, Theorem 4.3 and its final paragraph,
   equation `eq:multi-limit`; the proof observes
   `L^kappa epsilon_L = O(L^-2)` and
   `L^kappa gamma_L^2 = O(L^-kappa)`, hence the rescaled total error tends
   to zero.
4. Promotion event: prove the rescaled-error limit from the explicit
   `multiWellEpsilon` and `multiWellGamma` power laws and remove `herr` from
   `FinalTheoremMultiWell`.
5. Sole credit expected: caller-consumed rescaled-error limit.  The analytic
   block unitary and one-well spectral construction remain separate.

### Acceptance result — finite-energy one-well representative bridge

`finiteGagliardoEnergy.toLp`, `coeFn_toLp`, `norm_toLp`, and the mass-integral
bridge are accepted by the full `lake build` (`Build completed successfully
(2968 jobs)`).  `L2TwoWellAux` now stores the raw finite-energy representative
and derives `hphi` and `hmass`; the unchanged `FinalTheoremL2` caller consumes
those derived results through `toSpectralInput`.  The literal audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` is empty, and `#print axioms` reports
only `[propext, Classical.choice, Quot.sound]` for both `FinalTheorem` and
`FinalTheoremL2`.  Sole credit accepted: one-well ground-state representative
bridge.  No analytic operator or spectral construction is claimed yet.

## 2026-09-26 — form-based one-well interface repair

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, specifically the
   `q`, `hqphi`, and `hgapq` fields consumed by `FinalTheorem`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:form` and the
   associated-operator paragraph, followed by equation `eq:mass`; the proof
   uses the closed quadratic form and its Rayleigh lower bound, not a bounded
   realization of the unbounded restricted fractional Laplacian.
4. Promotion event: replace the impossible bounded field
   `oneWellOperator : Lp ->L[real] Lp` and its derived Rayleigh identity by
   the actual one-well energy map, normalization/eigenvalue relation, and
   spectral-gap inequality, then replay the unchanged `FinalTheoremL2`
   caller.
5. Sole credit expected: corrected form-based one-well interface toward the
   `FinalTheoremL2` theorem slot.  Existence of the form-domain minimizer and
   spectral gap from the fractional operator remains a separate obligation.

This is a source-representation repair.  It removes an assumption that could
not be discharged for an unbounded operator and makes the remaining analytic
spine item mathematically well posed.

### Acceptance result — form-based one-well interface repair

`L2TwoWellAux.oneWellEnergy`, `hphiEnergyValue`, and `hgapEnergy` now replace
the bounded `oneWellOperator` field and its false operator realization.  The
full `lake build` accepts the unchanged `FinalTheoremL2` caller (`Build
completed successfully (2968 jobs)`).  The literal audit remains empty and
`#print axioms` reports only `[propext, Classical.choice, Quot.sound]`.  This
acceptance credits the corrected form-based interface only; the existence of
the minimizer and spectral gap is still open and is now the first missing
one-well spine theorem.

## 2026-09-26 — finite multi-well capstone source extraction

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`, the finite
   multi-well conclusion corresponding to paper Theorem 4.3.
2. Immediate Lean consumer: the future block-reduction and cluster-perturbation
   construction in `Tunneling.MultiWell`, through the exact eigenvalue and
   limiting-gap statement being added below.
3. Exact paper source: `paper.tex`, Theorem 4.3, equations
   `eq:multi-eigenvalue-bound`, `eq:multi-cluster-edges`,
   `eq:multi-cluster-gap`, and `eq:multi-limit`, together with
   `eq:effective-matrix` and the constants `gamma_L` and `epsilon_L` from
   Lemmas 4.1 and 4.3.
4. Promotion event: extract the complete finite multi-well theorem statement,
   including the ordered effective-matrix eigenvalues `theta_k`, the
   compression error, cluster edges, gap, and the limiting rescaling.
5. Sole credit expected: finite multi-well source-extraction theorem slot.
   The analytic block unitary, compact-resolvent cluster theorem, and
   compression-error proof remain separate obligations.

### Acceptance result — quadratic spectral-gap bridge

`GroundStatePerturbation.spectral_gap_of_operator` derives the normalized gap
from a symmetric one-well operator, its normalized ground-state eigen-equation,
and the scaled orthogonal-complement gap.  `L2TwoWellAux.q` is the associated
Rayleigh energy; the raw `hqφ`/`hgapq` fields are removed and
`L2TwoWellAux.toSpectralInput` consumes the derived proofs.  Full `lake build`
passes (2968 jobs), the literal hole audit is empty, and `#print axioms` gives
only `[propext, Classical.choice, Quot.sound]` for both final theorems.

## 2026-09-26 — one-well ground-state representative bridge

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux` normalization and mass fields,
   consumed by `L2TwoWellAux.toSpectralInput.htApprox`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, where the
   normalized positive eigenfunction has integral `m_1`.
4. Promotion event: map a finite-energy zero-exterior representative into
   `L²`, derive the normalized ground-state equality and mass identity from
   that representative, and replay the unchanged `FinalTheoremL2` caller.
5. Sole credit: the one-well ground-state representative bridge.

### Acceptance result — quadratic spectral-gap bridge

`GroundStatePerturbation.spectral_gap_of_operator` derives the normalized gap
from a symmetric one-well operator, its normalized ground-state eigen-equation,
and the scaled orthogonal-complement gap.  `L2TwoWellAux.q` is the associated
Rayleigh energy; the raw `hqφ`/`hgapq` fields are removed and
`L2TwoWellAux.toSpectralInput` consumes the derived proofs.  Full `lake build`
passes (2968 jobs), the literal hole audit is empty, and `#print axioms` gives
only `[propext, Classical.choice, Quot.sound]` for both final theorems.

## 2026-09-26 — one-well ground-state representative bridge

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux` normalization and mass fields,
   consumed by `L2TwoWellAux.toSpectralInput.htApprox`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, where the
   normalized positive eigenfunction has integral `m_1`.
4. Promotion event: map a finite-energy zero-exterior representative into
   `L²`, derive the normalized ground-state equality and mass identity from
   that representative, and replay the unchanged `FinalTheoremL2` caller.
5. Sole credit: the one-well ground-state representative bridge.

### Acceptance result — quadratic spectral-gap bridge

`GroundStatePerturbation.spectral_gap_of_operator` now derives the normalized
gap inequality from a symmetric one-well operator, its normalized ground-state
eigen-equation, and the scaled orthogonal-complement gap.  `L2TwoWellAux.q` is
the associated Rayleigh energy, and the raw `hqφ`/`hgapq` fields have been
removed; `L2TwoWellAux.toSpectralInput` consumes the derived proofs directly.
The full `lake build` passes (`Build completed successfully (2968 jobs)`).
The literal audit `rg -n '^\\s*(axiom|sorry)\\b' Tunneling` is empty, and
`#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for
`Tunneling.FinalTheoremL2` and `Tunneling.FinalTheorem`.

## 2026-09-26 — one-well operator and ground-state construction

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: the `L2TwoWellAux` fields `oneWellOperator`,
   `φ`, `hφ`, `hφEigen`, `hsymm`, and `hgap`, consumed through
   `L2TwoWellAux.toSpectralInput`.
3. Exact paper source: `paper.tex`, Section 2, equations `eq:form` and
   `eq:mass`, together with the cited closedness, compact-resolvent,
   simplicity, positivity, and reflection-invariance facts for `A_D`.
4. Promotion event: construct the one-well operator and normalized positive
   even ground state from the restricted zero-exterior form, derive the
   eigen-equation and spectral gap consumed by `FinalTheorem`, and replay
   the unchanged `FinalTheoremL2` caller.
5. Sole credit: the one-well operator/ground-state structural bucket.

### Acceptance result — quadratic spectral-gap bridge

`GroundStatePerturbation.spectral_gap_of_operator` now derives the normalized
gap inequality from a symmetric one-well operator, its normalized ground-state
eigen-equation, and the scaled orthogonal-complement gap.  `L2TwoWellAux.q` is
the associated Rayleigh energy, and the raw `hqφ`/`hgapq` fields have been
removed; `L2TwoWellAux.toSpectralInput` consumes the derived proofs directly.
The full `lake build` passes (`Build completed successfully (2968 jobs)`).
The literal audit `rg -n '^\\s*(axiom|sorry)\\b' Tunneling` is empty, and
`#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for
`Tunneling.FinalTheoremL2` and `Tunneling.FinalTheorem`.

## 2026-09-26 — one-well operator and ground-state construction

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: the `L2TwoWellAux` fields `oneWellOperator`,
   `φ`, `hφ`, `hφEigen`, `hsymm`, and `hgap`, consumed through
   `L2TwoWellAux.toSpectralInput`.
3. Exact paper source: `paper.tex`, Section 2, equations `eq:form` and
   `eq:mass`, together with the cited closedness, compact-resolvent,
   simplicity, positivity, and reflection-invariance facts for `A_D`.
4. Promotion event: construct the one-well operator and normalized positive
   even ground state from the restricted zero-exterior form, derive the
   eigen-equation and spectral gap consumed by `FinalTheorem`, and replay
   the unchanged `FinalTheoremL2` caller.
5. Sole credit: the one-well operator/ground-state structural bucket.

## 2026-09-26 — quadratic spectral-gap bridge

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput.hqφ` and
   `L2TwoWellAux.toSpectralInput.hgapq`, consumed by `FinalTheorem` through
   `GroundStatePerturbation.lower_bound`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, and Lemma
   3.1's decomposition `psi = a phi + eta`; the spectral gap is the lower
   bound `(mu + g) ||eta||^2 <= <A eta, eta>` for `eta` orthogonal to `phi`.
4. Promotion event: derive the normalized inequality
   `mu + g * ||residual phi psi||^2 <= q psi` from a symmetric operator `T`
   with `T phi = mu • phi`, `q psi = <T psi, psi>`, and the scaled
   orthogonal-complement gap; remove the raw `hqφ` and `hgapq` fields from
   `L2TwoWellAux` and replay the unchanged `FinalTheoremL2` caller.
5. Sole credit: the `FinalTheoremL2` one-well ground-state gap slot.

## 2026-09-25 — zero-extension source extraction for the restricted form

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through the
   future one-well quadratic form built from `FractionalForm.zeroExteriorForm`.
3. Exact paper source: `paper.tex`, Section 2 and equation `eq:form`, where a
   function on `D` is interpreted by zero extension to `R^d` before applying
   the global Gagliardo integral.
4. Promotion event: make `zeroExteriorForm` use the exact zero-extension
   representative, prove its value is unchanged for almost-everywhere equal
   representatives, and preserve the existing nonnegativity theorem.  The
   acceptance check is the unchanged full `lake build` plus the literal hole
   audit.  This earns only the restricted-form source-extraction bridge; the
   one-well operator and spectral theorem slots remain open.
5. Sole credit: restricted-form source extraction under the open one-well
   spectral-construction receipt.

### Acceptance result — zero-extension source extraction

The first build failed only on named-argument spelling for Mathlib's
`quasiMeasurePreserving_fst` and `quasiMeasurePreserving_snd`; the exact
interface repair uses their Greek measure parameters.  After that repair,
`FractionalForm.zeroExtension` supplies the equation `eq:form` representative,
`gagliardoSeminormSq_congr_ae` and `zeroExteriorForm_congr_ae` prove
representative invariance, and `zeroExteriorForm_eq_of_zeroExterior` identifies
the form with the ambient Gagliardo integral for zero-exterior functions.  The
unchanged full `lake build` accepts `Tunneling.FinalTheoremL2` and the complete
dependency graph (`Build completed successfully (2968 jobs)`).  The literal
audit `rg -n '^\\s*(axiom|sorry)\\b|aux\\.χ|χ :' Tunneling` finds no project
hole or raw cross-pairing field.  This closes only the restricted-form
source-extraction bridge; the one-well operator and spectral theorem slots
remain open.

## 2026-09-25 — quadratic algebra of the restricted form

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: the future closed quadratic form and one-well
   operator construction from `FractionalForm.zeroExteriorForm`.
3. Exact paper source: `paper.tex`, equation `eq:form`, where the Gagliardo
   energy is the quadratic form used to define the restricted fractional
   Laplacian.
4. Promotion event: prove scalar homogeneity and the parallelogram identity
   for `gagliardoSeminormSq`, transport both identities through
   `zeroExteriorForm`, and preserve the existing representative-invariance and
   nonnegativity interface.  The acceptance check is the unchanged full
   `lake build` and literal hole audit.  This earns only the quadratic-form
   algebra source-extraction bridge; no final theorem slot closes.
5. Sole credit: restricted quadratic-form algebra under the open one-well
   spectral-construction receipt.

### Acceptance result — quadratic algebra of the restricted form

`gagliardoIntegrand_smul` and `gagliardoSeminormSq_smul` prove exact scalar
homogeneity.  `gagliardoIntegrand_add_add_sub` proves the pointwise
parallelogram identity, and
`gagliardoSeminormSq_add_add_sub_of_integrable` integrates it with explicit
finiteness hypotheses.  The zero-extension algebra
`zeroExtension_smul`, `zeroExtension_add`, and `zeroExtension_sub` transports
both identities to `zeroExteriorForm_smul` and
`zeroExteriorForm_add_add_sub_of_integrable`.  The focused source check and
the unchanged full `lake build` pass (`Build completed successfully
(2968 jobs)`).  The literal audit finds no `axiom`, `sorry`, or raw
cross-pairing field; the `χ` matches are ordinary local identifiers.  This
closes the restricted quadratic-form algebra bridge only.  The concrete
one-well closed form, associated operator, spectral gap, and ground-state
construction remain open.

## 2026-09-25 — finite-energy domain for the restricted form

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: the future closed quadratic form and one-well
   operator construction from `FractionalForm.zeroExteriorForm`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:form`, and the
   definition of the form domain `H^s_0(D)` as the completion of compactly
   supported smooth functions in the global `H^s` norm.
4. Promotion event: define finite Gagliardo energy through integrability of
   the zero-extended integrand, prove closure under zero, scalar
   multiplication, and addition using the positive-kernel square estimate,
   and package the resulting set as a submodule of `X → ℝ`.  The acceptance
   check is the unchanged full `lake build` and literal hole audit.  This
   earns only the finite-energy form-domain source-extraction bridge; the
   closedness, operator, and spectral theorem slots remain open.
5. Sole credit: finite-energy form-domain source extraction under the open
   one-well spectral-construction receipt.

### Acceptance result — finite-energy form-domain source extraction

`finiteGagliardoEnergy` now records both almost-everywhere measurability of
the zero-extended representative and integrability of the exact Gagliardo
integrand.  `gagliardoIntegrand_aestronglyMeasurable` constructs product
measurability from measurable representatives and the explicit product-kernel
bridge, `gagliardoIntegrand_add_le` proves the positive-kernel square bound,
and `finiteGagliardoEnergy_zero`, `finiteGagliardoEnergy_smul`, and
`finiteGagliardoEnergy_add` establish closure.  The carrier is packaged as
`finiteGagliardoEnergySubmodule` with the kernel measurability bridge exposed
as a parameter rather than hidden as an assumption.  The focused source check
and full `lake build` pass (`Build completed successfully (2968 jobs)`), and
the literal audit finds no project `axiom`, `sorry`, or raw cross-pairing
field.  This closes only the finite-energy form-domain bridge; closedness,
the associated operator, spectral gap, and ground-state construction remain
open.

## 2026-09-26 — finite-energy `L²` domain completion

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `restrictedZeroExteriorForm` and the future
   closed one-well form/operator construction from
   `FractionalForm.zeroExteriorForm`.
3. Exact paper source: `paper.tex`, Section 2, the definition
   `H^s(G) = {u in H^s(R^d) : u = 0 a.e. on R^d \\ G}` and equation `eq:form`.
4. Promotion event: add the missing `L²` component to
   `finiteGagliardoEnergy`, prove closure under zero, scalar multiplication,
   addition, negation, and subtraction using `MemLp` closure, and replay the
   existing restricted-quadratic-map consumer.  The acceptance check is the
   focused `FractionalForm.lean` source check, the unchanged full `lake build`,
   and the literal hole audit.
5. Sole credit: corrected finite-energy form-domain source extraction under
   the open one-well spectral-construction receipt.

### Acceptance result — finite-energy `L²` domain completion

`finiteGagliardoEnergy` now uses `MeasureTheory.MemLp (zeroExtension G u) 2 mu`
for the `H^s`/`L²` component while retaining the exact Gagliardo-integrand
integrability used by the restricted quadratic map.  The zero, scalar,
addition, negation, and subtraction closures use `MemLp.zero`,
`MemLp.const_smul`, `MemLp.add`, and `MemLp.sub`, and the existing
`restrictedZeroExteriorForm` consumer passes unchanged.  The focused
`FractionalForm.lean` source check and full `lake build` pass
(`Build completed successfully (2968 jobs)`), and the literal audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` is empty.  This closes the corrected
finite-energy form-domain bridge; closedness, the one-well operator, spectral
gap, and ground-state construction remain open.

## 2026-09-25 — finite-energy subtraction closure

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: the restricted quadratic form and one-well
   operator construction from `FractionalForm.zeroExteriorForm`.
3. Exact paper source: `paper.tex`, Section 2 and equation `eq:form`, where
   the form domain is a vector space and the quadratic form is evaluated on
   sums and differences of admissible functions.
4. Promotion event: derive negation and subtraction closure for
   `finiteGagliardoEnergy` from the existing scalar and addition closures,
   then replay the focused source check and full `lake build`.  This earns
   only the finite-energy vector-space bridge needed for polarization; the
   quadratic-map, closed-form, operator, and spectral slots remain open.
5. Sole credit: finite-energy subtraction closure under the one-well
   spectral-construction receipt.

### Acceptance result — finite-energy subtraction closure

`finiteGagliardoEnergy_neg` derives negation closure from scalar closure at
`-1`, and `finiteGagliardoEnergy_sub` derives subtraction closure by combining
negation with the existing addition theorem and converting
`u + -v` back to `u - v`.  The focused `FractionalForm.lean` check and the
unchanged full `lake build` pass (`Build completed successfully (2968 jobs)`),
and the literal audit finds no project `axiom`, `sorry`, or raw cross-pairing
field.  This closes the finite-energy vector-space bridge needed for
polarization only; the quadratic-map, closed-form, operator, and spectral
slots remain open.

## 2026-09-25 — restricted quadratic map on the finite-energy domain

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: the future closed quadratic form and one-well
   operator construction from `FractionalForm.zeroExteriorForm`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:form`, and the
   quadratic-form algebra used to define the restricted fractional
   Laplacian.
4. Promotion event: package `zeroExteriorForm` on
   `finiteGagliardoEnergySubmodule` as a `QuadraticMap`, proving scalar
   homogeneity and polarization additivity/scaling from finite-energy closure
   and the existing quadratic identities.  The acceptance check is the
   focused `FractionalForm.lean` source check followed by the unchanged full
   `lake build` and literal hole audit.  This earns only the restricted
   quadratic-map bridge; the closed form, operator, and spectral slots remain
   open.
5. Sole credit: restricted quadratic-map source extraction under the open
   one-well spectral-construction receipt.

### Acceptance result — restricted quadratic map on the finite-energy domain

`restrictedZeroExteriorForm` now packages `zeroExteriorForm` on
`finiteGagliardoEnergySubmodule` as a `QuadraticMap ℝ _ ℝ` via
`QuadraticMap.ofPolar`.  The scalar law follows from
`zeroExteriorForm_smul`; polarization additivity and scaling follow from the
finite-energy closure theorems, the exact pointwise cross-difference
identities, and `zeroExteriorForm_polar_eq_sub_sub_div_two`.  The focused
`FractionalForm.lean` source check and full `lake build` pass
(`Build completed successfully (2968 jobs)`), and the literal audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` is empty.  This closes only the
restricted quadratic-map bridge; the closed form, one-well operator, and
spectral slots remain open.

## 2026-09-25 — normalized limiting-gap error decomposition

1. Structural bucket and milestone capstone: two-well splitting, capped by
   `FinalTheoremL2`.
2. Exact paper source and Lean statement: `paper.tex`, Theorem 3.3,
   equation `eq:gap-limit`; prove the `A.gapLimit S.lambda` field consumed by
   `FinalTheorem` and `FinalTheoremL2`.
3. Supplier and immediate consumer: `Tunneling/Final.lean`, consumed by
   `FinalTheorem.hgapLimit` in the unchanged caller construction.
4. Acceptance check: `lake build`, followed by the literal
   `axiom`/`sorry` audit.
5. Sole credit: the `FinalTheoremL2` theorem slot `A.gapLimit`.

The changed mathematical input after the spine reset is the exact normalized
identity

`L^kappa * (lambda L 1 - lambda L 0) - 2*c*m^2`

`= L^kappa * (rMinus L - rPlus L) - 2*L^kappa*(t L + c*m^2*L^(-kappa))`,

with an explicit absolute-value bound obtained from the two branch remainder
bounds and `htApprox`.  This replaces the failed direct `Tendsto` assembly.

### Acceptance result — normalized limiting-gap error decomposition

`twoWellGapLimit_of_branchErrors` now proves equation `eq:gap-limit` from the
exact normalized branch-remainder identity and the two vanishing error orders.
`FinalTheorem` consumes this result in its `A.gapLimit` slot, and the raw
`hgapLimit` fields have been removed from both `TwoWellSpectralInput` and
`L2TwoWellAux`.  The unchanged `FinalTheoremL2` caller passes the full
`lake build` check (`Build completed successfully (2967 jobs)`), and the audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` is empty.

The acceptance followed several local repair checks for real-power
normalization, multiplication association, and `Tendsto.congr'` comparison
functions.  The paper source, theorem scope, and caller acceptance theorem
were unchanged throughout.

## 2026-09-25 — definitional branch eigenvalue slots

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `FinalTheorem` branch remainder assembly and
   `twoWellGapLimit_of_branchErrors`.
3. Exact paper source: `paper.tex`, Lemma 2.1 and Theorem 3.3,
   equation `eq:branches`, where the first two eigenvalues are the two branch
   ground energies.
4. Promotion event: define the first two entries of `lambda` from
   `branchEnergy q (B_L)` and `branchEnergy q (-B_L)`, remove the raw
   `hbranchPlus`/`hbranchMinus` fields, and replay the unchanged
   `FinalTheoremL2` caller build.
5. Sole credit: the `FinalTheoremL2` theorem slots for the two branch
   eigenvalue identities.

### Acceptance result — definitional branch eigenvalue slots

`twoWellLambda` now defines the first two entries of `lambda` from the two
branch ground energies, with higher spectral data retained explicitly.  The
raw `hbranchPlus`/`hbranchMinus` fields have been removed from both
`TwoWellSpectralInput` and `L2TwoWellAux`; `FinalTheorem` and
`twoWellGapLimit_of_branchErrors` consume the derived identities.  The full
`lake build` accepts the unchanged `FinalTheoremL2` caller
(`Build completed successfully (2967 jobs)`), and the literal audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` is empty.

## 2026-09-25 — third-level spectral bounds

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `FinalTheorem`, via the `hlambda2` and
   `hlambdaGap` conclusion fields.
3. Exact paper source: `paper.tex`, Theorem 3.3,
   equation `eq:two-well-third-level`, derived from the branch second-energy
   lower bound and the branch ground-energy upper bound.
4. Promotion event: introduce the orthogonal second branch energy, derive
   `mu1 + 3 gap / 4` for both branch second energies and the `gap / 2`
   separation from the branch ground energies, then replace the raw
   `hlambda2`/`hlambdaGap` fields with these derived bounds.
5. Sole credit: the `FinalTheoremL2` theorem slots for the two third-level
   inequalities.

### Acceptance result — third-level spectral bounds

Both inequalities in `eq:two-well-third-level` are now derived and consumed by
`FinalTheorem`.  `branchSecondEnergy` is the constrained Rayleigh infimum over
unit vectors orthogonal to the normalized ground state, with a conservative
fallback in degenerate spaces; `branchSecondEnergy_lower` proves the paper's
within-branch estimate from `hgapq` and `‖B_L‖ <= gap / 4`, and
`twoWellLambda` uses the minimum of the two constrained branch energies in its
third slot.  `TwoWellSpectralInput.third_level_lower` gives
`mu1 + 3 gap / 4 <= lambda L 2`, while `third_level_gap` gives
`gap / 2 <= lambda L 2 - lambda L 1`.  The raw `hlambda2`/`hlambdaGap` fields
have been removed from both `TwoWellSpectralInput` and `L2TwoWellAux`.  The
unchanged `FinalTheoremL2` caller passes the full `lake build` (`Build completed
successfully (2967 jobs)`), and the literal audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` is empty.

## 2026-09-25 — interaction-mass integrability

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput.htApprox`, through
   the `hlinInt` and `hRInt` arguments of `interactionMass_taylor_remainder`.
3. Exact paper source: `paper.tex`, Lemma 3.2 and equation `eq:kernel-expansion`,
   where the linear Taylor term and the quadratic remainder are integrated
   against the product ground-state mass after the pointwise Taylor bound.
4. Promotion event: derive both product integrability statements from
   `l2ProductIntegrable`, `hX`, `hdirection`, and the existing Taylor remainder
   bound, remove the raw `hlinInt`/`hRInt` fields from `L2TwoWellAux`, and replay
   the unchanged `FinalTheoremL2` caller build.
5. Sole credit: the interaction-mass integrability structural bucket.

### Acceptance result — interaction-mass integrability

`bounded_factor_mul_integrable` now derives both product integrability
statements from `l2ProductIntegrable` and measurable bounded factors.  The
linear factor is bounded by `2 R` using `hdirection`, `hX`, and
`abs_real_inner_le_norm`; the Taylor factor is bounded by
`A.C L^(-kappa-2)` using the existing pointwise `hTaylorBound` and
`twoWellTaylorRemainder_continuous`.  The raw `hlinInt`/`hRInt` fields have
been removed from `L2TwoWellAux`; `toSpectralInput.htApprox` now supplies the
derived proofs directly to `interactionMass_taylor_remainder`.  The unchanged
`FinalTheoremL2` caller passes the full `lake build` (`Build completed
successfully (2967 jobs)`), and the literal audit
`rg -n '^\s*(axiom|sorry)\b' Tunneling` is empty.

## 2026-09-25 — one-well spectral construction

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through the
   `q`, `φ`, `hφ`, `hqφ`, `hgapq`, `hmass`, and `hnonneg` fields.
3. Exact paper source: `paper.tex`, Section 2, equations `eq:form` and
   `eq:mass`, together with the cited compactness, simplicity, positivity,
   reflection invariance, and spectral-gap facts for the restricted fractional
   Laplacian on `D`.
4. Promotion event: construct the one-well self-adjoint operator with compact
   resolvent and its normalized positive even ground state, derive the
   quadratic energy and gap lower bound consumed by `FinalTheorem`, and replace
   the corresponding raw L2 inputs by that construction.
5. Sole credit: the one-well spectral-data structural bucket.

### Promotion status — one-well spectral construction

The first source-level subbridge under this receipt is now accepted:
`linear_integral_zero_of_even` derives the linear Taylor cancellation from
ground-state evenness and reflection invariance of the measure.  The raw
`hlinear` field has been removed from `L2TwoWellAux`; `htApprox` consumes the
derived proof in `interactionMass_taylor_remainder`.  The unchanged
`FinalTheoremL2` caller passes the full `lake build` (`Build completed
successfully (2967 jobs)`), and the literal audit
`rg -n '^\s*(axiom|sorry)\b' Tunneling` is empty.  The receipt remains open for
the one-well operator, ground-state, mass, and gap constructions.

### Promotion event — derived measurable negation

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `linear_integral_zero_of_even`, consumed by
   `L2TwoWellAux.toSpectralInput.htApprox`.
3. Exact paper source: `paper.tex`, Lemma 3.2 and the reflected-coordinate
   symmetry `phi_1(-x)=phi_1(x)` together with invariance of the component
   measure under central inversion.
4. Promotion event: derive `MeasurableNeg X` from the measurable field of
   `hmeasureNeg`, remove the redundant `MeasurableNeg X` typeclass assumptions,
   and replay the unchanged `FinalTheoremL2` caller build.
5. Sole credit: interface hygiene under the one-well receipt.

### Acceptance result — derived measurable negation

`measurableNeg_of_measurePreserving_neg` now derives `MeasurableNeg X` from
the measurable field of `hmu : MeasurePreserving (fun x => -x) mu mu`, and
`linear_integral_zero_of_even` consumes that named theorem instead of an
inline instance construction.  The focused `Final.lean` source check and the
full `lake build` pass (`Build completed successfully (2968 jobs)`), and the
literal audit `rg -n '^\\s*(axiom|sorry)\\b' Tunneling` is empty.  This closes
only the measurable-negation interface subbridge; the one-well operator,
ground-state, mass, and gap constructions remain open.

### Promotion event — valid-range L2 cross pairing

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.toSpectralInput`, through
   `hBnorm`, `htApprox`, and the `cross` field of `TwoWellSpectralInput`.
3. Exact paper source: `paper.tex`, Lemma 2.1 and equation `eq:B`, where the
   bounded cross-kernel estimate is asserted for the theorem's separation
   range `L >= A.L0`; no pairing is required for smaller separations.
4. Promotion event: restrict the raw `χ` field to `A.L0 <= L`, extend the
   symmetric cross pairing by zero outside that range, and replay the unchanged
   `FinalTheoremL2` caller build without changing its statement.
5. Sole credit: valid-range interface repair under the two-well cross-kernel
   receipt.

### Acceptance result — valid-range L2 cross pairing

The raw `χ` field in `L2TwoWellAux` now supplies an `L2CrossPairing` only for
`A.L0 <= L`.  `L2TwoWellAux.cross` extends this data to every real separation
by `SymmetricCrossPairing.zero` outside the theorem range, and both `lambda`
and `toSpectralInput` consume that extension.  The proofs of `hBnorm` and
`htApprox` reduce the extension back to `aux.χ L hL` on their valid range.
The unchanged `FinalTheoremL2` statement passes the full `lake build`
(`Build completed successfully (2967 jobs)`), and the literal audit
`rg -n '^\s*(axiom|sorry)\b' Tunneling` is empty.

### Acceptance result — kernel-derived L2 cross pairing

`FractionalForm` now proves bounded-kernel integrability and the four
bilinearity identities for `kernelCrossPairing`, using almost-everywhere
representative equalities of `MeasureTheory.Lp`.  `Final` packages these facts
in `L2CrossPairing.ofKernel`, and `L2TwoWellAux.validCross` constructs the
valid-range pairing from `twoWellKernel` using the existing separated-kernel
bound and continuity.  The raw `χ` field has therefore been removed from
`L2TwoWellAux`; `lambda`, `toSpectralInput.hBnorm`, and `htApprox` consume the
constructed pairing directly.  The unchanged `FinalTheoremL2` statement
passes the full `lake build` (`Build completed successfully (2967 jobs)`), and
the audit `rg -n '^\s*(axiom|sorry)\b|aux\.χ|χ :' Tunneling` finds no axiom,
hole, or raw cross-pairing field.

## 2026-09-25 — multi-well effective-matrix source extraction

1. Named final-facing theorem: the finite multi-well effective interaction
   theorem from `paper.tex`, Theorem 4.3 and equation `eq:effective-matrix`.
2. Immediate Lean consumer: `Tunneling.MultiWell`, currently the exact
   zero-diagonal matrix definition and its symmetry/Hermitian spectral
   interface.
3. Exact paper source: `paper.tex`, Definitions 4.1 and 4.2, equation
   `eq:effective-matrix`, and the ordered eigenvalues
   `theta_1 <= ... <= theta_N`.
4. Promotion event: add `effectiveInteractionMatrix` with entries
   `-c m^2 |a_i-a_j|^(-kappa)` off the diagonal and zero on the diagonal,
   prove `IsSymm`/`IsHermitian`, and expose
   `effectiveInteractionEigenvalues` through the matrix spectral theorem.
5. Sole credit: finite-dimensional multi-well source extraction.  The block
   operator reduction, compression error, cluster perturbation, and limiting
   theorem remain open.

### Acceptance result — multi-well effective-matrix source extraction

`Tunneling.MultiWell` compiles with no `sorry` or `axiom`, and is imported by
`Tunneling.lean`.  The full `lake build` accepts the complete dependency graph
(`Build completed successfully (2968 jobs)`).  This is source extraction and
finite-dimensional spectral plumbing only; it does not claim the analytic
multi-well theorem yet.

### Acceptance result — zero trace and eigenvalue sum

`Tunneling.MultiWell` now also proves
`Matrix.trace (effectiveInteractionMatrix a c m kappa) = 0` directly from its
zero diagonal and derives
`∑ i, effectiveInteractionEigenvalues a c m kappa i = 0` through
`Matrix.IsHermitian.trace_eq_sum_eigenvalues`.  The full `lake build` accepts
these additions (`Build completed successfully (2968 jobs)`).  These are the
finite-dimensional sign inputs used in the paper's collective-ground-state
argument; the sign inequalities and multi-well asymptotic theorem remain open.

### Acceptance result — nonzero matrix and positive eigenvalue

`Tunneling.MultiWell` now proves that two distinct indices with distinct
positions give a nonzero effective interaction matrix whenever `c` and `m` are
nonzero.  Combined with the zero-trace identity, this yields
`exists_positive_effectiveInteractionEigenvalue`, and the direct
`exists_positive_effectiveInteractionEigenvalue_of_distinct` corollary removes
the abstract nonzero premise.  The full `lake build` accepts these finite-
dimensional sign bridges (`Build completed successfully (2968 jobs)`).

### Acceptance result — paired sign eigenvalues

`Tunneling.MultiWell` now also proves
`exists_negative_effectiveInteractionEigenvalue` from the zero-trace
eigenvalue sum and the positive-eigenvalue theorem.  Together these give the
finite-dimensional sign pair used in the collective-ground-state argument.
The focused `MultiWell.lean` check passes with no holes.  The analytic
multi-well asymptotic theorem and one-well operator construction remain open.

### Acceptance result — ordered effective-matrix spectrum

`Tunneling.MultiWell` now exposes
`effectiveInteractionTheta`, the increasing finite sequence corresponding to
the paper's `theta_1 <= ... <= theta_N`, and proves
`effectiveInteractionTheta_monotone` by reversing Mathlib's antitone
`Matrix.IsHermitian.eigenvalues₀`.  The full project build accepts this
ordered spectral interface with no holes.  The analytic multi-well theorem and
one-well operator construction remain open.

### Acceptance result — ordered theta sign pair

`Tunneling.MultiWell` now proves `effectiveInteractionTheta_sum_eq_zero` and
the ordered sign statements
`exists_positive_effectiveInteractionTheta` and
`exists_negative_effectiveInteractionTheta` for every nonzero effective
interaction matrix.  These match the paper's `theta_1 < 0 < theta_N` sign
input and pass the full `lake build` (`Build completed successfully
(2968 jobs)`).  The analytic multi-well asymptotics and one-well operator
construction remain open.

## 2026-09-25 — defined two-well cross kernel

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.hBnorm` and
   `L2TwoWellAux.toSpectralInput.htApprox`, through the `hKdef` bridge.
3. Exact paper source: `paper.tex`, Lemma 2.1, equation `eq:B`, where
   `B_L v(x) = -c_{d,s} \int_D v(y) / |L e - x - y|^kappa dy`.
4. Promotion event: define `twoWellKernel A direction L x y` as
   `-A.c * translatedCrossKernel A.kappa ((L:ℝ) • direction) x y`, remove the
   free `K` and raw `hKdef` fields, and replay the unchanged `FinalTheoremL2`
   caller build.  The acceptance check is that caller build.

### Acceptance result — defined two-well cross kernel

`twoWellKernel A direction L x y` now defines the equation `eq:B` kernel as
`-A.c * translatedCrossKernel A.kappa ((L:ℝ) • direction) x y`.  The free `K`
parameter and raw `hKdef` field have been removed; `L2TwoWellAux.χ` is indexed
directly by this kernel.  The full `lake build` accepts `FinalTheoremL2`, with
`Tunneling.Final` built in the caller job, and the audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` remains empty.

## 2026-09-25 — definitional translated cross-kernel

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.hBnorm` and `htApprox`, which currently use
   `hKdef` to identify the cross kernel.
3. Exact paper source: `paper.tex`, Lemma 2.1 and equation `eq:B`, where
   `B_L` has kernel
   `-c_{d,s} abs(L e - x - y)^(-kappa)`.
4. Promotion event: define the translated cross-kernel from `A`, `direction`,
   and `L`, remove the raw `hKdef` equality from `L2TwoWellAux`, and replay
   the unchanged `FinalTheoremL2` caller build.

## 2026-09-25 — product integrability of the mass term

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.htApprox`, through
   `interactionMass_taylor_remainder`, whose `hprodInt` hypothesis is the
   product mass term.
3. Exact paper source: `paper.tex`, Lemma 3.2 and equation `eq:kernel-expansion`,
   where the leading interaction mass is
   `m_1^2 = integral integral phi_1(x) phi_1(y)`.
4. Promotion event: derive `hprodInt` from `φ ∈ Lp ℝ 2 mu` and finite measure
   using `MemLp.integrable` and `Integrable.mul_prod`, remove the raw
   `hprodInt` field from `L2TwoWellAux`, and replay the unchanged
   `FinalTheoremL2` caller build.

### Acceptance result — product integrability of the mass term

`l2ProductIntegrable` is accepted by the full `lake build` after supplying the
explicit `q := 2` exponent and `Integrable.mul_prod` binders.  The raw
`hprodInt` field has been removed from `L2TwoWellAux`, and the unchanged
`FinalTheoremL2` caller consumes the derived product integral.  The audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` remains empty.

## 2026-09-25 — product integrability of the mass term

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.htApprox`, through
   `interactionMass_taylor_remainder`, whose `hprodInt` hypothesis is the
   product mass term.
3. Exact paper source: `paper.tex`, Lemma 3.2 and equation `eq:kernel-expansion`,
   where the leading interaction mass is
   `m_1^2 = integral integral phi_1(x) phi_1(y)`.
4. Promotion event: derive `hprodInt` from `φ ∈ Lp ℝ 2 mu` and finite measure
   using `MemLp.integrable` and `Integrable.mul_prod`, remove the raw
   `hprodInt` field from `L2TwoWellAux`, and replay the unchanged
   `FinalTheoremL2` caller build.

## 2026-09-25 — product integrability of the mass term

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.htApprox`, through
   `interactionMass_taylor_remainder`, whose `hprodInt` hypothesis is the
   product mass term.
3. Exact paper source: `paper.tex`, Lemma 3.2 and equation `eq:kernel-expansion`,
   where the leading interaction mass is
   `m_1^2 = integral integral phi_1(x) phi_1(y)`.
4. Promotion event: derive `hprodInt` from `φ ∈ Lp ℝ 2 mu` and finite measure
   using `MemLp.integrable` and `Integrable.mul_prod`, remove the raw
   `hprodInt` field from `L2TwoWellAux`, and replay the unchanged
   `FinalTheoremL2` caller build.

### Promotion stalled — limiting gap

The limiting-gap receipt has two consecutive failed acceptance checks.  The
first reached the branch subtraction but failed on real-power and absolute-
value representation.  The repaired proof reached the final bound but failed
on the `L^kappa L^{-kappa}` normalization, the branch symmetry projection,
the final error comparison, and the `Tendsto`/squeeze names.  This receipt is
closed as promotion stalled.

Spine reset:

- Paper formula: equation `eq:gap-limit`,
  `L^kappa (lambda_L,2-lambda_L,1) -> 2 c_{d,s} m_1^2`.
- Current Lean type:
  `Filter.Tendsto (fun L : ℝ => L ^ A.kappa *
    (S.lambda L 1 - S.lambda L 0)) Filter.atTop
    (nhds (2 * A.c * A.phiMass ^ 2))`.
- Proposed bridge domain/codomain: branch energies and `S.t L` on
  `[A.L0, infinity)` to real error bounds tending to zero.
- Smallest identity test:
  `L^kappa * (S.lambda L 1 - S.lambda L 0) - 2*A.c*A.phiMass^2`
  is bounded by the sum of the `t_L` Taylor error and the two perturbation
  remainders.
- Theorem slot: `FinalTheoremL2` conclusion `A.gapLimit`.

### Promotion stalled — limiting gap

The limiting-gap receipt has two consecutive failed acceptance checks.  The
first reached the branch subtraction but failed on real-power and absolute-
value representation.  The repaired proof reached the final bound but failed
on the `L^kappa L^{-kappa}` normalization, the branch symmetry projection,
the final error comparison, and the `Tendsto`/squeeze names.  This receipt is
closed as promotion stalled.

Spine reset:

- Paper formula: equation `eq:gap-limit`,
  `L^kappa (lambda_L,2-lambda_L,1) -> 2 c_{d,s} m_1^2`.
- Current Lean type:
  `Filter.Tendsto (fun L : ℝ => L ^ A.kappa *
    (S.lambda L 1 - S.lambda L 0)) Filter.atTop
    (nhds (2 * A.c * A.phiMass ^ 2))`.
- Proposed bridge domain/codomain: branch energies and `S.t L` on
  `[A.L0, infinity)` to real error bounds tending to zero.
- Smallest identity test:
  `L^kappa * (S.lambda L 1 - S.lambda L 0) - 2*A.c*A.phiMass^2`
  is bounded by the sum of the `t_L` Taylor error and the two perturbation
  remainders.
- Theorem slot: `FinalTheoremL2` conclusion `A.gapLimit`.

## 2026-09-25 — definitional coordinate linear form

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `L2TwoWellAux.toSpectralInput.htApprox`, through `hlineDeriv`,
   `hTaylorBound`, and `interactionMass_taylor_remainder`, together with the
   `hlinInt` and `hlinear` fields.
3. Exact paper source: `paper.tex`, Lemma 3.2 and the Taylor expansion
   `F_L(z)=L^{-kappa}+kappa L^{-kappa-1} e dot z + ...`, where the linear
   coordinate map is `ell(z)=e dot z`.
4. Promotion event: replace the raw `linear`/`hlinearDef` fields in
   `L2TwoWellAux` by the derived form `linearForm direction z =
   inner ℝ direction z`, preserving the exact Taylor remainder statement and
   replaying the unchanged `FinalTheoremL2` caller build.

## 2026-09-25 — explicit L0 smallness condition

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `TwoWellSpectralInput.hbetaSmall` and `L2TwoWellAux.hbetaSmall`, consumed by
   `FinalTheorem` through `hsmall`, `hbneg`, and the two branch applications
   of `GroundStatePerturbation.lower_bound`.
3. Exact paper source: `paper.tex`, Theorem 3.3, equation `eq:explicit-L0`,
   and the first inequality in `eq:L0-conditions`,
   `beta_L <= g/4`.
4. Promotion event: derive `hbetaSmall` from the first threshold in `L0`,
   namely
   `L0 >= (4 * c * 2 ^ kappa * volumeD / gap) ^ (1 / kappa)`,
   and remove the raw `hbetaSmall` fields from both interfaces.  The
   acceptance check is the unchanged `FinalTheoremL2` caller build.

### Acceptance result — explicit L0 smallness condition

`TwoWellConstants.beta_small` is accepted by the full `lake build` after the
source-order and real-arithmetic repairs.  The raw `hbetaSmall` fields were
removed from `TwoWellSpectralInput` and `L2TwoWellAux`, and the unchanged
`FinalTheoremL2` caller consumes the proved theorem directly.  The audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` remains empty.

## 2026-09-25 — definitional cross-operator identity

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `TwoWellSpectralInput.hBcross`, used by `FinalTheorem` to derive symmetry
   of `B L` and by `L2TwoWellAux.toSpectralInput` to instantiate the L2
   operator.
3. Exact paper source: `paper.tex`, Lemma 2.1 and equation `eq:B`, where
   `B_L` is the self-adjoint operator associated with the cross kernel.
4. Promotion event: remove the raw equality field `hBcross` by defining the
   abstract branch operator from the supplied cross pairing, then rebuild the
   unchanged `FinalTheoremL2` caller.  The acceptance check is that caller
   build.

### Acceptance repair — derived operator projection

The first caller replay failed because `TwoWellSpectralInput.B` depends on
`SymmetricCrossPairing.operator` and therefore must be `noncomputable`, and
because `nlinarith` did not unfold that projection in the two norm-square
estimates.  This repair marks the definition `noncomputable` and proves the
square bound explicitly through `sq_le_sq` and the supplied `hBnorm`.  The
paper source, theorem scope, and acceptance check are unchanged.

### Acceptance result — definitional cross-operator identity

`TwoWellSpectralInput.B` is now derived from `cross`, and the raw `hBcross`
field has been removed.  The full `lake build` accepts the unchanged
`FinalTheoremL2` caller after the `noncomputable` and explicit norm-square
repairs.  The audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` remains empty.

## 2026-09-25 — definitional branch diagonal

1. Named final-facing theorem: `FinalTheoremL2`.
2. Immediate Lean consumer:
   `FinalTheorem.hstabPlus`, `FinalTheorem.hstabMinus`, and
   `L2TwoWellAux.toSpectralInput.htApprox`.
3. Exact paper source: `paper.tex`, Theorem 3.3 and equation `eq:branches`,
   where `t_L = <phi_1, B_L phi_1>` is the diagonal matrix coefficient of
   the cross perturbation.
4. Promotion event: remove the free `t : ℝ → ℝ` and `ht` equality fields from
   `TwoWellSpectralInput`, define `TwoWellSpectralInput.t` from the supplied
   cross operator and ground state, and replay the unchanged `FinalTheoremL2`
   caller build.

### Acceptance repair — diagonal projection normalization

The first caller replay reached the branch remainder assembly but failed on
the normalized summand order in `add_le_add`, on a stale `t` field in the L2
constructor, and on an extra function coercion in the operator-inner kernel
conversion.  This repair normalizes `htApprox` to
`|S.t L + c m^2 L^{-kappa}|`, removes the stale constructor field, and uses
the Lp element `aux.φ` directly.  The paper source, theorem scope, and
acceptance check are unchanged.

### Acceptance result — definitional coordinate linear form

`linearForm direction z = inner ℝ direction z` is now used by the L2 Taylor
remainder and integration fields, and the raw `linear`/`hlinearDef` fields
have been removed.  The full `lake build` accepts the unchanged
`FinalTheoremL2` caller.  The audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` remains empty.

### Acceptance result — definitional branch diagonal

`TwoWellSpectralInput.t` is now derived from
`inner ℝ ((cross L).operator φ) φ`, and both the free `t` field and the raw
`ht` equality have been removed.  The full `lake build` accepts the unchanged
`FinalTheoremL2` caller after the summand-order, stale-field, and coercion
repairs.  The audit
`rg -n '^\\s*(axiom|sorry)\\b' Tunneling` remains empty.

### Promotion stalled — limiting gap

The limiting-gap receipt has two consecutive failed acceptance checks.  The
first reached the branch subtraction but failed on real-power and absolute-
value representation.  The repaired proof reached the final bound but failed
on the `L^kappa L^{-kappa}` normalization, the branch symmetry projection,
the final error comparison, and the `Tendsto`/squeeze names.  This receipt is
closed as promotion stalled.

Spine reset:

- Paper formula: equation `eq:gap-limit`,
  `L^kappa (lambda_L,2-lambda_L,1) -> 2 c_{d,s} m_1^2`.
- Current Lean type:
  `Filter.Tendsto (fun L : ℝ => L ^ A.kappa *
    (S.lambda L 1 - S.lambda L 0)) Filter.atTop
    (nhds (2 * A.c * A.phiMass ^ 2))`.
- Proposed bridge domain/codomain: branch energies and `S.t L` on
  `[A.L0, infinity)` to real error bounds tending to zero.
- Smallest identity test:
  `L^kappa * (S.lambda L 1 - S.lambda L 0) - 2*A.c*A.phiMass^2`
  is bounded by the sum of the `t_L` Taylor error and the two perturbation
  remainders.
- Theorem slot: `FinalTheoremL2` conclusion `A.gapLimit`.

## 2026-09-27 — acceptance result — eigen-equation first-variation interface

The focused `Tunneling.Final` build and the full package replay pass
(`Build completed successfully (2972 jobs)`).  `L2TwoWellAux.hgroundPolar`
now consumes the source-level first-variation field `hgroundPolarSource`
directly, and the unchanged `FinalTheoremL2` caller consumes that bridge via
`hqEnergyGroundAdd`, `hgapEnergy`, and `hgapq`.  The literal audit finds no
project `axiom` or proof `sorry`; `#print axioms` reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` foundations.

This closes only the eigen-equation first-variation interface.  The
construction of `hgroundPolarSource` and `hgapOrthSource` from the restricted
fractional form, together with the one-well operator/ground-state realization
and the finite-well spectral reductions, remains open.

## 2026-09-27 — source-faithful polar compatibility

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: the source-to-`L²` first-variation bridge used by
   `L2TwoWellAux.hgroundPolarSource` and its derived `hgroundPolar`.
3. Exact paper source: `paper.tex`, equation `eq:form`, where polarization of
   the zero-exterior quadratic form is taken on the finite-energy domain.
4. Promotion event: prove that
   `restrictedZeroExteriorFormLift_polar_apply_toLp` agrees with
   `QuadraticMap.polar (restrictedZeroExteriorForm ...)` on finite-energy
   representatives.
5. Sole credit: the finite-energy source-faithful polar compatibility bridge.

### Acceptance result — source-faithful polar compatibility

`restrictedZeroExteriorFormLift_polar_apply_toLp` is accepted by the focused
`FractionalForm.lean` check and the full package replay
(`Build completed successfully (2972 jobs)`).  The literal audit has no
project `axiom` or proof `sorry`, and `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for all three capstones.  This
closes the finite-energy polar compatibility subbridge only.  It does not
construct the one-well operator or justify extension of the source form to
arbitrary `L²` elements; the compatibility lift remains a representation
bridge rather than the unbounded restricted fractional Laplacian.

## 2026-09-27 — one-well Rayleigh operator interface

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.hφEnergyValue`, `hgroundPolar`,
   `hgapEnergy`, and `toSpectralInput`, followed by `FinalTheoremL2`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:form`, the
   eigen-equation `A_D phi_1 = mu_1 phi_1`, and the orthogonal spectral gap.
4. Promotion event: replace the raw one-well energy, first-variation, and
   orthogonal-gap fields by a bounded symmetric one-well Rayleigh operator
   with its form representation and derive the old obligations from that
   operator interface.
5. Sole credit: the caller-consumed one-well Rayleigh operator interface.

### Acceptance result — one-well Rayleigh operator interface

`L2TwoWellAux` now carries `oneWellOperator`, `honeWellSymm`,
`honeWellEigen`, `honeWellForm`, and `honeWellGap`.  The derived theorems
`hφEnergyFromOperator`, `hgroundPolarFromOperator`, and
`hgapOrthFromOperator` feed `hφEnergyValue`, `hgroundMin`, `hgapOrth`,
`hgroundPolar`, and `hgapEnergy`; the superseded raw fields
`hφEnergySource`, `hgroundPolarSource`, and `hgapOrthSource` have been removed.
The focused `Final.lean` replay and full `lake build` pass
(`Build completed successfully (2972 jobs)`).  The literal audit has no
project `axiom` or proof `sorry`, and `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for all three capstones.

This closes the abstract Rayleigh operator interface only.  Construction of
the bounded one-well operator from the restricted fractional form, the
variational realization of its ground state, and the finite-well spectral
reductions remain open.

## 2026-09-27 — variational ground-state eigen-equation

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.hgroundPolarFromOperator`,
   `hφEnergyValue`, `hgapEnergy`, and `toSpectralInput`, followed by
   `FinalTheoremL2`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:mass`, where the
   normalized ground state is the unit-sphere minimizer of the one-well
   Rayleigh form and its first variation gives
   `A_D phi_1 = mu_1 phi_1`.
4. Promotion event: replace the raw `honeWellEigen` field by the variational
   source fields `honeWellEnergy` and `honeWellMin`, derive the eigen-equation
   with `eigenvector_of_min_unit_sphere`, and replay the unchanged
   `FinalTheoremL2` caller.
5. Sole credit: the caller-consumed variational ground-state eigen-equation.

### Acceptance result — variational ground-state eigen-equation

`L2TwoWellAux` now supplies `honeWellEnergy` and `honeWellMin`; the theorem
`honeWellEigenFromMin` derives the one-well eigen-equation and feeds
`hgroundPolarFromOperator`.  The raw `honeWellEigen` field has been removed.
The focused `Final.lean` replay and full `lake build` pass
(`Build completed successfully (2972 jobs)`).  The literal audit has no
project `axiom` or proof `sorry`, and `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for all three capstones.

This closes only the abstract variational eigen-equation bridge.  The bounded
one-well operator still has to be constructed from the restricted fractional
form, and the finite-well spectral reductions remain open.

## 2026-09-27 — bounded symmetric one-well pairing interface

1. Named final-facing theorem: `Tunneling.FinalTheoremL2`.
2. Immediate Lean consumer: `L2TwoWellAux.oneWellOperator`,
   `honeWellSymm`, `honeWellForm`, `honeWellEigenFromMin`, and
   `hgroundPolarFromOperator`, followed by `FinalTheoremL2`.
3. Exact paper source: `paper.tex`, Section 2, equation `eq:form`, where the
   Rayleigh form is represented by a symmetric bilinear form and its
   associated self-adjoint operator.
4. Promotion event: replace the raw `oneWellOperator`/`honeWellSymm` fields
   by a bounded symmetric pairing `oneWellPairing`, derive the operator and
   its Rayleigh identity from that pairing, and replay the unchanged
   `FinalTheoremL2` caller.
5. Sole credit: the caller-consumed bounded symmetric one-well pairing
   interface.

### Acceptance result — bounded symmetric one-well pairing interface

`L2TwoWellAux` now carries `oneWellPairing` and
`honeWellFormPairing`; `oneWellOperator`, `honeWellSymm`, and
`honeWellForm` are derived from `SymmetricCrossPairing.operator`,
`operator_symm`, and `operator_inner`.  The focused `Final.lean` replay and
full `lake build` pass (`Build completed successfully (2972 jobs)`).  The
literal audit has no project `axiom` or proof `sorry`, and `#print axioms`
reports only `[propext, Classical.choice, Quot.sound]` for all three
capstones.

This closes only the abstract bounded-pairing interface.  The continuous
symmetric pairing still has to be constructed from the restricted fractional
form, and the finite-well spectral reductions remain open.

## 2026-09-27 — symmetric matrix row-sum compression norm

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: the operator-norm estimate in the compression
   error slot of Lemma 4.3, through `multiWellConclusion_of_clusterCompression`
   and `FinalTheoremMultiWell`.
3. Exact paper source: `paper.tex`, Lemma 4.3, equation
   `eq:compression-error`, final paragraph: the operator norm of a real
   symmetric matrix is at most its largest absolute row sum.
4. Promotion event: formalize `maxAbsRowSum` and prove the quadratic-form
   bound
   `sum_i (sum_j A_ij x_j)^2 <= maxAbsRowSum(A)^2 * sum_j x_j^2`
   for symmetric matrices, then derive the induced Euclidean operator-norm
   bound consumed by the compression comparison.
5. Sole credit: the caller-consumed symmetric row-sum operator-norm bound.

### Acceptance result — symmetric matrix row-sum compression norm

Receipt `R43-ROWSUM-2026-09-27` records one uncredited acceptance check.
The focused `MultiWell.lean` build and the full `lake build` pass
(`Build completed successfully (2972 jobs)`).  The literal audit has no
project `axiom` or proof `sorry`.  The new results are `maxAbsRowSum`,
`le_maxAbsRowSum`, `maxAbsRowSum_nonneg`,
`symmetric_matrix_quadratic_le_maxAbsRowSum`, and
`symmetric_matrix_l2_opNorm_le_maxAbsRowSum`.

The exact consumer replay does not yet consume this theorem:
`multiWellConclusion_of_clusterCompression` and `FinalTheoremMultiWell` still
take `hcompress` as an explicit eigenvalue-comparison hypothesis.  Therefore
this closes the matrix-norm reduction from Lemma 4.3 only and earns zero
final-facing theorem-slot credit.  The first failed spine item is the missing
compression matrix and its eigenvalue comparison.  The next acceptance check
is to construct the compression matrix, derive its entrywise Taylor bounds,
and discharge `hcompress` in the unchanged `FinalTheoremMultiWell` caller.
The Taylor entrywise estimate and finite-dimensional eigenvalue comparison
remain separate analytic inputs.

## 2026-09-27 — entrywise compression norm bridge

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: the `hcompress` slot through
   `multiWellConclusion_of_clusterCompression` and `FinalTheoremMultiWell`.
3. Exact paper source: `paper.tex`, Lemma 4.3, equation
   `eq:compression-error`, especially the reduction from the entrywise
   Taylor estimates to the operator norm by the symmetric row-sum bound.
4. Promotion event: formalize the entrywise-to-row-sum estimate for the
   compression-error matrix and use the already-proved symmetric L2 norm
   bound to derive the matrix norm estimate consumed by the eigenvalue
   comparison.
5. Sole credit expected: caller-consumed entrywise compression norm bridge.

### Acceptance target

The theorem must produce the exact matrix estimate
`norm (T_L - L^(-kappa) • M_a) <= epsilon_L` from entrywise bounds
`|t_ij - L^(-kappa) m_ij| <= e_ij` and row sums
`sum_j e_ij <= epsilon_L`.  The remaining ordered-eigenvalue comparison is
kept as a named, separately source-audited input; no claim of unconditional
capstone closure is made.

### Acceptance result — entrywise compression norm bridge

`entrywise_matrix_norm_le` now proves the generic row-sum estimate
`‖T - M‖ ≤ epsilon` from symmetric error, entrywise bounds, and row sums,
using `symmetric_matrix_l2_opNorm_le_maxAbsRowSum`.  The focused
`MultiWell.lean` check passes with saved log
`/tmp/multiwell-entrywise-2026-09-27-r3.log`.

This remains zero final-facing theorem-slot credit.  The exact consumer
replay still does not consume the result: `multiWellConclusion_of_clusterCompression`
and `FinalTheoremMultiWell` retain `hcompress` as an explicit eigenvalue
comparison hypothesis, and the compression matrix `T_L` is not constructed.
The first failed spine item is therefore the ordered-eigenvalue comparison
from the matrix norm estimate.  Its immediate consumer is `hcompress` in
`multiWellConclusion_of_clusterCompression`, followed by the unchanged
`FinalTheoremMultiWell` caller.  The next acceptance check is to construct
`T_L`, discharge its entrywise Taylor estimate, and use a Weyl-type ordered
eigenvalue comparison to derive `hcompress`.

### Acceptance result — effective-matrix compression specialization

`compressionNorm_le_of_entrywise` now specializes the row-sum bridge to
`effectiveInteractionMatrix` and proves the exact Lemma 4.3 matrix estimate
`‖T - L^(-A.kappa) • M_a‖ ≤ multiWellEpsilon A a L` from entrywise Taylor
bounds and their row sums.  The focused `MultiWell.lean` check passes with
saved log `/tmp/multiwell-effective-bridge-2026-09-27-r2.log`.

This remains zero final-facing theorem-slot credit.  The theorem leaves the
actual compression matrix `T` and its Taylor hypotheses abstract, while
`multiWellConclusion_of_clusterCompression` and `FinalTheoremMultiWell`
continue to take `hcompress` explicitly.  The first failed spine item is the
ordered-eigenvalue comparison from this matrix norm to `hcompress`; its
immediate consumer remains `multiWellConclusion_of_clusterCompression`.

## 2026-09-27 — ordered eigenvalue compression comparison

1. Named final-facing theorem: `Tunneling.FinalTheoremMultiWell`.
2. Immediate Lean consumer: the `hcompress` slot in
   `multiWellConclusion_of_clusterCompression`, followed by
   `FinalTheoremMultiWell`.
3. Exact paper source: `paper.tex`, Lemma 4.3, equation
   `eq:compression-error`, where the matrix norm estimate is converted to
   the ordered eigenvalue estimate by the finite-dimensional Weyl
   comparison.
4. Promotion event: formalize the ordered-eigenvalue comparison for real
   symmetric matrices from the L2 operator norm, using the eigenvector-basis
   Rayleigh/min-max argument.
5. Sole credit expected: caller-consumed ordered-eigenvalue comparison.

### Acceptance target

For symmetric `T` and `M`, prove
`|eigenvalues₀ T k - L^(-kappa) * eigenvalues₀ M k| <= epsilon_L`
whenever `norm (T - L^(-kappa) • M) <= epsilon_L`, then discharge `hcompress`
in the unchanged `multiWellConclusion_of_clusterCompression` caller.  The
actual compression matrix and its Taylor hypotheses remain separate inputs.
