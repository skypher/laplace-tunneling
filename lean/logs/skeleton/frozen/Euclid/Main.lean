import Tunneling.Euclid.GroundState
import Tunneling.Euclid.Decomp
import Tunneling.Euclid.Compression
import Tunneling.Spectral.Cluster
import Tunneling.Final
import Tunneling.Euclid.MainAux
import Tunneling.Euclid.DecompForm
import Tunneling.Euclid.DecompBound

/-!
# The main theorems for the restricted fractional Laplacian on `ℝ^d`

All objects are the concrete ones of the paper:

* `eigenvalue c κ G k` is the `(k+1)`-st eigenvalue of the restricted
  fractional Laplacian `A_G` (Courant--Fischer level of the closed form
  `eq:form` on `H^s_0(G)`), with `κ = d + 2s`;
* `μ₁ = eigenvalue c κ D 0`, `μ₂ = eigenvalue c κ D 1`, `g = μ₂ - μ₁`;
* `φ` is the normalized nonnegative ground state of `A_D` and
  `m₁ = ∫ φ`.

`multiWell_main` is paper Theorem 4.3 (`thm:multi-well`) and `twoWell_main`
is paper Theorem 3.3 (`thm:two-well`).
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

section MultiWell

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The exact cluster comparison `eq:exact-cluster-comparison` together with
the cluster-edge bounds, for the eigenvalues of `A_{Ω_{a,L}}` and the ordered
eigenvalues `τ_k(L)` of the exact compression matrix `T_L`. -/
theorem multiWell_cluster (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (a : ι → Eucl d) (L : ℝ) (hL : 0 < L)
    (hsep : ∀ i j : ι, i ≠ j → 4 * R ≤ L * ‖a i - a j‖)
    (hsmall : multiWellGamma (oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ) a L ≤
      (oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ).gap / 4) :
    let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
    let hT := multiWellCompressionMatrix_isHermitian (volume : Measure (Eucl d))
      A.kappa A.c (φ : Eucl d → ℝ) a L
    (∀ k : Fin (Fintype.card ι),
      -(2 * multiWellGamma A a L ^ 2 / A.gap) ≤
          eigenvalue A.c A.kappa (multiWellDomain D a L) k.val -
            (A.mu1 + hT.eigenvalues₀ (Fin.rev k)) ∧
        eigenvalue A.c A.kappa (multiWellDomain D a L) k.val -
            (A.mu1 + hT.eigenvalues₀ (Fin.rev k)) ≤ 0) ∧
      (∀ k : Fin (Fintype.card ι), |hT.eigenvalues₀ k| ≤ multiWellGamma A a L) ∧
      A.mu1 + A.gap - multiWellGamma A a L ≤
        eigenvalue A.c A.kappa (multiWellDomain D a L) (Fintype.card ι) := by
  sorry

/-- **Paper Theorem 4.3** (`thm:multi-well`): finite multi-well effective
interaction matrix.  For a bounded open `D ⊆ B_R(0)`, distinct sites `a`, the
eigenvalues of the restricted fractional Laplacian on
`Ω_{a,L} = ⋃_j (D + L a_j)` satisfy, whenever `L δ_a ≥ 4R` and `γ_L ≤ g/4`,

* `|λ_k(Ω) - (μ₁ + L^{-κ} θ_k)| ≤ ε_L + 2γ_L²/g` for `1 ≤ k ≤ N`,
* `λ_N(Ω) ≤ μ₁ + γ_L`, `λ_{N+1}(Ω) ≥ μ₁ + g - γ_L`,
  `λ_{N+1}(Ω) - λ_N(Ω) ≥ g - 2γ_L`,

and `L^{d+2s} (λ_k(Ω) - μ₁) → θ_k` as `L → ∞`, where `θ_1 ≤ ... ≤ θ_N` are
the eigenvalues of the effective matrix `M_a` of equation
`eq:effective-matrix`. -/
theorem multiWell_main (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (a : ι → Eucl d) (ha : ∀ i j : ι, i ≠ j → a i ≠ a j) :
    let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
    multiWellStatement A a (effectiveInteractionTheta a A.c A.phiMass A.kappa)
      (fun L k => eigenvalue A.c A.kappa (multiWellDomain D a L) k) := by
  sorry

end MultiWell

section TwoWell

/-- **Paper Theorem 3.3** (`thm:two-well`): two-well algebraic splitting.  For
a bounded open `D ⊆ B_R(0)`, a unit vector `e`, and `L ≥ L₀`
(equation `eq:explicit-L0`), the eigenvalues of the restricted fractional
Laplacian on `Ω_L` satisfy `eq:lambda1`, `eq:lambda2`,
`eq:two-well-third-level`, the limit `eq:gap-limit`, and the first two
eigenvalues are simple: `λ₁(Ω_L) < λ₂(Ω_L) < λ₃(Ω_L)`.  Central symmetry of
`D` is not needed for these conclusions (compare paper Corollaries 4.4
and 4.6). -/
theorem twoWell_main (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (e : Eucl d) (he : ‖e‖ = 1) :
    let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
    A.twoWellStatement (fun L k => eigenvalue A.c A.kappa (twoWellDomain D e L) k) ∧
      ∀ L : ℝ, A.L0 ≤ L →
        eigenvalue A.c A.kappa (twoWellDomain D e L) 0 <
            eigenvalue A.c A.kappa (twoWellDomain D e L) 1 ∧
          eigenvalue A.c A.kappa (twoWellDomain D e L) 1 <
            eigenvalue A.c A.kappa (twoWellDomain D e L) 2 := by
  sorry

/-- Paper Theorem 3.3 with its exact hypothesis list: `D` is additionally
centrally symmetric (`D = -D`). -/
theorem twoWell_main_centrallySymmetric (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (_hDsymm : ∀ x, x ∈ D ↔ -x ∈ D)
    (φ : L2 d) (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (e : Eucl d) (he : ‖e‖ = 1) :
    let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
    A.twoWellStatement (fun L k => eigenvalue A.c A.kappa (twoWellDomain D e L) k) ∧
      ∀ L : ℝ, A.L0 ≤ L →
        eigenvalue A.c A.kappa (twoWellDomain D e L) 0 <
            eigenvalue A.c A.kappa (twoWellDomain D e L) 1 ∧
          eigenvalue A.c A.kappa (twoWellDomain D e L) 1 <
            eigenvalue A.c A.kappa (twoWellDomain D e L) 2 :=
  twoWell_main hd s hs c hc R hR D hDo hDne hDR φ hφ e he

end TwoWell

end Tunneling
