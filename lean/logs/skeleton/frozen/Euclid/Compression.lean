import Tunneling.Euclid.FormDomain
import Tunneling.MultiWell

/-!
# The compression error on `ℝ^d` (paper Lemma 4.3)

The Taylor estimate `eq:multi-taylor` holds for `|x|, |y| ≤ R`.  On `ℝ^d` the
ground state is supported in `D ⊆ B_R(0)`, so the pointwise hypothesis
`∀ x : X, ‖x‖ ≤ R` of `multiWellCompressionMatrix_entry_error` is replaced by
the support condition `u x ≠ 0 → ‖x‖ ≤ R`.
-/

namespace Tunneling

open MeasureTheory

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise compression error of Lemma 4.3 on `ℝ^d`. -/
theorem compression_entry_error_euclid (A : TwoWellConstants) (a : ι → Eucl d)
    (u : Eucl d → ℝ) (L : ℝ) (i j : ι) (hL : 0 < L)
    (hsep : ∀ p q : ι, p ≠ q → 4 * A.R ≤ L * ‖a p - a q‖)
    (hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ A.R)
    (hint : Integrable u (volume : Measure (Eucl d)))
    (hmass : ∫ x, u x = A.phiMass) (hnonneg : ∀ x, 0 ≤ u x) :
    |multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L i j -
      L ^ (-A.kappa) * effectiveInteractionMatrix a A.c A.phiMass A.kappa i j| ≤
      (if i = j then 0
        else A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) *
          ‖a i - a j‖ ^ (-A.kappa - 2)) := by
  sorry

/-- Operator-norm form of Lemma 4.3 on `ℝ^d`:
`‖T_L - L^{-κ} M_a‖ ≤ ε_L`. -/
theorem compression_norm_le_euclid (A : TwoWellConstants) (a : ι → Eucl d)
    (u : Eucl d → ℝ) (L : ℝ) (hL : 0 < L)
    (hsep : ∀ p q : ι, p ≠ q → 4 * A.R ≤ L * ‖a p - a q‖)
    (hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ A.R)
    (hint : Integrable u (volume : Measure (Eucl d)))
    (hmass : ∫ x, u x = A.phiMass) (hnonneg : ∀ x, 0 ≤ u x) :
    ‖multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L -
      L ^ (-A.kappa) • effectiveInteractionMatrix a A.c A.phiMass A.kappa‖ ≤
      multiWellEpsilon A a L := by
  sorry

/-- The two-sided kernel bound gives `-t_{ij}(L) ≥ c m₁² (L|a_i - a_j| + 2R)^{-κ}`
for `i ≠ j` (used for the simplicity statement of paper Theorem 3.3). -/
theorem compression_entry_le_euclid (A : TwoWellConstants) (a : ι → Eucl d)
    (u : Eucl d → ℝ) (L : ℝ) (i j : ι) (hij : i ≠ j) (hL : 0 < L)
    (hsep : ∀ p q : ι, p ≠ q → 4 * A.R ≤ L * ‖a p - a q‖)
    (hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ A.R)
    (hint : Integrable u (volume : Measure (Eucl d)))
    (hmass : ∫ x, u x = A.phiMass) (hnonneg : ∀ x, 0 ≤ u x) :
    multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L i j ≤
      -(A.c * A.phiMass ^ 2 * (L * ‖a i - a j‖ + 2 * A.R) ^ (-A.kappa)) := by
  sorry

end Tunneling
