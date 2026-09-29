import Tunneling.Euclid.FormDomain

/-!
# Absolute values and the sign of minimizers

For real `a, b`,
`|a - b|² - ||a| - |b||² = 2 (|a| |b| - a b) = 4 (a⁺ b⁻ + a⁻ b⁺)`.
Hence `[|u|] ≤ [u]`, and equality forces `u⁺(x) u⁻(y) = 0` for a.e.
`(x, y)`, because the Gagliardo kernel is positive off the diagonal.  By
Tonelli this means that `u⁺ = 0` a.e. or `u⁻ = 0` a.e.  This is the linear case
of the ground-state argument cited from [BrascoParini2016, Theorem 2.8].
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- The absolute value `|f|` of an `L²` function. -/
noncomputable def absL2 (f : L2 d) : L2 d :=
  (Lp.memLp f).norm.toLp (fun x => ‖(f : Eucl d → ℝ) x‖)

theorem absL2_ae (f : L2 d) :
    ((absL2 f : L2 d) : Eucl d → ℝ) =ᵐ[volume] fun x => |f x| := by
  sorry

theorem norm_absL2 (f : L2 d) : ‖absL2 f‖ = ‖f‖ := by
  sorry

theorem absL2_nonneg (f : L2 d) : 0 ≤ᵐ[volume] ((absL2 f : L2 d) : Eucl d → ℝ) := by
  sorry

theorem absL2_mem_formDomain (κ : ℝ) (G : Set (Eucl d)) {f : L2 d}
    (hf : f ∈ formDomain κ G) : absL2 f ∈ formDomain κ G := by
  sorry

theorem gagliardoSeminormSq_absL2_le (κ : ℝ) (G : Set (Eucl d)) {f : L2 d}
    (hf : f ∈ formDomain κ G) :
    gagliardoSeminormSq κ (volume : Measure (Eucl d)) ((absL2 f : L2 d) : Eucl d → ℝ) ≤
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ) := by
  sorry

/-- Equality of the energies of `u` and `|u|` forces a constant sign. -/
theorem ae_nonneg_or_nonpos_of_gagliardoSeminormSq_absL2_eq (hd : 1 ≤ d) (κ : ℝ)
    (G : Set (Eucl d)) {f : L2 d} (hf : f ∈ formDomain κ G)
    (heq : gagliardoSeminormSq κ (volume : Measure (Eucl d))
        ((absL2 f : L2 d) : Eucl d → ℝ) =
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ)) :
    (0 ≤ᵐ[volume] (f : Eucl d → ℝ)) ∨ ((f : Eucl d → ℝ) ≤ᵐ[volume] 0) := by
  sorry

end Tunneling
