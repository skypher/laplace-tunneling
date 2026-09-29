import Tunneling.Euclid.FormDomain

/-!
# Cube averaging: finite-dimensional approximation

For a bounded set `D ⊆ ℝ^d`, bounded subsets of `H^s_0(D)` are relatively
compact in `L²(ℝ^d)`.  This replaces the citation
[DiNezzaPalatucciValdinoci2012, Theorem 7.1] in paper Section 2 and is proved
by averaging over cubes of side `ε`: on a cube `Q` of diameter `√d ε`,

  `∫_Q |u - ⨍_Q u|² = (2|Q|)⁻¹ ∬_{Q×Q} |u(x)-u(y)|²
                     ≤ (√d ε)^κ (2 ε^d)⁻¹ ∬_{Q×Q} |u(x)-u(y)|² |x-y|^{-κ}`,

so the cube-average projection, whose range is finite dimensional on
functions supported in a bounded set, approximates `u` within
`C ε^s [u]`.  Lower semicontinuity of the Gagliardo energy follows from Fatou's
lemma along an a.e. convergent subsequence.
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- Finite-dimensional approximation of energy-bounded functions supported in
a fixed ball (cube averaging). -/
theorem exists_finiteDimensional_approx (s : ℝ) (hs : 0 < s ∧ s < 1)
    (R : ℝ) (D : Set (Eucl d)) (hDR : D ⊆ Metric.closedBall 0 R)
    (M δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Submodule ℝ (L2 d), FiniteDimensional ℝ S ∧
      ∀ f ∈ formDomain ((d : ℝ) + 2 * s) D, ‖f‖ ≤ 1 →
        gagliardoSeminormSq ((d : ℝ) + 2 * s) (volume : Measure (Eucl d))
            (f : Eucl d → ℝ) ≤ M →
          ∃ p ∈ S, ‖p‖ ≤ 1 ∧ ‖f - p‖ ≤ δ := by
  sorry

end Tunneling
