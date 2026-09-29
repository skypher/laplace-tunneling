import Tunneling.Euclid.Decomp

/-!
# The interaction bound `eq:gamma-L` and the exact compression `eq:exact-compression`
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace WellGeometry

variable (G : WellGeometry d ι)

/-- The operator-norm bound `‖𝒱_L‖ ≤ γ_L` of equation `eq:gamma-L`. -/
theorem abs_interaction_le (c : ℝ) (hc : 0 ≤ c) (ψ χ : formDomain G.κ G.Ω) :
    |G.interaction c ψ χ| ≤
      c * 2 ^ G.κ * (volume G.D).toReal * sigmaKappa G.a G.κ * G.L ^ (-G.κ) *
        ‖(ψ : L2 d)‖ * ‖(χ : L2 d)‖ := by
  sorry

/-- The compression of `𝒱_L` to the translated ground states is the matrix
`T_L` of equation `eq:exact-compression`. -/
theorem interaction_Φ (c : ℝ) (φ : formDomain G.κ G.D) (i j : ι) :
    G.interaction c (G.Φ φ i) (G.Φ φ j) =
      multiWellCompressionMatrix (volume : Measure (Eucl d)) G.κ c
        ((φ : L2 d) : Eucl d → ℝ) G.a G.L i j := by
  sorry

end WellGeometry

end Tunneling
