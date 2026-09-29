import Tunneling.Euclid.Decomp

/-!
# The exact block identity of paper Lemma 4.1
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace WellGeometry

variable (G : WellGeometry d ι)

/-- The exact block identity of Lemma 4.1 in the sense of closed forms. -/
theorem formQ_eq (c : ℝ) (ψ : formDomain G.κ G.Ω) :
    formQ c G.κ G.Ω ψ = G.Q0 c ψ + G.interaction c ψ ψ := by
  sorry

theorem interaction_symm (c : ℝ) (ψ χ : formDomain G.κ G.Ω) :
    G.interaction c ψ χ = G.interaction c χ ψ := by
  sorry

end WellGeometry

end Tunneling
