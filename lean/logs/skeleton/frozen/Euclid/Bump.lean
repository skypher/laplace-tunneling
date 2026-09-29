import Tunneling.Euclid.FormDomain

/-!
# Nontriviality of the form domain

An open nonempty set in `ℝ^d` (`d ≥ 1`) contains any finite number of pairwise
disjoint balls, and Lipschitz tent functions supported in these balls belong
to `H^s_0(G)` for `0 < s < 1`.  Hence the form domain has subspaces of every
finite dimension, so every Courant--Fischer level of `Q_G` is an infimum over
a nonempty family.
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- A Lipschitz tent function supported in a ball has finite Gagliardo
energy for `0 < s < 1`: the local singularity is integrable because `s < 1`
and the tail because `s > 0`. -/
theorem tent_mem_formDomain (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (x₀ : Eucl d) (r : ℝ) (hr : 0 < r) :
    ∃ f : L2 d, f ∈ formDomain ((d : ℝ) + 2 * s) (Metric.ball x₀ r) ∧ f ≠ 0 := by
  sorry

/-- The form domain of an open nonempty set has subspaces of every finite
dimension. -/
theorem exists_finrank_formDomain (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (G : Set (Eucl d)) (hG : IsOpen G) (hne : G.Nonempty) (n : ℕ) :
    ∃ W : Submodule ℝ (formDomain ((d : ℝ) + 2 * s) G), Module.finrank ℝ W = n := by
  sorry

end Tunneling
