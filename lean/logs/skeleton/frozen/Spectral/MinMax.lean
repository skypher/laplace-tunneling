import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Courant--Fischer levels of a quadratic form

For a real inner product space `V` (not necessarily complete) and a quadratic
map `Q` on `V`, the level of index `k` (counted from `0`) is

  `level Q k = inf { sup { Q u : u ∈ W, ‖u‖ = 1 } : W ≤ V, dim W = k + 1 }`.

For the closed form of a self-adjoint operator with compact resolvent, whose
form domain is `V`, these are the eigenvalues repeated according to
multiplicity (paper, Section 2).  This file only records the two elementary
halves of the min--max principle used in the paper: test-subspace upper bounds
and orthogonality lower bounds.
-/

namespace Tunneling
namespace MinMax

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Rayleigh supremum of `Q` over the unit sphere of the subspace `W`. -/
noncomputable def rayleighSup (Q : QuadraticMap ℝ V ℝ) (W : Submodule ℝ V) : ℝ :=
  ⨆ u : {u : W // ‖(u : V)‖ = 1}, Q (u : V)

/-- The Courant--Fischer level of index `k` (the `(k+1)`-st eigenvalue). -/
noncomputable def level (Q : QuadraticMap ℝ V ℝ) (k : ℕ) : ℝ :=
  ⨅ W : {W : Submodule ℝ V // Module.finrank ℝ W = k + 1}, rayleighSup Q W

/-- A quadratic map is bounded on the unit sphere of a finite-dimensional
subspace. -/
theorem bddAbove_unitSphere (Q : QuadraticMap ℝ V ℝ) (W : Submodule ℝ V)
    [FiniteDimensional ℝ W] :
    BddAbove (Set.range fun u : {u : W // ‖(u : V)‖ = 1} => Q (u : V)) := by
  sorry

/-- Upper bound for the Rayleigh supremum from a homogeneous bound. -/
theorem rayleighSup_le (Q : QuadraticMap ℝ V ℝ) (W : Submodule ℝ V)
    (hW : 0 < Module.finrank ℝ W) (a : ℝ)
    (h : ∀ u ∈ W, Q u ≤ a * ‖u‖ ^ 2) :
    rayleighSup Q W ≤ a := by
  sorry

/-- Every unit vector of a finite-dimensional subspace is below the Rayleigh
supremum. -/
theorem le_rayleighSup (Q : QuadraticMap ℝ V ℝ) (W : Submodule ℝ V)
    [FiniteDimensional ℝ W] (u : V) (hu : u ∈ W) (hnorm : ‖u‖ = 1) :
    Q u ≤ rayleighSup Q W := by
  sorry

/-- Min--max upper bound: a `(k+1)`-dimensional test subspace on which
`Q ≤ a ‖·‖²` gives `level Q k ≤ a`.  The lower bound `hbdd` makes the
infimum well defined. -/
theorem level_le (Q : QuadraticMap ℝ V ℝ) (k : ℕ)
    (hbdd : ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v)
    (W : Submodule ℝ V) (hW : Module.finrank ℝ W = k + 1) (a : ℝ)
    (h : ∀ u ∈ W, Q u ≤ a * ‖u‖ ^ 2) :
    level Q k ≤ a := by
  sorry

/-- Max--min lower bound: if `Q ≥ a ‖·‖²` on the orthogonal complement of
`k` vectors, then `a ≤ level Q k`, provided a `(k+1)`-dimensional subspace
exists. -/
theorem le_level (Q : QuadraticMap ℝ V ℝ) (k : ℕ) (e : Fin k → V) (a : ℝ)
    (h : ∀ v : V, (∀ i, inner ℝ (e i) v = 0) → a * ‖v‖ ^ 2 ≤ Q v)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = k + 1) :
    a ≤ level Q k := by
  sorry

/-- The lowest level is below the energy of every unit vector. -/
theorem level_zero_le (Q : QuadraticMap ℝ V ℝ)
    (hbdd : ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v)
    (u : V) (hu : ‖u‖ = 1) :
    level Q 0 ≤ Q u := by
  sorry

/-- The lowest level is a lower bound for the Rayleigh quotient. -/
theorem level_zero_mul_le (Q : QuadraticMap ℝ V ℝ)
    (hbdd : ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v) (v : V) :
    level Q 0 * ‖v‖ ^ 2 ≤ Q v := by
  sorry

/-- Near-optimal test subspaces exist above every level. -/
theorem exists_subspace_of_level_lt (Q : QuadraticMap ℝ V ℝ) (k : ℕ)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = k + 1) (a : ℝ)
    (h : level Q k < a) :
    ∃ W : Submodule ℝ V, Module.finrank ℝ W = k + 1 ∧
      ∀ u ∈ W, Q u ≤ a * ‖u‖ ^ 2 := by
  sorry

/-- The levels are nondecreasing. -/
theorem level_mono (Q : QuadraticMap ℝ V ℝ) (k : ℕ)
    (hbdd : ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = k + 2) :
    level Q k ≤ level Q (k + 1) := by
  sorry

/-- Subspaces of every smaller dimension exist. -/
theorem exists_finrank_of_le {n m : ℕ} (hmn : m ≤ n)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = n) :
    ∃ W : Submodule ℝ V, Module.finrank ℝ W = m := by
  sorry

end MinMax
end Tunneling
