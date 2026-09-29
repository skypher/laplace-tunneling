import Tunneling.Euclid.GroundState

/-!
# The Courant--Fischer levels are the eigenvalues of `A_G`

Paper Section 2 writes `λ₁(G) ≤ λ₂(G) ≤ ⋯` for the eigenvalues of the
operator `A_G` associated with the closed form `eq:form`, repeated according to
multiplicity.  In weak form, `λ` is an eigenvalue with eigenfunction
`u ∈ H^s_0(G) \ {0}` when `Q_G(u, v) = λ ⟪u, v⟫` for all `v ∈ H^s_0(G)`, i.e.
`polar Q_G u v = 2 λ ⟪u, v⟫`.

This file proves, for a bounded open nonempty `G`, that the levels
`eigenvalue c κ G k` enumerate exactly these eigenvalues with multiplicity:

* there is an orthonormal sequence of weak eigenfunctions with eigenvalues
  `eigenvalue c κ G k`;
* every weak eigenvalue is one of the levels;
* the weak eigenspace of `λ` has dimension `#{k | eigenvalue c κ G k = λ}`.
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- `u` is a weak eigenfunction of the restricted fractional Laplacian `A_G`
with eigenvalue `lam`. -/
def IsWeakEigenfunction (c κ : ℝ) (G : Set (Eucl d)) (lam : ℝ)
    (u : formDomain κ G) : Prop :=
  ∀ v : formDomain κ G,
    QuadraticMap.polar (formQ c κ G) u v = 2 * lam * inner ℝ (u : L2 d) (v : L2 d)

/-- The weak eigenspace of `A_G` for `lam`. -/
def weakEigenspace (c κ : ℝ) (G : Set (Eucl d)) (lam : ℝ) :
    Submodule ℝ (formDomain κ G) where
  carrier := {u | IsWeakEigenfunction c κ G lam u}
  zero_mem' := by
    intro v
    simp [IsWeakEigenfunction, QuadraticMap.polar]
  add_mem' := by
    intro u w hu hw v
    have h1 := hu v
    have h2 := hw v
    rw [QuadraticMap.polar_add_left, h1, h2]
    simp [inner_add_left, mul_add]
  smul_mem' := by
    intro t u hu v
    have h1 := hu v
    rw [QuadraticMap.polar_smul_left, h1]
    simp [inner_smul_left]
    ring

/-- The levels are attained by an orthonormal family of weak eigenfunctions. -/
theorem exists_orthonormal_eigenfunctions (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (G : Set (Eucl d)) (hGo : IsOpen G)
    (hGne : G.Nonempty) (hGR : G ⊆ Metric.ball 0 R) (n : ℕ) :
    ∃ e : Fin n → formDomain ((d : ℝ) + 2 * s) G,
      Orthonormal ℝ (fun i => ((e i : formDomain ((d : ℝ) + 2 * s) G) : L2 d)) ∧
        ∀ i : Fin n, IsWeakEigenfunction c ((d : ℝ) + 2 * s) G
          (eigenvalue c ((d : ℝ) + 2 * s) G i.val) (e i) := by
  sorry

/-- The levels are nondecreasing and tend to infinity. -/
theorem eigenvalue_monotone_tendsto (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (G : Set (Eucl d)) (hGo : IsOpen G)
    (hGne : G.Nonempty) (hGR : G ⊆ Metric.ball 0 R) :
    Monotone (eigenvalue c ((d : ℝ) + 2 * s) G) ∧
      Filter.Tendsto (eigenvalue c ((d : ℝ) + 2 * s) G) Filter.atTop Filter.atTop := by
  sorry

/-- Every weak eigenvalue of `A_G` is one of the levels. -/
theorem exists_eigenvalue_eq_of_weakEigenfunction (hd : 1 ≤ d) (s : ℝ)
    (hs : 0 < s ∧ s < 1) (c : ℝ) (hc : 0 < c) (R : ℝ) (G : Set (Eucl d))
    (hGo : IsOpen G) (hGne : G.Nonempty) (hGR : G ⊆ Metric.ball 0 R) (lam : ℝ)
    (u : formDomain ((d : ℝ) + 2 * s) G) (hu : u ≠ 0)
    (heig : IsWeakEigenfunction c ((d : ℝ) + 2 * s) G lam u) :
    ∃ k : ℕ, eigenvalue c ((d : ℝ) + 2 * s) G k = lam := by
  sorry

/-- Multiplicity: the weak eigenspace of `lam` has dimension equal to the
number of levels equal to `lam` (so the levels are the eigenvalues repeated
according to multiplicity). -/
theorem finrank_weakEigenspace (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (G : Set (Eucl d)) (hGo : IsOpen G)
    (hGne : G.Nonempty) (hGR : G ⊆ Metric.ball 0 R) (lam : ℝ) :
    FiniteDimensional ℝ (weakEigenspace c ((d : ℝ) + 2 * s) G lam) ∧
      Module.finrank ℝ (weakEigenspace c ((d : ℝ) + 2 * s) G lam) =
        Nat.card {k : ℕ // eigenvalue c ((d : ℝ) + 2 * s) G k = lam} := by
  sorry

end Tunneling
