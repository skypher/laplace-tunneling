import Tunneling.Euclid.Bump
import Tunneling.Euclid.Compactness
import Tunneling.Euclid.Sign

/-!
# The one-well ground state

Paper Section 2 uses, for a bounded open `D ⊆ B_R(0)`:

* `μ₁ = λ₁(D) < μ₂ = λ₂(D)` (simplicity of the first eigenvalue);
* a normalized nonnegative ground state `φ₁` with `A_D φ₁ = μ₁ φ₁` and
  mass `m₁ = ∫ φ₁ > 0` (equation `eq:mass`).

The paper cites [DiNezzaPalatucciValdinoci2012, Theorems 5.4 and 7.1] and
[BrascoParini2016, Theorem 2.8] for these facts; here they are proved from the
compactness of the form embedding (`Tunneling.Euclid.Compactness`) and the
sign property of minimizers (`Tunneling.Euclid.Sign`).  In this file `μ₁` and
`μ₂` are the Courant--Fischer levels `eigenvalue c κ D 0` and
`eigenvalue c κ D 1`.
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- `φ` is the normalized nonnegative ground state of `A_D`
(paper equation `eq:mass`): it lies in the form domain, has unit `L²` norm,
nonnegative values, and attains the lowest level `μ₁`. -/
structure IsPositiveGroundState (c κ : ℝ) (D : Set (Eucl d)) (φ : L2 d) : Prop where
  mem : φ ∈ formDomain κ D
  norm_eq_one : ‖φ‖ = 1
  energy_eq : formQ c κ D ⟨φ, mem⟩ = eigenvalue c κ D 0
  nonneg : 0 ≤ᵐ[volume] (φ : Eucl d → ℝ)

theorem formQ_bddBelow (c κ : ℝ) (hc : 0 ≤ c) (G : Set (Eucl d)) :
    ∃ m : ℝ, ∀ v : formDomain κ G, m * ‖v‖ ^ 2 ≤ formQ c κ G v :=
  ⟨0, fun v => by simpa using formQ_nonneg c κ hc G v⟩

/-- Existence of the normalized nonnegative ground state. -/
theorem exists_positiveGroundState (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) :
    ∃ φ : L2 d, IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ := by
  sorry

/-- The weak eigen-equation `A_D φ₁ = μ₁ φ₁` in form sense. -/
theorem IsPositiveGroundState.polar_eq (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) {φ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (v : formDomain ((d : ℝ) + 2 * s) D) :
    QuadraticMap.polar (formQ c ((d : ℝ) + 2 * s) D) ⟨φ, hφ.mem⟩ v =
      2 * eigenvalue c ((d : ℝ) + 2 * s) D 0 * inner ℝ φ (v : L2 d) := by
  sorry

/-- Simplicity of the first eigenvalue: `μ₁ < μ₂`. -/
theorem eigenvalue_zero_lt_one (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) :
    eigenvalue c ((d : ℝ) + 2 * s) D 0 < eigenvalue c ((d : ℝ) + 2 * s) D 1 := by
  sorry

/-- The spectral-gap inequality on the orthogonal complement of the ground
state: `Q_D[v] ≥ μ₂ ‖v‖²` for `v ⊥ φ₁`. -/
theorem IsPositiveGroundState.gap (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) {φ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (v : formDomain ((d : ℝ) + 2 * s) D) (hv : inner ℝ φ (v : L2 d) = 0) :
    eigenvalue c ((d : ℝ) + 2 * s) D 1 * ‖(v : L2 d)‖ ^ 2 ≤
      formQ c ((d : ℝ) + 2 * s) D v := by
  sorry

/-- The ground-state mass `m₁ = ∫ φ₁` is positive. -/
theorem IsPositiveGroundState.mass_pos (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) {φ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ) :
    0 < ∫ x, φ x := by
  sorry

/-- The ground state is integrable (it is square integrable and supported in
the bounded set `D`). -/
theorem IsPositiveGroundState.integrable (s : ℝ) (c : ℝ) (R : ℝ) (D : Set (Eucl d))
    (hDR : D ⊆ Metric.ball 0 R) {φ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ) :
    Integrable (φ : Eucl d → ℝ) := by
  sorry

/-- Uniqueness of the normalized nonnegative ground state. -/
theorem IsPositiveGroundState.unique (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) {φ ψ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (hψ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D ψ) : φ = ψ := by
  sorry

end Tunneling
