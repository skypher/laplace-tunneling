import Tunneling.Euclid.Main

/-!
# Corollaries of the main theorems (paper Corollaries 3.4 and 4.4--4.8)
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- **Paper Corollary 3.4** (`cor:distant-ball`): for `D = B_R(0)`,
`L^{d+2s} (λ₂(Ω_L) - λ₁(B_R)) → c m₁²`. -/
theorem distantBall_rate (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) (Metric.ball (0 : Eucl d) R) φ)
    (e : Eucl d) (he : ‖e‖ = 1) :
    Filter.Tendsto
      (fun L : ℝ => L ^ ((d : ℝ) + 2 * s) *
        (eigenvalue c ((d : ℝ) + 2 * s) (twoWellDomain (Metric.ball (0 : Eucl d) R) e L) 1 -
          eigenvalue c ((d : ℝ) + 2 * s) (Metric.ball (0 : Eucl d) R) 0))
      Filter.atTop (nhds (c * (∫ x, φ x) ^ 2)) := by
  sorry

/-- **Paper Corollary 4.4** (`cor:symmetry-free-two`): two arbitrary distinct
sites, no symmetry of `D`.  With `r = |a₁ - a₂|`,
`λ₁,₂(Ω_L) = μ₁ ∓ c m₁² r^{-κ} L^{-κ} + O(L^{-κ-2} + L^{-2κ})` and
`L^{d+2s}(λ₂ - λ₁) → 2 c m₁² r^{-d-2s}`. -/
theorem symmetryFree_twoWell (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (a : Fin 2 → Eucl d) (ha : a 0 ≠ a 1) :
    let κ : ℝ := (d : ℝ) + 2 * s
    let μ₁ := eigenvalue c κ D 0
    let m := ∫ x, φ x
    let r := ‖a 0 - a 1‖
    (∃ C L₁ : ℝ, ∀ L : ℝ, L₁ ≤ L →
      |eigenvalue c κ (multiWellDomain D a L) 0 - (μ₁ - c * m ^ 2 * r ^ (-κ) * L ^ (-κ))| ≤
          C * (L ^ (-κ - 2) + L ^ (-2 * κ)) ∧
        |eigenvalue c κ (multiWellDomain D a L) 1 - (μ₁ + c * m ^ 2 * r ^ (-κ) * L ^ (-κ))| ≤
          C * (L ^ (-κ - 2) + L ^ (-2 * κ))) ∧
      Filter.Tendsto
        (fun L : ℝ => L ^ κ * (eigenvalue c κ (multiWellDomain D a L) 1 -
          eigenvalue c κ (multiWellDomain D a L) 0))
        Filter.atTop (nhds (2 * c * m ^ 2 * r ^ (-κ))) := by
  sorry

/-- **Paper Corollary 4.6** (`cor:multi-two`): for `a₁ = -e/2`, `a₂ = e/2`
the multi-well error `ε_L + 2γ_L²/g` equals the two-well remainder. -/
theorem multiTwo_remainder (A : TwoWellConstants) (e : Eucl d) (he : ‖e‖ = 1) (L : ℝ) :
    multiWellEpsilon A (twoWellSites e) L +
        2 * multiWellGamma A (twoWellSites e) L ^ 2 / A.gap =
      A.remainder L := by
  sorry

/-- **Paper Corollary 4.7** (`cor:collective-ground`), matrix part: `θ₁ < 0`
is simple with an eigenvector of positive entries, and `θ_N > 0`. -/
theorem collectiveGround_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (a : ι → Eucl d) (ha : ∀ i j : ι, i ≠ j → a i ≠ a j)
    (c m κ : ℝ) (hc : 0 < c) (hm : 0 < m) :
    let θ := effectiveInteractionTheta a c m κ
    θ ⟨0, by omega⟩ < 0 ∧ θ ⟨0, by omega⟩ < θ ⟨1, by omega⟩ ∧
      0 < θ ⟨Fintype.card ι - 1, by omega⟩ ∧
      ∃ z : ι → ℝ, (∀ i, 0 < z i) ∧
        (effectiveInteractionMatrix a c m κ).mulVec z = θ ⟨0, by omega⟩ • z := by
  sorry

/-- **Paper Corollary 4.7**, spectral part: `λ₁(Ω_{a,L})` is simple for every
`L > 0`, and `λ₁(Ω_{a,L}) < μ₁ < λ_N(Ω_{a,L})` for all large `L`. -/
theorem collectiveGround_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (a : ι → Eucl d) (ha : ∀ i j : ι, i ≠ j → a i ≠ a j) :
    let κ : ℝ := (d : ℝ) + 2 * s
    (∀ L : ℝ, 0 < L →
      eigenvalue c κ (multiWellDomain D a L) 0 < eigenvalue c κ (multiWellDomain D a L) 1) ∧
      ∀ᶠ L in Filter.atTop,
        eigenvalue c κ (multiWellDomain D a L) 0 < eigenvalue c κ D 0 ∧
          eigenvalue c κ D 0 < eigenvalue c κ (multiWellDomain D a L) (Fintype.card ι - 1) := by
  sorry

/-- **Paper Corollary 4.8** (`cor:simplex`): equidistant sites.  Then
`N ≤ d + 1`, `θ₁ = -(N-1) w` and `θ₂ = ⋯ = θ_N = w` with `w = c m₁² r^{-κ}`. -/
theorem simplex_cluster {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hN : 1 ≤ Fintype.card ι) (a : ι → Eucl d) (r : ℝ) (hr : 0 < r)
    (hdist : ∀ i j : ι, i ≠ j → ‖a i - a j‖ = r) (c m κ : ℝ) (hc : 0 ≤ c) :
    let w := c * m ^ 2 * r ^ (-κ)
    Fintype.card ι ≤ d + 1 ∧
      effectiveInteractionTheta a c m κ ⟨0, by omega⟩ = -((Fintype.card ι - 1 : ℝ) * w) ∧
      ∀ k : Fin (Fintype.card ι), k.val ≠ 0 → effectiveInteractionTheta a c m κ k = w := by
  sorry

end Tunneling
