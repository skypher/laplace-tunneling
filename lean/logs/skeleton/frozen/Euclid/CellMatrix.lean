import Tunneling.Euclid.FormDomain

/-!
# Exact cell-integral Galerkin matrix (paper Proposition 5.1)

On the line (`d = 1`) with `0 < s < 1/2` and `q = 1 - 2s`, the normalized
indicator `e = h^{-1/2} 1_I` of a cell `I` of length `h` has finite form
energy, and the entries of the Galerkin matrix of the zero-exterior form are

  `B(e_α, e_α) = (c/h) · 2 h^q / (2 s q)`,
  `B(e_α, e_β) = -(c/h) · (2 r^q - (r + h)^q - (r - h)^q) / (2 s q)`,
    `r = |x_α - x_β| ≥ h`,

where `B(u, v) = (c/2) ∬ (u(x) - u(y)) (v(x) - v(y)) |x - y|^{-1-2s}` is the
bilinear form of `eq:form` (so `B(u, u) = Q_G[u]` and
`polar Q_G u v = 2 B(u, v)`).
-/

namespace Tunneling

open MeasureTheory

/-- The cell of length `h` centred at `a` on the line `ℝ = Eucl 1`. -/
def lineCell (a h : ℝ) : Set (Eucl 1) := {x | |x 0 - a| < h / 2}

theorem measurableSet_lineCell (a h : ℝ) : MeasurableSet (lineCell a h) := by
  sorry

theorem volume_lineCell (a h : ℝ) (hh : 0 ≤ h) :
    volume (lineCell a h) = ENNReal.ofReal h := by
  sorry

theorem volume_lineCell_ne_top (a h : ℝ) : volume (lineCell a h) ≠ ⊤ := by
  sorry

/-- The `L²`-normalized cell indicator `e = h^{-1/2} 1_I`. -/
noncomputable def cellVec (a h : ℝ) : L2 1 :=
  (h ^ (-(1 / 2 : ℝ))) • indicatorConstLp 2 (measurableSet_lineCell a h)
    (volume_lineCell_ne_top a h) (1 : ℝ)

/-- The bilinear form of the zero-exterior form on `L²(ℝ)`. -/
noncomputable def formBilin (c κ : ℝ) (u v : L2 1) : ℝ :=
  c / 2 * ∫ z : Eucl 1 × Eucl 1,
    ((u : Eucl 1 → ℝ) z.1 - (u : Eucl 1 → ℝ) z.2) *
      ((v : Eucl 1 → ℝ) z.1 - (v : Eucl 1 → ℝ) z.2) *
        gagliardoKernel κ z.1 z.2 ∂(volume.prod volume)

theorem norm_cellVec (a h : ℝ) (hh : 0 < h) : ‖cellVec a h‖ = 1 := by
  sorry

/-- Cell indicators have finite form energy when `s < 1/2`. -/
theorem cellVec_mem_formDomain (s : ℝ) (hs : 0 < s ∧ s < 1 / 2) (a h : ℝ) (hh : 0 < h)
    (G : Set (Eucl 1)) (hG : lineCell a h ⊆ G) :
    cellVec a h ∈ formDomain (1 + 2 * s) G := by
  sorry

/-- `B` is half the polar form of `Q_G` on the form domain. -/
theorem formBilin_eq_polar (c κ : ℝ) (G : Set (Eucl 1)) (u v : formDomain κ G) :
    formBilin c κ (u : L2 1) (v : L2 1) = QuadraticMap.polar (formQ c κ G) u v / 2 := by
  sorry

/-- Paper equation `eq:cell-diagonal`. -/
theorem cellMatrix_diag (c s : ℝ) (hs : 0 < s ∧ s < 1 / 2) (a h : ℝ) (hh : 0 < h) :
    formBilin c (1 + 2 * s) (cellVec a h) (cellVec a h) =
      c / h * (2 * h ^ (1 - 2 * s) / (2 * s * (1 - 2 * s))) := by
  sorry

/-- Paper equation `eq:cell-offdiagonal`. -/
theorem cellMatrix_offdiag (c s : ℝ) (hs : 0 < s ∧ s < 1 / 2) (a b h : ℝ) (hh : 0 < h)
    (hab : h ≤ |a - b|) :
    formBilin c (1 + 2 * s) (cellVec a h) (cellVec b h) =
      -(c / h) * ((2 * |a - b| ^ (1 - 2 * s) - (|a - b| + h) ^ (1 - 2 * s) -
        (|a - b| - h) ^ (1 - 2 * s)) / (2 * s * (1 - 2 * s))) := by
  sorry

end Tunneling
