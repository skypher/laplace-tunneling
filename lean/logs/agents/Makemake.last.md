- **Proved:** `oneWellGalerkin_isHermitian` and `multiWellGalerkin_isHermitian`.
- **Blocked:** `fixedMesh_cluster`. I found no counterexample. This attempt did not complete the finite block gap and interaction/compression estimates needed to apply `MinMax.cluster_levels`.
- **Helper added:** `formBilin_comm`, by commutativity of the integrand’s two difference factors.
- **Type-checked:** The complete file below was regenerated into Lean stdin and checked with Lean 4.33. It exited successfully; the only warning was that `fixedMesh_cluster` still uses `sorry`. I did not run `lake build`.

===BEGIN FILE Tunneling/Euclid/FixedMesh.lean===
import Tunneling.Euclid.CellMatrix
import Tunneling.Euclid.Compression
import Tunneling.Spectral.Cluster
import Tunneling.Spectral.MatrixLevels
import Tunneling.Spectral.PerronFrobenius

/-!
# Fixed-mesh cluster asymptotic (paper Corollary 5.2)

`d = 1`, `0 < s < 1/2`, `D = (-1/2, 1/2)` with the uniform partition into `n`
cells of length `h = 1/n` and centres `x_α = -1/2 + (α + 1/2) h`.  The one-well
Galerkin matrix is `A_h = (B(e_α, e_β))` in the orthonormal basis
`e_α = h^{-1/2} 1_{I_α}` (entries from paper Proposition 5.1), and the
multi-well Galerkin matrix on `⋃_j (D + L a_j)` with the translated partition
is `H_{h,L}((i,α),(j,β)) = B(e_{i,α}, e_{j,β})`, `e_{i,α}` the cell vector
centred at `L a_i + x_α`.  Its ordered eigenvalues satisfy
`λ_{k,h}(L) = μ_{1,h} + L^{-1-2s} θ_{k,h} + O(L^{-3-2s} + L^{-2-4s})`.
-/

namespace Tunneling

open MeasureTheory

private theorem formBilin_comm (c kappa : ℝ) (u v : L2 1) :
    formBilin c kappa u v = formBilin c kappa v u := by
  unfold formBilin
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  ring

/-- Centres of the uniform partition of `(-1/2, 1/2)` into `n` cells. -/
noncomputable def meshCenter (n : ℕ) (α : Fin n) : ℝ := -1 / 2 + ((α : ℝ) + 1 / 2) / n

/-- The one-well Galerkin matrix `A_h`. -/
noncomputable def oneWellGalerkin (c s : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun α β =>
    formBilin c (1 + 2 * s) (cellVec (meshCenter n α) (1 / n)) (cellVec (meshCenter n β) (1 / n))

/-- The multi-well Galerkin matrix `H_{h,L}` for sites `a : ι → ℝ`. -/
noncomputable def multiWellGalerkin {ι : Type*} (c s : ℝ) (n : ℕ) (a : ι → ℝ) (L : ℝ) :
    Matrix (ι × Fin n) (ι × Fin n) ℝ :=
  Matrix.of fun p q =>
    formBilin c (1 + 2 * s) (cellVec (L * a p.1 + meshCenter n p.2) (1 / n))
      (cellVec (L * a q.1 + meshCenter n q.2) (1 / n))

theorem oneWellGalerkin_isHermitian (c s : ℝ) (n : ℕ) : (oneWellGalerkin c s n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro α β
  simp only [oneWellGalerkin, Matrix.of_apply, star_trivial]
  exact formBilin_comm c (1 + 2 * s)
    (cellVec (meshCenter n β) (1 / n)) (cellVec (meshCenter n α) (1 / n))

theorem multiWellGalerkin_isHermitian {ι : Type*} [Fintype ι] (c s : ℝ) (n : ℕ) (a : ι → ℝ)
    (L : ℝ) : (multiWellGalerkin c s n a L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  simp only [multiWellGalerkin, Matrix.of_apply, star_trivial]
  exact formBilin_comm c (1 + 2 * s)
    (cellVec (L * a q.1 + meshCenter n q.2) (1 / n))
    (cellVec (L * a p.1 + meshCenter n p.2) (1 / n))

/-- **Paper Corollary 5.2** (`cor:discrete-cluster`).  `μ_{1,h}` is the lowest
eigenvalue of `A_h`, `φ` its positive normalized eigenvector,
`m_{1,h} = ∫ Σ_α φ_α e_α = h^{1/2} Σ_α φ_α`, and `θ_{k,h}` are the ordered
eigenvalues of the effective matrix with mass `m_{1,h}`. -/
theorem fixedMesh_cluster {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (c s : ℝ) (hc : 0 < c) (hs : 0 < s ∧ s < 1 / 2) (n : ℕ) (hn : 1 ≤ n)
    (a : ι → ℝ) (ha : Function.Injective a) :
    let μ := (oneWellGalerkin_isHermitian c s n).eigenvalues₀
      (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩)
    ∃ φ : Fin n → ℝ, (∀ α, 0 < φ α) ∧ ∑ α, φ α ^ 2 = 1 ∧
      (oneWellGalerkin c s n).mulVec φ = μ • φ ∧
      ∃ C L₁ : ℝ, ∀ L : ℝ, L₁ ≤ L → ∀ k : Fin (Fintype.card ι),
        |(multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
            (Fin.rev ⟨k.val, by
              have hk := k.isLt
              rw [Fintype.card_prod, Fintype.card_fin]
              nlinarith⟩) -
          (μ + L ^ (-(1 + 2 * s)) *
            effectiveInteractionTheta a c
              ((1 / (n : ℝ)) ^ (1 / 2 : ℝ) * ∑ α, φ α) (1 + 2 * s) k)| ≤
          C * (L ^ (-3 - 2 * s) + L ^ (-2 - 4 * s)) := by
  sorry

end Tunneling
===END FILE