- `oneWellGalerkin_isHermitian`: proved; statement unchanged.
- `multiWellGalerkin_isHermitian`: proved; statement unchanged.
- `fixedMesh_cluster`: **not proved in this submission**. I found no counterexample or missing hypothesis. The remaining gap is the finite block cluster argument and its compression estimate; I did not complete that formalization.
- Helpers added: mesh spacing, strict concavity/off-diagonal negativity, and normalized positive one-well ground data, including the `n = 1` case.
- Type-checked the complete file below with Lean 4.33 via `lean --stdin`: no errors; Lean reported the remaining `sorry` warning in `fixedMesh_cluster`.

===BEGIN FILE Tunneling/Euclid/FixedMesh.lean===
```lean
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
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

private theorem meshCenter_gap {n : ℕ} (hn : 0 < n) (α β : Fin n) (hab : α ≠ β) :
    1 / (n : ℝ) ≤ |meshCenter n α - meshCenter n β| := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiff : meshCenter n α - meshCenter n β = ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ) := by
    simp only [meshCenter]
    ring
  rw [hdiff, abs_div, abs_of_pos hnR]
  rcases lt_or_gt_of_ne hab with h | h
  · have hval : α.val < β.val := Fin.lt_def.mp h
    have hsucc : α.val + 1 ≤ β.val := Nat.succ_le_of_lt hval
    have hreal : (α.val : ℝ) + 1 ≤ (β.val : ℝ) := by exact_mod_cast hsucc
    have hgap : 1 ≤ (β.val : ℝ) - (α.val : ℝ) := by linarith
    rw [abs_of_nonpos (by linarith : (α.val : ℝ) - (β.val : ℝ) ≤ 0)]
    exact div_le_div_of_nonneg_right
      (by linarith : 1 ≤ -((α.val : ℝ) - (β.val : ℝ))) hnR.le
  · have hval : β.val < α.val := Fin.lt_def.mp h
    have hsucc : β.val + 1 ≤ α.val := Nat.succ_le_of_lt hval
    have hreal : (β.val : ℝ) + 1 ≤ (α.val : ℝ) := by exact_mod_cast hsucc
    have hgap : 1 ≤ (α.val : ℝ) - (β.val : ℝ) := by linarith
    rw [abs_of_nonneg (by linarith : 0 ≤ (α.val : ℝ) - (β.val : ℝ))]
    exact div_le_div_of_nonneg_right hgap hnR.le

private theorem meshSecondDiff_pos {q r h : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hh : 0 < h) (hr : h ≤ r) :
    0 < 2 * r ^ q - (r + h) ^ q - (r - h) ^ q := by
  have hx : 0 ≤ r + h := by linarith
  have hy : 0 ≤ r - h := by linarith
  have hxy : r + h ≠ r - h := by linarith
  have hj : (1 / 2 : ℝ) • ((r + h) ^ q) + (1 / 2 : ℝ) • ((r - h) ^ q) <
      ((1 / 2 : ℝ) • (r + h) + (1 / 2 : ℝ) • (r - h)) ^ q := by
    exact (Real.strictConcaveOn_rpow hq hq1).2 hx hy hxy
      (by norm_num) (by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) • (r + h) + (1 / 2 : ℝ) • (r - h) = r := by
    simp only [smul_eq_mul]
    ring
  rw [hmid, smul_eq_mul, smul_eq_mul] at hj
  nlinarith

private theorem oneWellGalerkin_offdiag_neg (c s : ℝ) (hc : 0 < c)
    (hs : 0 < s ∧ s < 1 / 2) (n : ℕ) (hn : 0 < n) (α β : Fin n) (hab : α ≠ β) :
    oneWellGalerkin c s n α β < 0 := by
  have hh : 0 < 1 / (n : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hn)
  have hr : 1 / (n : ℝ) ≤ |meshCenter n α - meshCenter n β| :=
    meshCenter_gap hn α β hab
  have hq : 0 < 1 - 2 * s := by linarith
  have hq1 : 1 - 2 * s < 1 := by linarith
  have hsecond := meshSecondDiff_pos hq hq1 hh hr
  have hden : 0 < 2 * s * (1 - 2 * s) := mul_pos (mul_pos (by norm_num) hs.1) hq
  have hfrac : 0 <
      (2 * |meshCenter n α - meshCenter n β| ^ (1 - 2 * s) -
        (|meshCenter n α - meshCenter n β| + 1 / (n : ℝ)) ^ (1 - 2 * s) -
        (|meshCenter n α - meshCenter n β| - 1 / (n : ℝ)) ^ (1 - 2 * s)) /
        (2 * s * (1 - 2 * s)) := div_pos hsecond hden
  rw [oneWellGalerkin, Matrix.of_apply,
    cellMatrix_offdiag c s hs (meshCenter n α) (meshCenter n β) (1 / (n : ℝ)) hh hr]
  have hcoef : 0 < c / (1 / (n : ℝ)) := div_pos hc hh
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hcoef) hfrac

private theorem oneWell_groundData (c s : ℝ) (hc : 0 < c) (hs : 0 < s ∧ s < 1 / 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : Fin n → ℝ, (∀ α, 0 < φ α) ∧ ∑ α, φ α ^ 2 = 1 ∧
      (oneWellGalerkin c s n).mulVec φ =
        ((oneWellGalerkin_isHermitian c s n).eigenvalues₀
          (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩)) • φ := by
  classical
  let A := oneWellGalerkin c s n
  let hA := oneWellGalerkin_isHermitian c s n
  let k0 : Fin (Fintype.card (Fin n)) := Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩
  let μ := hA.eigenvalues₀ k0
  by_cases hn2 : 2 ≤ n
  · have hN : 2 ≤ Fintype.card (Fin n) := by simpa using hn2
    have hoff : ∀ α β : Fin n, α ≠ β → A α β < 0 := by
      intro α β hab
      exact oneWellGalerkin_offdiag_neg c s hc hs n (by omega) α β hab
    obtain ⟨_, φ, hpos, hnorm, heig⟩ := ground_simple_of_neg_offdiag A hA hN hoff
    exact ⟨φ, hpos, hnorm, heig⟩
  · have hn1 : n = 1 := by omega
    subst n
    let φ : Fin 1 → ℝ := fun _ => 1
    let ei : Fin 1 → Fin (Fintype.card (Fin 1)) :=
      fun i => (Fintype.equivOfCardEq (Fintype.card_fin 1)).symm i
    have ht' : oneWellGalerkin c s 1 0 0 = hA.eigenvalues₀ (ei 0) := by
      simpa [Matrix.trace, Matrix.IsHermitian.eigenvalues, ei] using hA.trace_eq_sum_eigenvalues
    have hidx : ei 0 = k0 := by
      apply Fin.ext
      have hlt : (ei 0).val < 1 := by simpa [ei] using (ei 0).isLt
      have hk : k0.val = 0 := by simp [k0, Fin.rev]
      omega
    have hμ : μ = A 0 0 := by
      change hA.eigenvalues₀ k0 = A 0 0
      calc
        hA.eigenvalues₀ k0 = hA.eigenvalues₀ (ei 0) := by rw [hidx]
        _ = oneWellGalerkin c s 1 0 0 := ht'.symm
        _ = A 0 0 := rfl
    refine ⟨φ, ?_, ?_, ?_⟩
    · intro α
      fin_cases α
      norm_num [φ]
    · norm_num [φ]
    · have hsingle : A.mulVec φ = A 0 0 • φ := by
        ext α
        fin_cases α
        simp [Matrix.mulVec, dotProduct, φ, A, oneWellGalerkin, Matrix.of_apply, Fin.sum_univ_one]
      change A.mulVec φ = μ • φ
      calc
        A.mulVec φ = A 0 0 • φ := hsingle
        _ = μ • φ := by rw [← hμ]

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
  classical
  obtain ⟨φ, hφpos, hφnorm, hφeig⟩ := oneWell_groundData c s hc hs n hn
  refine ⟨φ, hφpos, hφnorm, hφeig, ?_⟩
  sorry

end Tunneling
```