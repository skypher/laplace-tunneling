- `oneWellGalerkin_isHermitian`: proved.
- `multiWellGalerkin_isHermitian`: proved.
- `fixedMesh_cluster`: blocked in this attempt. For `n = 1`, `cluster_levels` cannot be applied directly: its required extra dimension is unavailable. I added a checked ordered-eigenvalue shift lemma for a direct Weyl comparison, but did not complete the matrix-to-compression reduction. I found no counterexample to the theorem.
- Helper added: private `eigenvalues₀_add_smul`.
- Type-checked the complete delivered file through `lean --stdin`. It reports no errors; it still reports that `fixedMesh_cluster` uses `sorry`.

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

private theorem eigenvalues₀_add_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ c : ℝ) (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (hDdef : D = μ • (1 : Matrix ι ι ℝ) + c • A) (hc : 0 < c)
    (k : Fin (Fintype.card ι)) :
    hD.eigenvalues₀ k = μ + c * hA.eigenvalues₀ k := by
  have hmat : D = (c • A) - Matrix.scalar ι (-μ) := by
    rw [hDdef]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar, Matrix.smul_apply]
      ring
    · have hdiag : Matrix.diagonal (fun _ : ι => -μ) i j = 0 :=
        Matrix.diagonal_apply_ne _ hij
      simp [Matrix.one_apply_ne hij, hdiag, Matrix.smul_apply]
  have hrootsC : (c • A).charpoly.roots =
      A.charpoly.roots.map (fun x => c * x) := by
    rw [charpoly_smul_eq_scaleRoots]
    exact Polynomial.roots_scaleRoots A.charpoly
      (isUnit_iff_ne_zero.mpr (ne_of_gt hc))
  have hrootsShift :
      ((c • A) - Matrix.scalar ι (-μ)).charpoly.roots =
        ((c • A).charpoly.roots).map (fun x => x + μ) := by
    calc
      _ = ((c • A).charpoly.comp (Polynomial.X + Polynomial.C (-μ))).roots := by
        rw [Matrix.charpoly_sub_scalar]
      _ = _ := by
        have hp : Polynomial.X + Polynomial.C (-μ) =
            Polynomial.C (1:ℝ) * Polynomial.X + Polynomial.C (-μ) := by simp
        rw [hp]
        simpa [one_mul, sub_eq_add_neg] using
          (Polynomial.roots_comp_C_mul_X_add_C
            ((c • A).charpoly) 1 (-μ) isUnit_one)
  have hroots :
      D.charpoly.roots =
        A.charpoly.roots.map (fun x => c * x + μ) := by
    rw [hmat, hrootsShift, hrootsC]
    simp [Multiset.map_map]
  have hre :
      (D.charpoly.roots.map RCLike.re) =
        (A.charpoly.roots.map RCLike.re).map (fun x => μ + c * x) := by
    rw [hroots]
    simp only [Multiset.map_map]
    congr 1
    funext x
    change c * x + μ = μ + c * x
    ring
  have hAsort := hA.sort_roots_charpoly_eq_eigenvalues₀
  have hDsort := hD.sort_roots_charpoly_eq_eigenvalues₀
  have horder : ∀ a ∈ A.charpoly.roots.map RCLike.re,
      ∀ b ∈ A.charpoly.roots.map RCLike.re,
        (a ≥ b) ↔ (μ + c * a ≥ μ + c * b) := by
    intro a ha b hb
    constructor
    · intro hab
      have hm : c * b ≤ c * a := mul_le_mul_of_nonneg_left hab hc.le
      nlinarith
    · intro hab
      have hm : c * b ≤ c * a := by nlinarith
      exact le_of_mul_le_mul_left hm hc
  have hsortmap : List.map (μ + c * ·)
      ((A.charpoly.roots.map RCLike.re).sort (· ≥ ·)) =
      ((A.charpoly.roots.map RCLike.re).map (μ + c * ·)).sort (· ≥ ·) :=
    Multiset.map_sort _ _ _ _ horder
  have hlist : List.map (μ + c * ·) (List.ofFn hA.eigenvalues₀) =
      List.ofFn (fun i => μ + c * hA.eigenvalues₀ i) := by
    rw [List.map_ofFn]
    rfl
  have heq : List.ofFn hD.eigenvalues₀ =
      List.ofFn (fun i => μ + c * hA.eigenvalues₀ i) := by
    rw [← hDsort, hre, ← hsortmap, hAsort]
    exact hlist
  exact congrFun (List.ofFn_inj.mp heq) k

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
===END FILE Tunneling/Euclid/FixedMesh.lean