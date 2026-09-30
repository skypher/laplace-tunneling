import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Tunneling.MultiWell
import Tunneling.Perturbation

/-!
# Ground states of symmetric matrices with negative off-diagonal entries

Paper Corollaries 4.9 and 5.2 use the Rayleigh-quotient form of the
Perron--Frobenius argument: for a real symmetric matrix whose off-diagonal
entries are strictly negative, the lowest eigenvalue is simple and has an
eigenvector with strictly positive entries.
-/

open WithLp

namespace Tunneling

private noncomputable def qmat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : QuadraticMap ℝ (EuclideanSpace ℝ ι) ℝ :=
  (Matrix.toQuadraticForm' A).comp (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap

private theorem qmat_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    qmat A x = ∑ i, ∑ j, x i * x j * A i j := by
  simp [qmat, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply]
  congr 2 with i
  congr 2 with j
  ring

private theorem qmat_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    qmat A x = inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap x) x := by
  rw [qmat_sum, EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.toEuclideanLin_apply, dotProduct, Matrix.mulVec_apply_eq_sum,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

private theorem lowerquad {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hN : 2 ≤ Fintype.card ι)
    (x : EuclideanSpace ℝ ι) :
    hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩) * ‖x‖ ^ 2 ≤
      inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap x) x := by
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := Matrix.toEuclideanLin A
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let hdim : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
  let k0 : Fin (Fintype.card ι) := Fin.rev ⟨0, by omega⟩
  have hk0 (k : Fin (Fintype.card ι)) : k ≤ k0 := by
    apply Fin.le_iff_val_le_val.mpr
    simp [k0, Fin.rev]
    omega
  have hm (k : Fin (Fintype.card ι)) (hk : k ∈ Set.univ) :
      hA.eigenvalues₀ k0 ≤ hT.eigenvalues hdim k := by
    have hv := hA.eigenvalues₀_antitone (hk0 k)
    change hA.eigenvalues₀ k0 ≤ hA.eigenvalues₀ k
    exact hv
  let b := hT.eigenvectorBasis hdim
  have hbspan : Submodule.span ℝ (b.toBasis '' (Set.univ : Set (Fin (Fintype.card ι)))) = ⊤ := by
    rw [Set.image_univ]
    exact b.toBasis.span_eq
  have hx : x ∈ Submodule.span ℝ (b.toBasis ''
      (Set.univ : Set (Fin (Fintype.card ι)))) := by
    rw [hbspan]
    exact Submodule.mem_top
  have h := rayleigh_ge_on_eigenvectorSpan T hT hdim
    (hA.eigenvalues₀ k0) Set.univ hm x hx
  simpa [T, k0] using h

private theorem abs_ground {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hN : 2 ≤ Fintype.card ι)
    (hoff : ∀ i j, i ≠ j → A i j < 0)
    (x : EuclideanSpace ℝ ι)
    (hxnorm : ‖x‖ = 1)
    (heig : (Matrix.toEuclideanLin A) x =
      hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩) • x) :
    (∀ i, 0 < |x i|) ∧
      ‖(WithLp.toLp 2 (fun i => |x i|) : EuclideanSpace ℝ ι)‖ = 1 ∧
      (Matrix.toEuclideanLin A) (WithLp.toLp 2 (fun i => |x i|) : EuclideanSpace ℝ ι) =
        hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩) •
          (WithLp.toLp 2 (fun i => |x i|) : EuclideanSpace ℝ ι) := by
  let θ := hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩)
  let p : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => |x i|)
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hpSq : ‖p‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, p i ^ 2 = ∑ i, x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [p, sq_abs]
      _ = ‖x‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq x).symm
      _ = 1 := by rw [hxnorm]; norm_num
  have hpNorm : ‖p‖ = 1 := by nlinarith [norm_nonneg p]
  have hQle : qmat A p ≤ qmat A x := by
    rw [qmat_sum, qmat_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i = j
    · subst j
      have heq : |x i| * |x i| * A i i = x i * x i * A i i := by
        calc
          |x i| * |x i| * A i i = (|x i|) ^ 2 * A i i := by ring
          _ = (x i) ^ 2 * A i i := by rw [sq_abs]
          _ = x i * x i * A i i := by ring
      exact le_of_eq heq
    · change |x i| * |x j| * A i j ≤ x i * x j * A i j
      have hprod : x i * x j ≤ |x i| * |x j| := by
        calc
          x i * x j ≤ |x i * x j| := le_abs_self _
          _ = |x i| * |x j| := abs_mul _ _
      calc
        |x i| * |x j| * A i j = A i j * (|x i| * |x j|) := by ring
        _ ≤ A i j * (x i * x j) := mul_le_mul_of_nonpos_left hprod (hoff i j hij).le
        _ = x i * x j * A i j := by ring
  have heigC : ((Matrix.toEuclideanLin A).toContinuousLinearMap) x = θ • x := by
    simpa [θ] using heig
  have hxQ : qmat A x = θ := by
    rw [qmat_inner, heigC, real_inner_smul_left, real_inner_self_eq_norm_mul_norm, hxnorm]
    ring
  have hlower := lowerquad A hA hN p
  rw [← qmat_inner, hpNorm] at hlower
  norm_num at hlower
  have hpEnergy : qmat A p = θ := by
    apply le_antisymm
    · calc
        qmat A p ≤ qmat A x := hQle
        _ = θ := hxQ
    · nlinarith [hlower]
  have hmin : ∀ ψ : EuclideanSpace ℝ ι, ‖ψ‖ = 1 → qmat A p ≤ qmat A ψ := by
    intro ψ hψ
    have hlowerψ := lowerquad A hA hN ψ
    rw [← qmat_inner, hψ] at hlowerψ
    norm_num at hlowerψ
    rw [hpEnergy]
    exact hlowerψ
  have hsym : ∀ y z : EuclideanSpace ℝ ι,
      inner ℝ (T y) z = inner ℝ y (T z) := by
    intro y z
    exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) y z
  have hpEig : T p = θ • p :=
    GroundStatePerturbation.eigenvector_of_min_unit_sphere T (qmat A) p θ
      (qmat_inner A) hsym hpNorm hpEnergy hmin
  have hpMat : A.mulVec p.ofLp = θ • p.ofLp := by
    have hh := congrArg (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) hpEig
    simpa [T, Matrix.ofLp_toEuclideanLin_apply] using hh
  have hcoord (i : ι) : ∑ j, A i j * p j = θ * p i := by
    have hh := congrFun hpMat i
    simpa [Matrix.mulVec_apply_eq_sum] using hh
  have hpos : ∀ i, 0 < |x i| := by
    intro i
    by_contra hi
    have hpi : p i = 0 := by
      have habs : |x i| = 0 := by
        have := abs_nonneg (x i)
        exact le_antisymm (le_of_not_gt hi) this
      simp [p, habs]
    have hex : ∃ j, p j ^ 2 ≠ 0 := by
      by_contra h
      have hz : ∀ j, p j ^ 2 = 0 := by simpa using h
      have hs : ∑ j, p j ^ 2 = 0 := by simp [hz]
      have hs' : ∑ j, p j ^ 2 = 1 := by
        rw [← EuclideanSpace.real_norm_sq_eq, hpNorm]
        norm_num
      linarith
    obtain ⟨j, hj⟩ := hex
    have hpj : p j ≠ 0 := by
      intro hz
      rw [hz] at hj
      norm_num at hj
    have hpjpos : 0 < p j := by
      have hnonneg : 0 ≤ p j := by simp [p]
      exact lt_of_le_of_ne hnonneg (Ne.symm hpj)
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hpj hpi
    have hsumle : ∀ k, A i k * p k ≤ 0 := by
      intro k
      by_cases hik : i = k
      · subst k
        simp [hpi]
      · exact mul_nonpos_of_nonpos_of_nonneg (hoff i k hik).le (by simp [p])
    have hsumlt : ∑ k, A i k * p k < 0 := by
      have hs := Finset.sum_lt_sum (s := Finset.univ)
        (fun k hk => hsumle k)
        ⟨j, Finset.mem_univ _, mul_neg_of_neg_of_pos (hoff i j (Ne.symm hji)) hpjpos⟩
      simpa using hs
    have hzero : ∑ k, A i k * p k = 0 := by
      simpa [hpi] using hcoord i
    linarith
  exact ⟨hpos, hpNorm, by simpa [T, p, θ] using hpEig⟩


 /-- The lowest eigenvalue `hA.eigenvalues₀ (Fin.rev 0)` of a real symmetric
matrix with strictly negative off-diagonal entries is simple and has a
normalized eigenvector with strictly positive entries. -/
theorem ground_simple_of_neg_offdiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hN : 2 ≤ Fintype.card ι)
    (hoff : ∀ i j, i ≠ j → A i j < 0) :
    hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩) < hA.eigenvalues₀ (Fin.rev ⟨1, by omega⟩) ∧
      ∃ z : ι → ℝ, (∀ i, 0 < z i) ∧ ∑ i, z i ^ 2 = 1 ∧
        A.mulVec z = hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩) • z := by
  classical
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := Matrix.toEuclideanLin A
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let hdim : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
  let k0 : Fin (Fintype.card ι) := Fin.rev ⟨0, by omega⟩
  let k1 : Fin (Fintype.card ι) := Fin.rev ⟨1, by omega⟩
  let b := hT.eigenvectorBasis hdim
  let θ := hA.eigenvalues₀ k0
  have hk10 : k1 < k0 := by
    apply Fin.lt_iff_val_lt_val.mpr
    simp [k0, k1, Fin.rev]
    omega
  have hle : θ ≤ hA.eigenvalues₀ k1 :=
    hA.eigenvalues₀_antitone (le_of_lt hk10)
  have huNorm : ‖b k0‖ = 1 := by simp [b]
  have huEig : T (b k0) = θ • b k0 := by
    have h := hT.apply_eigenvectorBasis hdim k0
    change T (b k0) = θ • b k0
    exact h
  have hgap : θ < hA.eigenvalues₀ k1 := by
    by_contra hnot
    have heq : θ = hA.eigenvalues₀ k1 := le_antisymm hle (not_lt.mp hnot)
    have hvEig : T (b k1) = θ • b k1 := by
      have h := hT.apply_eigenvectorBasis hdim k1
      have hv : hT.eigenvalues hdim k1 = θ := by
        change hA.eigenvalues₀ k1 = θ
        exact heq.symm
      rw [hv] at h
      exact h
    have hnonempty : Nonempty ι :=
      Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
    let i0 : ι := Classical.choice hnonempty
    by_cases hu0 : b k0 i0 = 0
    · have hpos := (abs_ground A hA hN hoff (b k0) huNorm huEig).1 i0
      simpa [hu0] using hpos
    · let y : EuclideanSpace ℝ ι :=
        (b k1 i0) • b k0 - (b k0 i0) • b k1
      have hycoord : y i0 = 0 := by
        calc
          y i0 = (b k1 i0) * (b k0 i0) - (b k0 i0) * (b k1 i0) := by simp [y]
          _ = 0 := by ring
      have hne : k0 ≠ k1 := ne_of_gt hk10
      have huv : inner ℝ (b k0) (b k1) = 0 := b.inner_eq_zero hne
      have hvv : inner ℝ (b k1) (b k1) = 1 := b.inner_eq_one k1
      have hyinner : inner ℝ y (b k1) = -(b k0 i0) := by
        change inner ℝ ((b k1 i0) • b k0 - (b k0 i0) • b k1) (b k1) = _
        simp only [inner_sub_left, real_inner_smul_left, huv, hvv]
        ring
      have hyne : y ≠ 0 := by
        intro hyzero
        have hzero : inner ℝ y (b k1) = 0 := by simp [hyzero]
        rw [hyinner] at hzero
        exact hu0 (by linarith)
      have hyEig : T y = θ • y := by
        change T ((b k1 i0) • b k0 - (b k0 i0) • b k1) =
          θ • ((b k1 i0) • b k0 - (b k0 i0) • b k1)
        simp only [map_sub, map_smul, huEig, hvEig, smul_sub, smul_smul]
        congr 1 <;> ring
      have hyNormPos : 0 < ‖y‖ := norm_pos_iff.mpr hyne
      let q : EuclideanSpace ℝ ι := ‖y‖⁻¹ • y
      have hqNorm : ‖q‖ = 1 := by
        change ‖‖y‖⁻¹ • y‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyNormPos)]
        exact inv_mul_cancel₀ hyNormPos.ne'
      have hqEig : T q = θ • q := by
        change T (‖y‖⁻¹ • y) = θ • (‖y‖⁻¹ • y)
        rw [map_smul, hyEig]
        simp [smul_smul, mul_comm]
      have hqcoord : q i0 = 0 := by
        change (‖y‖⁻¹) • y i0 = 0
        rw [hycoord]
        simp
      have hpos := (abs_ground A hA hN hoff q hqNorm hqEig).1 i0
      simpa [hqcoord] using hpos
  refine ⟨hgap, ?_⟩
  let x : EuclideanSpace ℝ ι := b k0
  have hxNorm : ‖x‖ = 1 := huNorm
  have hxEig : T x = θ • x := huEig
  have hposData := abs_ground A hA hN hoff x hxNorm hxEig
  let p : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => |x i|)
  let z : ι → ℝ := p.ofLp
  refine ⟨z, ?_, ?_, ?_⟩
  · intro i
    simpa [z, p] using hposData.1 i
  · calc
      ∑ i, z i ^ 2 = ‖p‖ ^ 2 := by
        simpa [z] using (EuclideanSpace.real_norm_sq_eq p).symm
      _ = 1 := by rw [hposData.2.1]; norm_num
  · have hh := congrArg (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) hposData.2.2
    simpa [z, Matrix.ofLp_toEuclideanLin_apply] using hh

end Tunneling
