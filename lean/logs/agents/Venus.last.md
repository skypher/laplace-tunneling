- `cluster_levels`: proved, replacing the original `sorry`.
- Added private helpers for the cluster embedding, projection and residual, quadratic form bounds, compressed matrix identity, and Young’s inequality.
- Type-checked the complete replacement through Lean 4.33.0 via `--stdin`; exit code 0, no errors or `sorry` warnings. Lean emitted only linter and deprecation warnings. The read-only sandbox left the repository file untouched.

===BEGIN FILE Tunneling/Spectral/Cluster.lean===
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Tunneling.Spectral.MinMax
import Tunneling.MultiWell

/-!
# The isolated spectral-cluster bound

This file formalizes paper Lemma 4.2 (`lem:cluster`) in the Courant--Fischer
language of `Tunneling.MinMax`.  The unperturbed form `Q₀` has the `N`
orthonormal vectors `φ i` as eigenvectors with eigenvalue `μ` (weak
eigen-equation `heig`) and the gap `hgap` on their orthogonal complement.  The
perturbation is a bounded symmetric bilinear form `w`, and the compression of
`w` to `span φ` is the matrix `T`.
-/

namespace Tunneling
namespace MinMax

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private def clusterEmbed {ι : Type*} [Fintype ι] (φ : ι → V) :
    EuclideanSpace ℝ ι →ₗ[ℝ] V where
  toFun z := ∑ i, z i • φ i
  map_add' z y := by simp [Finset.sum_add_distrib, add_smul]
  map_smul' a z := by simp [Finset.smul_sum, smul_smul]

private theorem clusterEmbed_coeff
    {ι : Type*} [Fintype ι] (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (z : EuclideanSpace ℝ ι) (i : ι) :
    inner ℝ (φ i) (clusterEmbed φ z) = z i := by
  simpa [clusterEmbed] using hφ.inner_right_fintype z i

private theorem clusterEmbed_inner
    {ι : Type*} [Fintype ι] (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (z : EuclideanSpace ℝ ι) (v : V) :
    inner ℝ (clusterEmbed φ z) v =
      ∑ i, z i * inner ℝ (φ i) v := by
  simp [clusterEmbed, sum_inner, inner_smul_left]

private theorem clusterEmbed_pairing
    {ι : Type*} [Fintype ι] (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (clusterEmbed φ x) (clusterEmbed φ y) = inner ℝ x y := by
  calc
    inner ℝ (clusterEmbed φ x) (clusterEmbed φ y) =
        ∑ i, x i * inner ℝ (φ i) (clusterEmbed φ y) :=
      clusterEmbed_inner φ hφ x _
    _ = ∑ i, x i * y i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [clusterEmbed_coeff φ hφ]
    _ = inner ℝ x y := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.inner_apply]

private theorem clusterEmbed_norm_sq
    {ι : Type*} [Fintype ι] (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (z : EuclideanSpace ℝ ι) :
    ‖clusterEmbed φ z‖ ^ 2 = ‖z‖ ^ 2 := by
  calc
    ‖clusterEmbed φ z‖ ^ 2 =
        inner ℝ (clusterEmbed φ z) (clusterEmbed φ z) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ z z := clusterEmbed_pairing φ hφ z z
    _ = ‖z‖ ^ 2 := real_inner_self_eq_norm_sq _

private theorem clusterEmbed_injective
    {ι : Type*} [Fintype ι] (φ : ι → V) (hφ : Orthonormal ℝ φ) :
    Function.Injective (clusterEmbed φ) := by
  intro x y hxy
  ext i
  calc
    x i = inner ℝ (φ i) (clusterEmbed φ x) :=
      (clusterEmbed_coeff φ hφ x i).symm
    _ = inner ℝ (φ i) (clusterEmbed φ y) := congrArg (inner ℝ (φ i)) hxy
    _ = y i := clusterEmbed_coeff φ hφ y i

private theorem clusterPolar_embed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q₀ : QuadraticMap ℝ V ℝ) (φ : ι → V) (μ : ℝ)
    (heig : ∀ (i : ι) (v : V),
      QuadraticMap.polar Q₀ (φ i) v = 2 * μ * inner ℝ (φ i) v)
    (z : EuclideanSpace ℝ ι) (v : V) :
    QuadraticMap.polar Q₀ (clusterEmbed φ z) v =
      2 * μ * inner ℝ (clusterEmbed φ z) v := by
  classical
  have hsum : ∀ s : Finset ι,
      QuadraticMap.polar Q₀ (∑ i ∈ s, z i • φ i) v =
        2 * μ * inner ℝ (∑ i ∈ s, z i • φ i) v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [QuadraticMap.polar]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, QuadraticMap.polar_add_left,
          QuadraticMap.polar_smul_left, heig, ih, inner_add_left, inner_smul_left]
        simp [smul_eq_mul]
        ring
  simpa [clusterEmbed] using hsum Finset.univ

private theorem clusterQ0_embed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q₀ : QuadraticMap ℝ V ℝ) (φ : ι → V) (μ : ℝ)
    (heig : ∀ (i : ι) (v : V),
      QuadraticMap.polar Q₀ (φ i) v = 2 * μ * inner ℝ (φ i) v)
    (z : EuclideanSpace ℝ ι) :
    Q₀ (clusterEmbed φ z) = μ * ‖clusterEmbed φ z‖ ^ 2 := by
  have hp := clusterPolar_embed Q₀ φ μ heig z (clusterEmbed φ z)
  have hq : 2 * Q₀ (clusterEmbed φ z) =
      2 * μ * ‖clusterEmbed φ z‖ ^ 2 := by
    simpa [QuadraticMap.polar_self, nsmul_eq_mul, real_inner_self_eq_norm_sq] using hp
  nlinarith

private def clusterCoeff {ι : Type*} [Fintype ι] (φ : ι → V) (v : V) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => inner ℝ (φ i) v

private def clusterProjection {ι : Type*} [Fintype ι] (φ : ι → V) (v : V) : V :=
  clusterEmbed φ (clusterCoeff φ v)

private def clusterResidual {ι : Type*} [Fintype ι] (φ : ι → V) (v : V) : V :=
  v - clusterProjection φ v

private theorem clusterResidual_orthogonal
    {ι : Type*} [Fintype ι] (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (v : V) (i : ι) :
    inner ℝ (φ i) (clusterResidual φ v) = 0 := by
  change inner ℝ (φ i) (v - clusterEmbed φ (clusterCoeff φ v)) = 0
  rw [inner_sub_right, clusterEmbed_coeff φ hφ]
  simp [clusterCoeff]

private theorem clusterNorm_decomp
    {ι : Type*} [Fintype ι] (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (v : V) :
    ‖v‖ ^ 2 =
      ‖clusterProjection φ v‖ ^ 2 + ‖clusterResidual φ v‖ ^ 2 := by
  have hpr : inner ℝ (clusterProjection φ v) (clusterResidual φ v) = 0 := by
    rw [clusterProjection, clusterEmbed_inner φ hφ]
    apply Finset.sum_eq_zero
    intro i hi
    rw [clusterResidual_orthogonal φ hφ]
    simp
  have hsum : clusterProjection φ v + clusterResidual φ v = v := by
    simp [clusterResidual]
  calc
    ‖v‖ ^ 2 = ‖clusterProjection φ v + clusterResidual φ v‖ ^ 2 := by
      rw [hsum]
    _ = ‖clusterProjection φ v‖ ^ 2 + ‖clusterResidual φ v‖ ^ 2 := by
      rw [norm_add_sq_real, hpr]
      ring

private theorem clusterQ0_projection_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q₀ : QuadraticMap ℝ V ℝ) (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (μ g : ℝ) (hg : 0 < g)
    (heig : ∀ (i : ι) (v : V),
      QuadraticMap.polar Q₀ (φ i) v = 2 * μ * inner ℝ (φ i) v)
    (hgap : ∀ v : V, (∀ i, inner ℝ (φ i) v = 0) →
      (μ + g) * ‖v‖ ^ 2 ≤ Q₀ v)
    (v : V) :
    μ * ‖clusterProjection φ v‖ ^ 2 +
      (μ + g) * ‖clusterResidual φ v‖ ^ 2 ≤ Q₀ v := by
  let p := clusterProjection φ v
  let r := clusterResidual φ v
  have hsum : p + r = v := by simp [p, r, clusterResidual]
  have hpEq : p = clusterEmbed φ (clusterCoeff φ v) := rfl
  have hpQ : Q₀ p = μ * ‖p‖ ^ 2 := by
    rw [hpEq, clusterQ0_embed Q₀ φ μ heig, clusterEmbed_norm_sq φ hφ]
  have hpolar : QuadraticMap.polar Q₀ p r = 0 := by
    rw [hpEq, clusterPolar_embed Q₀ φ μ heig]
    have hinner : inner ℝ (clusterEmbed φ (clusterCoeff φ v)) r = 0 := by
      rw [clusterEmbed_inner φ hφ]
      apply Finset.sum_eq_zero
      intro i hi
      rw [clusterResidual_orthogonal φ hφ]
      simp
    rw [hinner]
    ring
  have hrQ : (μ + g) * ‖r‖ ^ 2 ≤ Q₀ r :=
    hgap r (fun i => by
      simpa [r] using clusterResidual_orthogonal φ hφ v i)
  have hsumQ : Q₀ (p + r) = Q₀ p + Q₀ r := by
    rw [QuadraticMap.map_add Q₀ p r, hpolar]
    ring
  calc
    μ * ‖p‖ ^ 2 + (μ + g) * ‖r‖ ^ 2 ≤ Q₀ p + Q₀ r :=
      add_le_add hpQ.symm.le hrQ
    _ = Q₀ (p + r) := hsumQ.symm
    _ = Q₀ v := by rw [hsum]

private theorem clusterQ0_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q₀ : QuadraticMap ℝ V ℝ) (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (μ g : ℝ) (hg : 0 < g)
    (heig : ∀ (i : ι) (v : V),
      QuadraticMap.polar Q₀ (φ i) v = 2 * μ * inner ℝ (φ i) v)
    (hgap : ∀ v : V, (∀ i, inner ℝ (φ i) v = 0) →
      (μ + g) * ‖v‖ ^ 2 ≤ Q₀ v)
    (v : V) :
    μ * ‖v‖ ^ 2 ≤ Q₀ v := by
  have hq := clusterQ0_projection_lower Q₀ φ hφ μ g hg heig hgap v
  have hn := clusterNorm_decomp φ hφ v
  have heq : μ * ‖v‖ ^ 2 =
      μ * ‖clusterProjection φ v‖ ^ 2 +
        μ * ‖clusterResidual φ v‖ ^ 2 := by
    rw [hn]
    ring
  have hres : μ * ‖clusterResidual φ v‖ ^ 2 ≤
      (μ + g) * ‖clusterResidual φ v‖ ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hg) (sq_nonneg (‖clusterResidual φ v‖))]
  calc
    μ * ‖v‖ ^ 2 =
        μ * ‖clusterProjection φ v‖ ^ 2 +
          μ * ‖clusterResidual φ v‖ ^ 2 := heq
    _ ≤ μ * ‖clusterProjection φ v‖ ^ 2 +
          (μ + g) * ‖clusterResidual φ v‖ ^ 2 :=
      add_le_add le_rfl hres
    _ ≤ Q₀ v := hq

private theorem clusterGlobal_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q₀ Q : QuadraticMap ℝ V ℝ) (w : LinearMap.BilinForm ℝ V)
    (b μ g : ℝ) (hb0 : 0 ≤ b) (hg : 0 < g)
    (hwb : ∀ x y : V, |w x y| ≤ b * ‖x‖ * ‖y‖)
    (hQ : ∀ v : V, Q v = Q₀ v + w v v)
    (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (heig : ∀ (i : ι) (v : V),
      QuadraticMap.polar Q₀ (φ i) v = 2 * μ * inner ℝ (φ i) v)
    (hgap : ∀ v : V, (∀ i, inner ℝ (φ i) v = 0) →
      (μ + g) * ‖v‖ ^ 2 ≤ Q₀ v) :
    ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v := by
  refine ⟨μ - b, ?_⟩
  intro v
  have hq0 := clusterQ0_lower Q₀ φ hφ μ g hg heig hgap v
  have hw : -(b * ‖v‖ ^ 2) ≤ w v v := by
    have hh := (abs_le.mp (hwb v v)).1
    simpa [pow_two, mul_assoc] using hh
  rw [hQ v]
  nlinarith [hq0, hw]

private lemma clusterYoung (b g x y : ℝ) (hb0 : 0 ≤ b) (hg : 0 < g) :
    2 * b * x * y ≤ 2 * b ^ 2 / g * x ^ 2 + g / 2 * y ^ 2 := by
  have hsquare : 0 ≤ (2 * b * x - g * y) ^ 2 := sq_nonneg _
  have hmul := mul_nonneg (le_of_lt hg) hsquare
  field_simp [ne_of_gt hg]
  nlinarith [hmul]

private theorem clusterW_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : LinearMap.BilinForm ℝ V) (φ : ι → V) (hφ : Orthonormal ℝ φ)
    (hwsymm : ∀ x y : V, w x y = w y x)
    (T : Matrix ι ι ℝ) (hTw : ∀ i j, T i j = w (φ i) (φ j))
    (z : EuclideanSpace ℝ ι) :
    w (clusterEmbed φ z) (clusterEmbed φ z) =
      inner ℝ (Matrix.toEuclideanLin T z) z := by
  classical
  simp [clusterEmbed, Matrix.toEuclideanLin_apply, PiLp.inner_apply,
    Matrix.mulVec, dotProduct, hTw, hwsymm, mul_comm, mul_left_comm, mul_assoc]

/-- Paper Lemma 4.2, equations `eq:cluster-bound` and `eq:cluster-separation`.
The eigenvalues of `T` are listed increasingly as
`hT.eigenvalues₀ (Fin.rev k)`. -/
theorem cluster_levels
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q₀ Q : QuadraticMap ℝ V ℝ) (w : LinearMap.BilinForm ℝ V)
    (hwsymm : ∀ x y : V, w x y = w y x)
    (b : ℝ) (hwb : ∀ x y : V, |w x y| ≤ b * ‖x‖ * ‖y‖)
    (hQ : ∀ v : V, Q v = Q₀ v + w v v)
    (φ : ι → V) (hφ : Orthonormal ℝ φ) (μ g : ℝ)
    (hg : 0 < g) (hb0 : 0 ≤ b) (hb : b ≤ g / 4)
    (heig : ∀ (i : ι) (v : V),
      QuadraticMap.polar Q₀ (φ i) v = 2 * μ * inner ℝ (φ i) v)
    (hgap : ∀ v : V, (∀ i, inner ℝ (φ i) v = 0) → (μ + g) * ‖v‖ ^ 2 ≤ Q₀ v)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = Fintype.card ι + 1)
    (T : Matrix ι ι ℝ) (hTw : ∀ i j, T i j = w (φ i) (φ j)) (hT : T.IsHermitian) :
    (∀ k : Fin (Fintype.card ι),
      -(2 * b ^ 2 / g) ≤ level Q k - (μ + hT.eigenvalues₀ (Fin.rev k)) ∧
        level Q k - (μ + hT.eigenvalues₀ (Fin.rev k)) ≤ 0) ∧
      (∀ k : Fin (Fintype.card ι), |hT.eigenvalues₀ k| ≤ b) ∧
      μ + g - b ≤ level Q (Fintype.card ι) := by
  classical
  let n := Fintype.card ι
  let E := EuclideanSpace ℝ ι
  let A : E →ₗ[ℝ] E := Matrix.toEuclideanLin T
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hT
  have hn : Module.finrank ℝ E = n := by simp [n, E]
  let B : OrthonormalBasis (Fin n) ℝ E := hA.eigenvectorBasis hn
  have hEval : ∀ i : Fin n, hA.eigenvalues hn i = hT.eigenvalues₀ i := by
    intro i
    rfl
  have hEigenray : ∀ i : Fin n,
      inner ℝ (A (B i)) (B i) = hT.eigenvalues₀ i := by
    intro i
    change inner ℝ (A (hA.eigenvectorBasis hn i))
      (hA.eigenvectorBasis hn i) = hT.eigenvalues₀ i
    rw [hA.apply_eigenvectorBasis hn i, inner_smul_left,
      real_inner_self_eq_norm_sq]
    simp [hEval i, (hA.eigenvectorBasis hn).norm_eq_one]
  have hRevCard : ∀ k : Fin n, n - (Fin.rev k).val = k.val + 1 := by
    intro k
    have hkrev : (Fin.rev k).val = n - (k.val + 1) := rfl
    rw [hkrev]
    omega
  have hEigAbs : ∀ k : Fin n, |hT.eigenvalues₀ k| ≤ b := by
    intro k
    have hw := hwb (clusterEmbed φ (B k)) (clusterEmbed φ (B k))
    rw [clusterW_matrix w φ hφ hwsymm T hTw (B k),
      hEigenray k] at hw
    have hnormsq : ‖clusterEmbed φ (B k)‖ ^ 2 = 1 := by
      rw [clusterEmbed_norm_sq φ hφ, B.norm_eq_one]
      norm_num
    have hnorm : ‖clusterEmbed φ (B k)‖ = 1 := by
      nlinarith [norm_nonneg (clusterEmbed φ (B k))]
    rw [hnorm] at hw
    simpa using hw
  have hglobal := clusterGlobal_lower Q₀ Q w b μ g hb0 hg hwb hQ φ hφ heig hgap
  have hdimN : ∃ W : Submodule ℝ V, Module.finrank ℝ W = n + 1 := by
    simpa [n] using hdim
  have hupper : ∀ k : Fin n, level Q k.val ≤ μ + hT.eigenvalues₀ (Fin.rev k) := by
    intro k
    let idx : Fin n := Fin.rev k
    let eta : ℝ := hT.eigenvalues₀ idx
    have hEtaU : ∀ i : Fin n, i ∈ (Finset.Ici idx : Set (Fin n)) →
        hA.eigenvalues hn i ≤ eta := by
      intro i hi
      have hanti := hT.eigenvalues₀_antitone (show idx ≤ i from Finset.mem_Ici.mp hi)
      change hA.eigenvalues hn i ≤ hT.eigenvalues₀ idx
      rw [hEval i]
      exact hanti
    let S : Submodule ℝ E :=
      Submodule.span ℝ ((B.toBasis) '' (Finset.Ici idx : Set (Fin n)))
    let f : S →ₗ[ℝ] V := (clusterEmbed φ).comp S.subtype
    let W : Submodule ℝ V := LinearMap.range f
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact clusterEmbed_injective φ hφ hxy
    have hWdim : Module.finrank ℝ W = k.val + 1 := by
      calc
        Module.finrank ℝ W = Module.finrank ℝ S :=
          LinearMap.finrank_range_of_inj hf
        _ = n - idx.val := finrank_eigenvectorSpan_Ici A hA hn idx
        _ = k.val + 1 := hRevCard k
    have hWbound : ∀ u ∈ W, Q u ≤ (μ + eta) * ‖u‖ ^ 2 := by
      intro u hu
      rcases (LinearMap.mem_range).mp hu with ⟨z, hzu⟩
      have hz : (z : E) ∈ S := z.property
      change clusterEmbed φ (z : E) = u at hzu
      rw [← hzu]
      have hRay := rayleigh_le_on_eigenvectorSpan A hA hn eta
        (Finset.Ici idx : Set (Fin n)) hEtaU (z : E) hz
      calc
        Q (clusterEmbed φ (z : E)) =
            Q₀ (clusterEmbed φ (z : E)) +
              w (clusterEmbed φ (z : E)) (clusterEmbed φ (z : E)) := hQ _
        _ = μ * ‖(z : E)‖ ^ 2 + inner ℝ (A (z : E)) (z : E) := by
          rw [clusterQ0_embed Q₀ φ μ heig, clusterEmbed_norm_sq φ hφ,
            clusterW_matrix w φ hφ hwsymm T hTw (z : E)]
        _ ≤ (μ + eta) * ‖(z : E)‖ ^ 2 := by nlinarith [hRay]
        _ = (μ + eta) * ‖clusterEmbed φ (z : E)‖ ^ 2 := by
          rw [clusterEmbed_norm_sq φ hφ]
    have hlev := level_le Q k.val hglobal W hWdim (μ + eta) hWbound
    simpa [idx, eta] using hlev
  refine ⟨?_, hEigAbs, ?_⟩
  · intro k
    let idx : Fin n := Fin.rev k
    let eta : ℝ := hT.eigenvalues₀ idx
    have hhi := hupper k
    have hEtaAbs := hEigAbs idx
    have hEtaLo : -b ≤ eta := (abs_le.mp hEtaAbs).1
    have hEtaHi : eta ≤ b := (abs_le.mp hEtaAbs).2
    let e : Fin k.val → V :=
      fun i => clusterEmbed φ (B ((Fin.castLE (Nat.le_of_lt k.isLt) i).rev))
    have hEtaL : ∀ i : Fin n, i ∈ (Finset.Iic idx : Set (Fin n)) →
        eta ≤ hA.eigenvalues hn i := by
      intro i hi
      have hanti := hT.eigenvalues₀_antitone (Finset.mem_Iic.mp hi)
      change hT.eigenvalues₀ idx ≤ hA.eigenvalues hn i
      rw [hEval i]
      exact hanti
    have hdimk : ∃ W : Submodule ℝ V, Module.finrank ℝ W = k.val + 1 := by
      exact exists_finrank_of_le (by omega) hdimN
    have hlowRay : ∀ v : V, (∀ i, inner ℝ (e i) v = 0) →
        (μ + eta - 2 * b ^ 2 / g) * ‖v‖ ^ 2 ≤ Q v := by
      intro v hv
      let z : EuclideanSpace ℝ ι := clusterCoeff φ v
      let p : V := clusterProjection φ v
      let r : V := clusterResidual φ v
      have hpEq : p = clusterEmbed φ z := rfl
      have hprsum : p + r = v := by simp [p, r, clusterResidual]
      have hq0 := clusterQ0_projection_lower Q₀ φ hφ μ g hg heig hgap v
      have hnorm := clusterNorm_decomp φ hφ v
      have hzcoeff : ∀ i : Fin n,
          Module.Basis.repr B.toBasis z i = inner ℝ (B i) z := by
        intro i
        simpa [OrthonormalBasis.coe_toBasis_repr_apply] using
          OrthonormalBasis.repr_apply_apply B z i
      have hcoeffzero : ∀ j : Fin n, idx < j →
          inner ℝ (B j) z = 0 := by
        intro j hj
        have hjrev : Fin.rev j < k := by
          rw [← Fin.rev_lt_iff]
          simpa [idx] using hj
        let i : Fin k.val := ⟨(Fin.rev j).val, by omega⟩
        have hcast : Fin.castLE (Nat.le_of_lt k.isLt) i = Fin.rev j := by
          apply Fin.ext
          rfl
        have hi : (Fin.castLE (Nat.le_of_lt k.isLt) i).rev = j := by
          rw [hcast, Fin.rev_rev]
        have hzero := hv i
        have hrzero :
            inner ℝ (clusterEmbed φ (B j)) r = 0 := by
          change inner ℝ (clusterEmbed φ (B j)) (clusterResidual φ v) = 0
          rw [clusterEmbed_inner φ hφ]
          apply Finset.sum_eq_zero
          intro a ha
          rw [clusterResidual_orthogonal φ hφ]
          simp
        have hpinner :
            inner ℝ (clusterEmbed φ (B j)) p =
              inner ℝ (B j) z := by
          rw [hpEq]
          exact clusterEmbed_pairing φ hφ (B j) z
        have hsuminner :
            inner ℝ (clusterEmbed φ (B j)) v =
              inner ℝ (clusterEmbed φ (B j)) p +
                inner ℝ (clusterEmbed φ (B j)) r := by
          rw [← hprsum, inner_add_right]
        have hzero' : inner ℝ (clusterEmbed φ (B j)) v = 0 := by
          simpa [e, hi] using hzero
        rw [hsuminner, hpinner, hrzero] at hzero'
        simpa using hzero'
      have hzspan : z ∈
          Submodule.span ℝ (B.toBasis '' (Finset.Iic idx : Set (Fin n))) := by
        rw [B.toBasis.mem_span_image]
        intro j hj
        by_contra hnot
        have hjgt : idx < j := by
          have hnot' : ¬ j ≤ idx := by simpa [Finset.mem_Iic] using hnot
          exact lt_of_not_ge hnot'
        have hcz := hcoeffzero j hjgt
        have hrepr := hzcoeff j
        have hsupp : Module.Basis.repr B.toBasis z j ≠ 0 :=
          Finsupp.mem_support_iff.mp hj
        rw [hzcoeff j] at hsupp
        exact hsupp hcz
      have hRay := rayleigh_ge_on_eigenvectorSpan A hA hn eta
        (Finset.Iic idx : Set (Fin n)) hEtaL z hzspan
      have hpRay : eta * ‖p‖ ^ 2 ≤ w p p := by
        calc
          eta * ‖p‖ ^ 2 = eta * ‖z‖ ^ 2 := by rw [hpEq, clusterEmbed_norm_sq φ hφ]
          _ ≤ inner ℝ (A z) z := hRay
          _ = w p p := by rw [hpEq]; exact (clusterW_matrix w φ hφ hwsymm T hTw z).symm
      have hcross : -b * ‖p‖ * ‖r‖ ≤ w p r := by
        have hh := (abs_le.mp (hwb p r)).1
        simpa [mul_assoc] using hh
      have hrr : -b * ‖r‖ ^ 2 ≤ w r r := by
        have hh := (abs_le.mp (hwb r r)).1
        simpa [pow_two, mul_assoc] using hh
      have hwexpand : w v v = w p p + w p r + w r p + w r r := by
        rw [← hprsum]
        simp only [map_add, LinearMap.add_apply]
        abel
      have hsym : w r p = w p r := hwsymm r p
      have hYoung := clusterYoung b g ‖p‖ ‖r‖ hb0 hg
      have hcomp : eta - 2 * b ^ 2 / g ≤ g / 2 - b := by
        have hfrac : 0 ≤ 2 * b ^ 2 / g :=
          div_nonneg (mul_nonneg (by norm_num) (sq_nonneg b)) (le_of_lt hg)
        have hbg : 2 * b ≤ g / 2 := by linarith [hb]
        linarith
      have hmix :
          (μ + eta - 2 * b ^ 2 / g) * ‖p‖ ^ 2 +
            (μ + g / 2 - b) * ‖r‖ ^ 2 ≤ Q v := by
        rw [hQ v, hwexpand]
        nlinarith [hq0, hpRay, hcross, hrr, hsym, hYoung]
      have hnormcoef :
          (μ + eta - 2 * b ^ 2 / g) * ‖v‖ ^ 2 ≤
            (μ + eta - 2 * b ^ 2 / g) * ‖p‖ ^ 2 +
              (μ + g / 2 - b) * ‖r‖ ^ 2 := by
        rw [hnorm]
        have hcoef :
            0 ≤ (μ + g / 2 - b) - (μ + eta - 2 * b ^ 2 / g) :=
          sub_nonneg.mpr (by linarith [hcomp])
        nlinarith [mul_nonneg hcoef (sq_nonneg (‖r‖))]
      exact hnormcoef.trans hmix
    have hlo := le_level Q k.val e
      (μ + eta - 2 * b ^ 2 / g) hlowRay hdimk
    have hlo' : μ + hT.eigenvalues₀ (Fin.rev k) - 2 * b ^ 2 / g ≤ level Q k := by
      simpa [eta, idx] using hlo
    have hhi' : level Q k ≤ μ + hT.eigenvalues₀ (Fin.rev k) := by
      simpa [idx] using hhi
    constructor
    · linarith
    · linarith
  · have hsepRay : ∀ v : V,
        (∀ i : Fin n, inner ℝ (φ ((Fintype.equivFin ι).symm i)) v = 0) →
          (μ + g - b) * ‖v‖ ^ 2 ≤ Q v := by
      intro v hv
      have horth : ∀ i : ι, inner ℝ (φ i) v = 0 := by
        intro i
        have hi := hv ((Fintype.equivFin ι) i)
        simpa using hi
      have hq0 := hgap v horth
      have hw : -(b * ‖v‖ ^ 2) ≤ w v v := by
        have hh := (abs_le.mp (hwb v v)).1
        simpa [pow_two, mul_assoc] using hh
      rw [hQ v]
      nlinarith [hq0, hw]
    have hsep := le_level Q n
      (fun i : Fin n => φ ((Fintype.equivFin ι).symm i))
      (μ + g - b) hsepRay hdimN
    simpa [n] using hsep

end MinMax
end Tunneling
===END FILE===
