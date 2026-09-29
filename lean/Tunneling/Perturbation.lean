import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Ground-state perturbation estimate

This is the exact Hilbert-space estimate in Lemma 3.1 of the paper.  The
quadratic energy is represented by a real-valued function `q`; its only role in
the proof is the spectral-gap lower bound along the orthogonal complement of
the normalized ground state.
-/

namespace Tunneling

open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace GroundStatePerturbation

/-- The orthogonal residual of `ψ` relative to the normalized ground state `φ`. -/
noncomputable def residual (φ ψ : H) : H := ψ - inner ℝ φ ψ • φ

theorem inner_residual (φ ψ : H) :
    inner ℝ φ (residual φ ψ) = inner ℝ φ ψ - inner ℝ φ ψ * ‖φ‖ ^ 2 := by
  simp [residual, inner_sub_right, inner_smul_right]

theorem residual_orthogonal {φ ψ : H} (hφ : ‖φ‖ = 1) :
    inner ℝ φ (residual φ ψ) = 0 := by
  rw [inner_residual, hφ]
  ring

theorem decomposition (φ ψ : H) :
  ψ = inner ℝ φ ψ • φ + residual φ ψ := by
  simp [residual]

/-- The Rayleigh integrand of a branch `q + W`. -/
abbrev branchRayleigh (q : H → ℝ) (W : H →L[ℝ] H) (x : H) : ℝ :=
  q x + inner ℝ (W x) x

/-- The block quadratic energy of the two-well matrix
`[[A, B], [B, A]]` before the parity change of variables. -/
abbrev twoWellBlockEnergy (q : H → ℝ) (W : H →L[ℝ] H) (x y : H) : ℝ :=
  q x + q y + 2 * inner ℝ (W x) y

/-- Rayleigh integrands scale quadratically along scalar multiples. -/
theorem branchRayleigh_smul
    (q : H → ℝ) (W : H →L[ℝ] H)
    (hqsmul : ∀ (t : ℝ) (x : H), q (t • x) = t ^ 2 * q x)
    (t : ℝ) (x : H) :
    branchRayleigh q W (t • x) = t ^ 2 * branchRayleigh q W x := by
  simp only [branchRayleigh, hqsmul, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- The exact block-parity identity from Lemma 2.1.  With
`p = x + y` and `r = x - y`, the block energy is the average of the
symmetric branch energy at `p` and the antisymmetric branch energy at `r`. -/
theorem twoWellBlockEnergy_parity
    (q : H → ℝ) (W : H →L[ℝ] H)
    (hq : ∀ x y : H, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hW : ∀ x y : H, inner ℝ (W x) y = inner ℝ x (W y))
    (x y : H) :
    twoWellBlockEnergy q W x y =
      (branchRayleigh q W (x + y) +
        branchRayleigh q (-W) (x - y)) / 2 := by
  have hWcross :
      inner ℝ (W (x + y)) (x + y) - inner ℝ (W (x - y)) (x - y) =
        4 * inner ℝ (W x) y := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right]
    rw [hW y x]
    simp only [real_inner_comm]
    ring
  have hqsum : q (x + y) + q (x - y) = 2 * q x + 2 * q y := hq x y
  simp only [twoWellBlockEnergy, branchRayleigh,
    neg_apply, inner_neg_left]
  linarith [hqsum, hWcross]

/-- The normalized symmetric/antisymmetric change of variables from Lemma 2.1. -/
theorem twoWellBlockEnergy_parity_normalized
    (q : H → ℝ) (W : H →L[ℝ] H)
    (hqsmul : ∀ (t : ℝ) (x : H), q (t • x) = t ^ 2 * q x)
    (hq : ∀ x y : H, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hW : ∀ x y : H, inner ℝ (W x) y = inner ℝ x (W y))
    (x y : H) :
    twoWellBlockEnergy q W x y =
      branchRayleigh q W ((Real.sqrt 2)⁻¹ • (x + y)) +
        branchRayleigh q (-W) ((Real.sqrt 2)⁻¹ • (x - y)) := by
  rw [twoWellBlockEnergy_parity q W hq hW x y,
    branchRayleigh_smul q W hqsmul (Real.sqrt 2)⁻¹ (x + y),
    branchRayleigh_smul q (-W) hqsmul (Real.sqrt 2)⁻¹ (x - y)]
  have hsqrt : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 2⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsqrt]
  ring

/-- The unit sphere of directions orthogonal to a fixed ground state. -/
def orthogonalUnitSphere (φ : H) : Set H :=
  {ψ | ‖ψ‖ = 1 ∧ inner ℝ φ ψ = 0}

/-- The second Rayleigh energy as the infimum on the orthogonal unit sphere. -/
noncomputable def orthogonalRayleighInf (q : H → ℝ) (φ : H) : ℝ :=
  sInf (q '' orthogonalUnitSphere φ)

/-- The orthogonal spectral-gap inequality follows from the variational
definition of the second Rayleigh energy. -/
theorem quadratic_gap_of_orthogonalRayleighInf
    (φ : H) (q : H → ℝ) (mu mu2 gap : ℝ)
    (hqsmul : ∀ (t : ℝ) (x : H), q (t • x) = t ^ 2 * q x)
    (hqnonneg : ∀ x : H, 0 ≤ q x)
    (hinf : orthogonalRayleighInf q φ = mu2)
    (hgap : gap = mu2 - mu) :
    ∀ η : H, inner ℝ φ η = 0 →
      (mu + gap) * ‖η‖ ^ 2 ≤ q η := by
  have hbdd : BddBelow (q '' orthogonalUnitSphere φ) := by
    refine ⟨0, fun y hy => ?_⟩
    obtain ⟨ψ, hψ, rfl⟩ := hy
    exact hqnonneg ψ
  intro η hη
  by_cases hη0 : η = 0
  · subst hη0
    have hq0 : q 0 = 0 := by
      have h := hqsmul 0 (0 : H)
      simpa using h
    rw [hq0]
    simp
  · set r : ℝ := ‖η‖ with hrdef
    have hrpos : 0 < r := by
      rw [hrdef]
      exact norm_pos_iff.mpr hη0
    set ψ : H := r⁻¹ • η with hψdef
    have hψnorm : ‖ψ‖ = 1 := by
      rw [hψdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos),
        inv_mul_cancel₀ hrpos.ne']
    have hψorth : inner ℝ φ ψ = 0 := by
      rw [hψdef, real_inner_smul_right, hη, mul_zero]
    have hmem : ψ ∈ orthogonalUnitSphere φ := ⟨hψnorm, hψorth⟩
    have hqmem : q ψ ∈ q '' orthogonalUnitSphere φ :=
      Set.mem_image_of_mem q hmem
    have hinfle : mu2 ≤ q ψ := by
      have h := csInf_le hbdd hqmem
      rw [← hinf]
      change sInf (q '' orthogonalUnitSphere φ) ≤ q ψ
      exact h
    have hηeq : η = r • ψ := by
      rw [hψdef, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
    have hqη : q η = r ^ 2 * q ψ := by
      rw [hηeq, hqsmul]
    have hgapEq : mu + gap = mu2 := by
      linarith [hgap]
    have hmul : r ^ 2 * (mu + gap) ≤ r ^ 2 * q ψ :=
      mul_le_mul_of_nonneg_left (by rw [hgapEq]; exact hinfle) (sq_nonneg r)
    nlinarith [hqη, hmul]

theorem residual_norm_sq (φ ψ : H) (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    ‖residual φ ψ‖ ^ 2 = 1 - inner ℝ φ ψ ^ 2 := by
  set a : ℝ := inner ℝ φ ψ
  set η : H := residual φ ψ
  have hη : inner ℝ φ η = 0 := residual_orthogonal (φ := φ) (ψ := ψ) hφ
  have hdecomp : ψ = a • φ + η := by
    simpa [a, η] using decomposition φ ψ
  have hsum : ‖a • φ + η‖ ^ 2 = ‖a • φ‖ ^ 2 + ‖η‖ ^ 2 := by
    rw [pow_two, pow_two, pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • φ) η
      (by rw [real_inner_smul_left, hη, mul_zero])
  have hpyth : ‖ψ‖ ^ 2 = ‖a • φ‖ ^ 2 + ‖η‖ ^ 2 := by
    rw [hdecomp, hsum]
  rw [hψ] at hpyth
  simp only [norm_smul, Real.norm_eq_abs, hφ, one_pow] at hpyth
  simp only [mul_one] at hpyth
  rw [sq_abs] at hpyth
  nlinarith

/-- Polarization of the Rayleigh quadratic map of a linear operator. -/
theorem quadratic_polar_of_operator
    (T : H →L[ℝ] H) (q : H → ℝ) (x y : H)
    (hq : ∀ z : H, q z = inner ℝ (T z) z) :
    QuadraticMap.polar q x y =
      inner ℝ (T x) y + inner ℝ (T y) x := by
  rw [QuadraticMap.polar, hq (x + y), hq x, hq y]
  simp only [map_add, inner_add_left, inner_add_right]
  ring

/-- The polar form of a symmetric Rayleigh operator vanishes between an
eigenline and every orthogonal direction. -/
theorem quadratic_polar_zero_of_eigenline
    (T : H →L[ℝ] H) (q : H → ℝ) (φ : H) (mu : ℝ)
    (hq : ∀ z : H, q z = inner ℝ (T z) z)
    (hT : ∀ x y : H, inner ℝ (T x) y = inner ℝ x (T y))
    (hφ : T φ = mu • φ) (t : ℝ) (r : H)
    (hr : inner ℝ φ r = 0) :
    QuadraticMap.polar q (t • φ) r = 0 := by
  have h : inner ℝ (t • φ) (T r) = 0 := by
    rw [inner_smul_left, ← hT φ r, hφ, inner_smul_left, hr]
    ring
  have h2 : inner ℝ (T r) (t • φ) = 0 := by
    rw [real_inner_comm]
    exact h
  rw [quadratic_polar_of_operator T q (t • φ) r hq,
    hT (t • φ) r, h, h2]
  ring

/-- A normalized global minimizer of a quadratic energy has vanishing polar
form against every orthogonal direction. -/
theorem quadratic_polar_zero_of_min_unit_sphere
    (φ : H) (Q : QuadraticMap ℝ H ℝ) (r : H)
    (hφ : ‖φ‖ = 1)
    (hr : inner ℝ φ r = 0)
    (hmin : ∀ ψ : H, ‖ψ‖ = 1 → Q φ ≤ Q ψ) :
    QuadraticMap.polar (⇑Q) φ r = 0 := by
  set p : ℝ := QuadraticMap.polar (⇑Q) φ r
  set c : ℝ := Q r - Q φ * ‖r‖ ^ 2
  have hqshift : ∀ t : ℝ, Q (φ + t • r) = Q φ + t * p + t ^ 2 * Q r := by
    intro t
    have hadd : Q (φ + t • r) =
        Q φ + Q (t • r) + QuadraticMap.polar (⇑Q) φ (t • r) :=
      QuadraticMap.map_add (⇑Q) φ (t • r)
    have hsmulq : Q (t • r) = t ^ 2 * Q r := by
      rw [Q.map_smul, smul_eq_mul, pow_two]
    have hpolar : QuadraticMap.polar (⇑Q) φ (t • r) =
        t * QuadraticMap.polar (⇑Q) φ r := by
      rw [QuadraticMap.polar_smul_right Q t φ r, smul_eq_mul]
    rw [hadd, hsmulq, hpolar]
    simp only [p]
    ring
  have hnormshift : ∀ t : ℝ, ‖φ + t • r‖ ^ 2 = 1 + t ^ 2 * ‖r‖ ^ 2 := by
    intro t
    have hinner : inner ℝ φ (t • r) = 0 := by
      rw [real_inner_smul_right, hr, mul_zero]
    have hpy : ‖φ + t • r‖ ^ 2 = ‖φ‖ ^ 2 + ‖t • r‖ ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero φ (t • r) hinner
    rw [hpy, hφ, one_pow]
    have hsm : ‖t • r‖ ^ 2 = t ^ 2 * ‖r‖ ^ 2 := by
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hsm]
  have hkey : ∀ t : ℝ, 0 ≤ t * p + t ^ 2 * c := by
    intro t
    set x : H := φ + t • r
    have hx2 : ‖x‖ ^ 2 = 1 + t ^ 2 * ‖r‖ ^ 2 := hnormshift t
    have hx2pos : 0 < ‖x‖ ^ 2 := by
      rw [hx2]
      positivity
    have hxpos : 0 < ‖x‖ := by
      have hne : ‖x‖ ≠ 0 := by
        intro h
        rw [h] at hx2pos
        simp at hx2pos
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hunit : ‖(‖x‖⁻¹ • x)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos),
        inv_mul_cancel₀ hxpos.ne']
    have hminx := hmin _ hunit
    have hscale : Q ((‖x‖⁻¹) • x) = (‖x‖⁻¹) ^ 2 * Q x := by
      rw [Q.map_smul, smul_eq_mul, pow_two]
    rw [hscale] at hminx
    have hrew : (‖x‖⁻¹ : ℝ) ^ 2 * Q x = Q x / ‖x‖ ^ 2 := by
      field_simp [hxpos.ne']
      try ring
    rw [hrew] at hminx
    have hmul : ‖x‖ ^ 2 * Q φ ≤ Q x := by
      have hdiv := (le_div_iff₀ hx2pos).mp hminx
      simpa [mul_comm] using hdiv
    have hqx : Q x = Q φ + t * p + t ^ 2 * Q r := by
      simpa [x] using hqshift t
    rw [hx2, hqx] at hmul
    simp only [c] at hmul ⊢
    nlinarith
  by_contra hp
  have hp2 : 0 < p ^ 2 := sq_pos_of_ne_zero hp
  set d : ℝ := 1 + |c|
  have hd : 0 < d := by positivity
  set t : ℝ := -p / (2 * d)
  have ht := hkey t
  have hcb : c ≤ |c| := le_abs_self c
  have hdb : |c| ≤ d := by
    simp only [d]
    linarith
  have h1 : t * p = -p ^ 2 / (2 * d) := by
    simp only [t, pow_two]
    field_simp [hd.ne']
    try ring
  have h2 : t ^ 2 * c = (p ^ 2 / (4 * d)) * (c / d) := by
    simp only [t, pow_two]
    field_simp [hd.ne']
    try ring
  have h3 : c / d ≤ 1 := by
    rw [div_le_one hd]
    exact le_trans (le_abs_self c) hdb
  have h4 : 0 ≤ p ^ 2 / (4 * d) := by positivity
  have h5 : (p ^ 2 / (4 * d)) * (c / d) ≤ p ^ 2 / (4 * d) := by
    have := mul_le_mul_of_nonneg_left h3 h4
    simpa using this
  have h6 : t * p + t ^ 2 * c < 0 := by
    rw [h1, h2]
    calc
      -p ^ 2 / (2 * d) + (p ^ 2 / (4 * d)) * (c / d) ≤
          -p ^ 2 / (2 * d) + p ^ 2 / (4 * d) := by linarith
      _ = -p ^ 2 / (4 * d) := by
        field_simp [hd.ne']
        try ring
      _ < 0 := by
        exact div_neg_of_neg_of_pos (neg_neg_of_pos hp2) (by positivity)
  exact absurd ht (not_le_of_gt h6)

/-- The normalized gap inequality for a quadratic energy with a ground-line
polarization identity and a lower bound on the orthogonal complement. -/
theorem eigenvector_of_min_unit_sphere
    (T : H →L[ℝ] H) (Q : QuadraticMap ℝ H ℝ) (φ : H) (mu : ℝ)
    (hq : ∀ z : H, Q z = inner ℝ (T z) z)
    (hT : ∀ x y : H, inner ℝ (T x) y = inner ℝ x (T y))
    (hφ : ‖φ‖ = 1)
    (henergy : Q φ = mu)
    (hmin : ∀ ψ : H, ‖ψ‖ = 1 → Q φ ≤ Q ψ) :
    T φ = mu • φ := by
  have hpolar : ∀ r : H, inner ℝ φ r = 0 →
      QuadraticMap.polar (⇑Q) φ r = 0 := by
    intro r hr
    exact quadratic_polar_zero_of_min_unit_sphere φ Q r hφ hr hmin
  have horth : ∀ r : H, inner ℝ φ r = 0 →
      inner ℝ (T φ) r = 0 := by
    intro r hr
    have hp := hpolar r hr
    rw [quadratic_polar_of_operator T (⇑Q) φ r hq] at hp
    have hs : inner ℝ (T r) φ = inner ℝ (T φ) r := by
      rw [hT r φ, real_inner_comm]
    rw [hs] at hp
    linarith
  have hmain : ∀ x : H, inner ℝ (T φ - mu • φ) x = 0 := by
    intro x
    set a : ℝ := inner ℝ φ x
    set rr : H := residual φ x
    have hdecomp : x = a • φ + rr := by
      simpa [a, rr] using decomposition φ x
    have hrr : inner ℝ φ rr = 0 := by
      simpa [rr] using residual_orthogonal (φ := φ) (ψ := x) hφ
    have hφinner : inner ℝ (T φ - mu • φ) φ = 0 := by
      rw [inner_sub_left, real_inner_smul_left, ← hq φ, henergy,
        real_inner_self_eq_norm_mul_norm, hφ]
      ring
    have hrrinner : inner ℝ (T φ - mu • φ) rr = 0 := by
      rw [inner_sub_left, real_inner_smul_left, horth rr hrr, hrr]
      ring
    rw [hdecomp, inner_add_right, inner_smul_right, hφinner, hrrinner]
    ring
  have hzero : T φ - mu • φ = 0 :=
    inner_self_eq_zero.mp (hmain (T φ - mu • φ))
  exact sub_eq_zero.mp hzero

theorem quadratic_gap_of_polar
    (φ : H) (Q : QuadraticMap ℝ H ℝ) (mu gap : ℝ)
    (hφ : ‖φ‖ = 1)
    (hqφ : Q φ = mu)
    (hpolar : ∀ (t : ℝ) (r : H), inner ℝ φ r = 0 →
      QuadraticMap.polar (⇑Q) (t • φ) r = 0)
    (horth : ∀ η : H, inner ℝ φ η = 0 →
      (mu + gap) * ‖η‖ ^ 2 ≤ Q η)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    mu + gap * ‖residual φ ψ‖ ^ 2 ≤ Q ψ := by
  set a : ℝ := inner ℝ φ ψ
  set η : H := residual φ ψ
  have hη : inner ℝ φ η = 0 := residual_orthogonal hφ
  have hdecomp : ψ = a • φ + η := by
    simpa [a, η] using decomposition φ ψ
  have hnorm : ‖η‖ ^ 2 = 1 - a ^ 2 := residual_norm_sq φ ψ hφ hψ
  have hpolar' : QuadraticMap.polar (⇑Q) (a • φ) η = 0 := hpolar a η hη
  have hqη := horth η hη
  have hadd : Q ψ = Q (a • φ) + Q η +
      QuadraticMap.polar (⇑Q) (a • φ) η := by
    rw [hdecomp]
    exact QuadraticMap.map_add (⇑Q) (a • φ) η
  have hsmul : Q (a • φ) = a ^ 2 * Q φ := by
    simp only [QuadraticMap.map_smul, smul_eq_mul, pow_two]
  have hq : Q ψ = a ^ 2 * mu + Q η := by
    rw [hadd, hpolar', hsmul, hqφ]
    ring
  have hkey : Q ψ = (1 - ‖η‖ ^ 2) * mu + Q η := by
    rw [hq, hnorm]
    ring
  calc
    mu + gap * ‖η‖ ^ 2 ≤
        (1 - ‖η‖ ^ 2) * mu + Q η := by nlinarith [hqη]
    _ = Q ψ := hkey.symm

/-- The normalized spectral-gap inequality for a symmetric operator.  If
`T φ = mu • φ` and every vector orthogonal to `φ` has energy at least
`(mu + gap)` times its squared norm, then the quadratic form of `T` satisfies
the gap bound along the residual of every normalized vector. -/
theorem spectral_gap_of_operator
    (φ : H) (T : H →L[ℝ] H) (mu gap : ℝ)
    (hφ : ‖φ‖ = 1)
    (hTφ : T φ = mu • φ)
    (hT : ∀ x y : H, inner ℝ (T x) y = inner ℝ x (T y))
    (hgap : ∀ η : H, inner ℝ φ η = 0 →
      (mu + gap) * ‖η‖ ^ 2 ≤ inner ℝ (T η) η)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    mu + gap * ‖residual φ ψ‖ ^ 2 ≤ inner ℝ (T ψ) ψ := by
  set a : ℝ := inner ℝ φ ψ
  set η : H := residual φ ψ
  have hη : inner ℝ φ η = 0 := residual_orthogonal hφ
  have hdecomp : ψ = a • φ + η := by
    simpa [a, η] using decomposition φ ψ
  have hnorm : ‖η‖ ^ 2 = 1 - a ^ 2 := residual_norm_sq φ ψ hφ hψ
  have hTφη : inner ℝ (T φ) η = 0 := by
    rw [hTφ, real_inner_smul_left, hη, mul_zero]
  have hTηφ : inner ℝ (T η) φ = 0 := by
    rw [hT η φ, hTφ, real_inner_smul_right, real_inner_comm, hη, mul_zero]
  have hdiag : inner ℝ (T φ) φ = mu := by
    rw [hTφ, real_inner_smul_left, real_inner_self_eq_norm_mul_norm, hφ]
    ring
  have hexpand : inner ℝ (T ψ) ψ =
      a * a * inner ℝ (T φ) φ + inner ℝ (T η) η := by
    rw [hdecomp]
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hTφη, hTηφ]
    ring
  have hηgap := hgap η hη
  calc
    mu + gap * ‖η‖ ^ 2 ≤
        (1 - ‖η‖ ^ 2) * mu + inner ℝ (T η) η := by
      nlinarith [hηgap]
    _ = inner ℝ (T ψ) ψ := by
      rw [hexpand, hdiag, hnorm]
      ring

theorem abs_inner_le_norm (φ ψ : H) : |inner ℝ φ ψ| ≤ ‖φ‖ * ‖ψ‖ := by
  exact abs_real_inner_le_norm φ ψ

theorem quadratic_remainder (gap b x : ℝ)
    (hgap : 0 < gap) (hb : b ≤ gap / 4) :
    (gap - 2 * b) * x ^ 2 - 2 * b * x + 2 * b ^ 2 / gap ≥ 0 := by
  set d : ℝ := gap - 2 * b
  have hd : 0 < d := by
    have : b ≤ gap / 4 := hb
    nlinarith
  have hcomplete : 0 ≤ d * (x - b / d) ^ 2 :=
    mul_nonneg hd.le (sq_nonneg _)
  have hconst : b ^ 2 / d ≤ 2 * b ^ 2 / gap := by
    rw [div_le_div_iff₀ hd hgap]
    nlinarith [hb, hgap]
  have hstep :
      d * (x - b / d) ^ 2 = d * x ^ 2 - 2 * b * x + b ^ 2 / d := by
    field_simp [hd.ne']
    ring
  nlinarith [hcomplete, hconst, hstep]

/-- The lower Rayleigh estimate in Lemma 3.1.  The energy `q` is assumed to
have bottom value `mu` at `φ` and spectral gap `gap` on `φᗮ`. -/
theorem lower_bound
    (φ : H) (q : H → ℝ) (mu gap : ℝ)
    (W : H →L[ℝ] H)
    (hφ : ‖φ‖ = 1)
    (_hqφ : q φ = mu)
    (hgap : 0 < gap)
    (hq : ∀ ψ : H, ‖ψ‖ = 1 →
      mu + gap * ‖residual φ ψ‖ ^ 2 ≤ q ψ)
    (hW : ∀ x y : H, inner ℝ (W x) y = inner ℝ x (W y))
    (hb : ‖W‖ ≤ gap / 4)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    mu + inner ℝ (W φ) φ - 2 * ‖W‖ ^ 2 / gap ≤ q ψ + inner ℝ (W ψ) ψ := by
  set a : ℝ := inner ℝ φ ψ
  set η : H := residual φ ψ
  have hdecomp : ψ = a • φ + η := decomposition φ ψ
  have hη : inner ℝ φ η = 0 := residual_orthogonal hφ
  have hnorm : ‖η‖ ^ 2 = 1 - a ^ 2 := residual_norm_sq φ ψ hφ hψ
  set t2 : ℝ := ‖η‖ ^ 2
  have ht2 : 0 ≤ t2 := sq_nonneg _
  have ha : |a| ≤ 1 := by
    have h := abs_inner_le_norm φ ψ
    rw [hφ, hψ] at h
    simpa using h
  have hcross : |inner ℝ (W φ) η| ≤ ‖W‖ * ‖η‖ := by
    calc
      |inner ℝ (W φ) η| ≤ ‖W φ‖ * ‖η‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖W‖ * ‖φ‖ * ‖η‖ := by
        have h := ContinuousLinearMap.le_opNorm W φ
        have hη : 0 ≤ ‖η‖ := norm_nonneg η
        nlinarith [hφ]
      _ = ‖W‖ * ‖η‖ := by rw [hφ]; ring
  have hself : inner ℝ (W φ) η = inner ℝ φ (W η) := by
    exact hW φ η
  have hdiag : |inner ℝ (W η) η| ≤ ‖W‖ * ‖η‖ ^ 2 := by
    calc
      |inner ℝ (W η) η| ≤ ‖W η‖ * ‖η‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖W‖ * ‖η‖ * ‖η‖ := by
        have h := ContinuousLinearMap.le_opNorm W η
        have hη : 0 ≤ ‖η‖ := norm_nonneg η
        nlinarith
      _ = ‖W‖ * ‖η‖ ^ 2 := by ring
  have hexpand :
      inner ℝ (W ψ) ψ - inner ℝ (W φ) φ
        = -t2 * inner ℝ (W φ) φ + 2 * a * inner ℝ (W φ) η
            + inner ℝ (W η) η := by
    have hsum : inner ℝ (W ψ) ψ =
        a * a * inner ℝ (W φ) φ + 2 * a * inner ℝ (W φ) η
          + inner ℝ (W η) η := by
      rw [hdecomp]
      simp only [map_add, map_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hself, real_inner_comm (W η) φ, hW η φ]
      ring_nf
    have hkey : a * a - 1 = -t2 := by
      nlinarith [hnorm]
    rw [hsum]
    calc
      a * a * inner ℝ (W φ) φ + 2 * a * inner ℝ (W φ) η
          + inner ℝ (W η) η - inner ℝ (W φ) φ
          = (a * a - 1) * inner ℝ (W φ) φ + 2 * a * inner ℝ (W φ) η
              + inner ℝ (W η) η := by ring
      _ = -t2 * inner ℝ (W φ) φ + 2 * a * inner ℝ (W φ) η
              + inner ℝ (W η) η := by rw [hkey]
  have hWq : inner ℝ (W ψ) ψ - inner ℝ (W φ) φ ≥
      -2 * ‖W‖ * t2 - 2 * ‖W‖ * ‖η‖ := by
    rw [hexpand]
    have hprod : |a * inner ℝ (W φ) η| ≤ ‖W‖ * ‖η‖ := by
      rw [abs_mul]
      nlinarith [hcross, ha, abs_nonneg a, abs_nonneg (inner ℝ (W φ) η)]
    have hfirst : -t2 * inner ℝ (W φ) φ ≥ -‖W‖ * t2 := by
      have hbound : |inner ℝ (W φ) φ| ≤ ‖W‖ := by
        calc
          |inner ℝ (W φ) φ| ≤ ‖W φ‖ * ‖φ‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖W‖ * ‖φ‖ * ‖φ‖ := by
            have h := ContinuousLinearMap.le_opNorm W φ
            have hφ' : 0 ≤ ‖φ‖ := norm_nonneg φ
            nlinarith
          _ = ‖W‖ := by rw [hφ]; ring
      have hwle : inner ℝ (W φ) φ ≤ ‖W‖ := (abs_le.mp hbound).2
      nlinarith [hwle, ht2]
    have hsecond : -2 * ‖W‖ * ‖η‖ ≤ 2 * a * inner ℝ (W φ) η := by
      nlinarith [neg_le_of_abs_le hprod]
    have hthird : -‖W‖ * t2 ≤ inner ℝ (W η) η := by
      nlinarith [neg_le_of_abs_le hdiag]
    nlinarith [hfirst, hsecond, hthird]
  have hlower :
      q ψ + inner ℝ (W ψ) ψ ≥
        mu + inner ℝ (W φ) φ + gap * t2
          - 2 * ‖W‖ * t2 - 2 * ‖W‖ * ‖η‖ := by
    have hqψ := hq ψ hψ
    nlinarith [_hqφ, hWq]
  have hcomplete := quadratic_remainder gap ‖W‖ ‖η‖ hgap hb
  nlinarith [hlower, hcomplete]

/-- The upper Rayleigh estimate in Lemma 3.1, witnessed by the ground state. -/
theorem upper_bound (φ : H) (q : H → ℝ) (mu : ℝ)
    (W : H →L[ℝ] H) (hqφ : q φ = mu) :
    q φ + inner ℝ (W φ) φ ≤ mu + inner ℝ (W φ) φ := by
  rw [hqφ]

/-- The quadratic-form lower bound inside the proof of Lemma 4.2.  The vector
`psi` is split orthogonally as `p + r`, where `p` lies in the isolated ground
cluster and `r` is orthogonal to it.  The unperturbed form has value `mu` on
the cluster and gap `gap` on its orthogonal complement. -/
theorem cluster_form_lower_bound
    (q : H → ℝ) (W : H →L[ℝ] H) (mu gap b : ℝ)
    (p r psi : H)
    (hgap : 0 < gap) (hb : 0 ≤ b) (hsmall : b ≤ gap / 4)
    (hW : ∀ x y : H, inner ℝ (W x) y = inner ℝ x (W y))
    (hnormW : ‖W‖ ≤ b)
    (hpr : inner ℝ p r = 0)
    (hpsi : psi = p + r)
    (hq : q psi = q p + q r)
    (hqp : q p = mu * ‖p‖ ^ 2)
    (hqr : (mu + gap) * ‖r‖ ^ 2 ≤ q r) :
      mu * ‖psi‖ ^ 2 + inner ℝ (W p) p - 2 * b ^ 2 / gap * ‖p‖ ^ 2 +
        (gap / 2 - b) * ‖r‖ ^ 2 ≤
      q psi + inner ℝ (W psi) psi := by
  have hnorm : ‖psi‖ ^ 2 = ‖p‖ ^ 2 + ‖r‖ ^ 2 := by
    rw [hpsi, pow_two, pow_two, pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p r hpr
  have hcross : 2 * inner ℝ (W p) r ≥ -2 * b * ‖p‖ * ‖r‖ := by
    have h1 : |inner ℝ (W p) r| ≤ b * ‖p‖ * ‖r‖ := by
      calc
        |inner ℝ (W p) r| ≤ ‖W p‖ * ‖r‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖W‖ * ‖p‖ * ‖r‖ := by
          have h := ContinuousLinearMap.le_opNorm W p
          exact mul_le_mul_of_nonneg_right h (norm_nonneg r)
        _ ≤ b * ‖p‖ * ‖r‖ := by
          have hp : 0 ≤ ‖p‖ := norm_nonneg p
          have hr : 0 ≤ ‖r‖ := norm_nonneg r
          have hmul := mul_le_mul_of_nonneg_right hnormW (mul_nonneg hp hr)
          simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
    have h2 : -(b * ‖p‖ * ‖r‖) ≤ inner ℝ (W p) r :=
      neg_le_of_abs_le h1
    nlinarith
  have hcross' : inner ℝ (W p) r + inner ℝ (W r) p ≥
      -2 * b * ‖p‖ * ‖r‖ := by
    have h1 : inner ℝ (W r) p = inner ℝ (W p) r := by
      rw [hW r p, real_inner_comm]
    rw [h1]
    nlinarith [hcross]
  have hself : -(b * ‖r‖ ^ 2) ≤ inner ℝ (W r) r := by
    have h1 : |inner ℝ (W r) r| ≤ b * ‖r‖ ^ 2 := by
      calc
        |inner ℝ (W r) r| ≤ ‖W r‖ * ‖r‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖W‖ * ‖r‖ * ‖r‖ := by
          have h := ContinuousLinearMap.le_opNorm W r
          exact mul_le_mul_of_nonneg_right h (norm_nonneg r)
        _ = ‖W‖ * ‖r‖ ^ 2 := by ring
        _ ≤ b * ‖r‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right hnormW (sq_nonneg ‖r‖)
    exact neg_le_of_abs_le h1
  have hexpand :
      inner ℝ (W psi) psi = inner ℝ (W p) p +
        (inner ℝ (W p) r + inner ℝ (W r) p) + inner ℝ (W r) r := by
    rw [hpsi]
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  have hqle : mu * ‖psi‖ ^ 2 + gap * ‖r‖ ^ 2 ≤ q psi := by
    rw [hq, hqp, hnorm]
    nlinarith [hqr]
  have halgebra :
      gap * ‖r‖ ^ 2 - 2 * b * ‖p‖ * ‖r‖ - b * ‖r‖ ^ 2 ≥
        -2 * b ^ 2 / gap * ‖p‖ ^ 2 + (gap / 2 - b) * ‖r‖ ^ 2 := by
    have hsq : 0 ≤ (gap * ‖r‖ - 2 * b * ‖p‖) ^ 2 / 2 := by positivity
    have hkey :
        gap * ((gap * ‖r‖ ^ 2 - 2 * b * ‖p‖ * ‖r‖ - b * ‖r‖ ^ 2) -
          (-2 * b ^ 2 / gap * ‖p‖ ^ 2 + (gap / 2 - b) * ‖r‖ ^ 2)) =
            (gap * ‖r‖ - 2 * b * ‖p‖) ^ 2 / 2 := by
      field_simp [hgap.ne']
      ring
    have hdiff : 0 ≤ gap *
        (gap * ‖r‖ ^ 2 - 2 * b * ‖p‖ * ‖r‖ - b * ‖r‖ ^ 2 -
          (-2 * b ^ 2 / gap * ‖p‖ ^ 2 + (gap / 2 - b) * ‖r‖ ^ 2)) := by
      rw [hkey]
      exact hsq
    nlinarith [hdiff, hgap]
  have hcrossself :
      gap * ‖r‖ ^ 2 +
        (inner ℝ (W p) r + inner ℝ (W r) p) + inner ℝ (W r) r ≥
        gap * ‖r‖ ^ 2 - 2 * b * ‖p‖ * ‖r‖ - b * ‖r‖ ^ 2 := by
    nlinarith [hcross', hself]
  have hcombined :
      mu * ‖psi‖ ^ 2 + inner ℝ (W p) p +
        (gap * ‖r‖ ^ 2 +
          (inner ℝ (W p) r + inner ℝ (W r) p) + inner ℝ (W r) r) ≥
        mu * ‖psi‖ ^ 2 + inner ℝ (W p) p +
          (-2 * b ^ 2 / gap * ‖p‖ ^ 2 + (gap / 2 - b) * ‖r‖ ^ 2) := by
    nlinarith [halgebra, hcrossself]
  have hlast :
      mu * ‖psi‖ ^ 2 + inner ℝ (W p) p - 2 * b ^ 2 / gap * ‖p‖ ^ 2 +
          (gap / 2 - b) * ‖r‖ ^ 2 ≤
        mu * ‖psi‖ ^ 2 + gap * ‖r‖ ^ 2 + inner ℝ (W p) p +
          (inner ℝ (W p) r + inner ℝ (W r) p) + inner ℝ (W r) r := by
    have h := hcombined
    simp only [sub_eq_add_neg] at h ⊢
    ring_nf at h ⊢
    linarith [h]
  calc
    mu * ‖psi‖ ^ 2 + inner ℝ (W p) p - 2 * b ^ 2 / gap * ‖p‖ ^ 2 +
        (gap / 2 - b) * ‖r‖ ^ 2 ≤
      mu * ‖psi‖ ^ 2 + gap * ‖r‖ ^ 2 + inner ℝ (W p) p +
        (inner ℝ (W p) r + inner ℝ (W r) p) + inner ℝ (W r) r := hlast
    _ ≤ q psi + inner ℝ (W psi) psi := by
      rw [hexpand]
      nlinarith [hqle]

end GroundStatePerturbation

end Tunneling
