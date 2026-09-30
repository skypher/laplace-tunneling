import Tunneling.Euclid.FormDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Cube averaging: finite-dimensional approximation

For a bounded set `D ⊆ ℝ^d`, bounded subsets of `H^s_0(D)` are relatively
compact in `L²(ℝ^d)`.  This is paper Lemma 2.1 (`lem:compact`), which needs no
boundary regularity (the Lipschitz route via
[DiNezzaPalatucciValdinoci2012, Theorem 7.1] is not used), and is proved
by averaging over cubes of side `ε`: on a cube `Q` of diameter `√d ε`,

  `∫_Q |u - ⨍_Q u|² = (2|Q|)⁻¹ ∬_{Q×Q} |u(x)-u(y)|²
                     ≤ (√d ε)^κ (2 ε^d)⁻¹ ∬_{Q×Q} |u(x)-u(y)|² |x-y|^{-κ}`,

so the cube-average projection, whose range is finite dimensional on
functions supported in a bounded set, approximates `u` within
`C ε^s [u]`.  Lower semicontinuity of the Gagliardo energy follows from Fatou's
lemma along an a.e. convergent subsequence.
-/

namespace Tunneling
open MeasureTheory Filter Topology Function
variable {d : ℕ}

private def cell (e : ℝ) (k : Fin d → ℤ) : Set (Eucl d) :=
  {x | ∀ i, Int.floor (x i / e) = k i}

private theorem cell_eq_box (e : ℝ) (he : 0 < e) (k : Fin d → ℤ) :
    cell e k = (fun x : Eucl d => (x : Fin d → ℝ)) ⁻¹' Set.univ.pi
      (fun i => Set.Ico ((k i : ℝ) * e) (((k i : ℝ) + 1) * e)) := by
  ext x
  simp only [cell, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi]
  constructor
  · intro h i
    have hf := Int.floor_eq_iff.mp (h i)
    exact ⟨(le_div_iff₀ he).mp hf.1, (div_lt_iff₀ he).mp hf.2⟩
  · intro h i
    apply Int.floor_eq_iff.mpr
    exact ⟨(le_div_iff₀ he).mpr (h i).1, (div_lt_iff₀ he).mpr (h i).2⟩

private theorem cell_meas (e : ℝ) (he : 0 < e) (k : Fin d → ℤ) :
    MeasurableSet (cell e k) := by
  rw [cell_eq_box e he]
  exact (PiLp.volume_preserving_ofLp (Fin d)).measurable
    (MeasurableSet.univ_pi fun i => measurableSet_Ico)

private theorem cell_vol (e : ℝ) (he : 0 < e) (k : Fin d → ℤ) :
    (volume : Measure (Eucl d)) (cell e k) = ENNReal.ofReal e ^ d := by
  rw [cell_eq_box e he]
  have hbox : MeasurableSet
      (Set.univ.pi fun i : Fin d => Set.Ico ((k i : ℝ) * e) ((k i + 1) * e)) :=
    MeasurableSet.univ_pi fun i => measurableSet_Ico
  rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage hbox.nullMeasurableSet]
  rw [Real.volume_pi_Ico]
  simp [Finset.prod_const, Fintype.card_fin, sub_mul, add_mul, he.le]

private theorem cell_real_vol (e : ℝ) (he : 0 < e) (k : Fin d → ℤ) :
    (volume : Measure (Eucl d)).real (cell e k) = e ^ d := by
  rw [Measure.real_def, cell_vol e he k]
  simp [he.le]

private theorem cell_finite (e : ℝ) (he : 0 < e) (k : Fin d → ℤ) :
    (volume : Measure (Eucl d)) (cell e k) ≠ ⊤ := by
  rw [cell_vol e he k]
  simp

private theorem cell_disjoint (e : ℝ) {k l : Fin d → ℤ} (hkl : k ≠ l) :
    Disjoint (cell e k) (cell e l) := by
  rw [Set.disjoint_left]
  intro x hx hy
  apply hkl
  funext i
  exact (hx i).symm.trans (hy i)

private theorem cell_coord_abs_lt (e : ℝ) (he : 0 < e) (k : Fin d → ℤ)
    {x y : Eucl d} (hx : x ∈ cell e k) (hy : y ∈ cell e k) (i : Fin d) :
    |x i - y i| < e := by
  have hfx := Int.floor_eq_iff.mp (hx i)
  have hfy := Int.floor_eq_iff.mp (hy i)
  have hxl := (le_div_iff₀ he).mp hfx.1
  have hxu := (div_lt_iff₀ he).mp hfx.2
  have hyl := (le_div_iff₀ he).mp hfy.1
  have hyu := (div_lt_iff₀ he).mp hfy.2
  rw [abs_lt]
  constructor <;> nlinarith

private theorem cell_dist_le (e : ℝ) (he : 0 < e) (k : Fin d → ℤ)
    {x y : Eucl d} (hx : x ∈ cell e k) (hy : y ∈ cell e k) :
    dist x y ≤ (Real.sqrt (d : ℝ) + 1) * e := by
  have hsum : (∑ i : Fin d, dist (x i) (y i) ^ 2) ≤ d * e ^ 2 := by
    calc
      (∑ i : Fin d, dist (x i) (y i) ^ 2) ≤ ∑ i : Fin d, e ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := cell_coord_abs_lt e he k hx hy i
        exact (sq_le_sq₀ (abs_nonneg _) he.le).2 (le_of_lt h)
      _ = d * e ^ 2 := by simp [Finset.sum_const, Fintype.card_fin]
  have hsq : dist x y ^ 2 ≤ d * e ^ 2 := by simpa [EuclideanSpace.dist_sq_eq] using hsum
  have hd : 0 ≤ (Real.sqrt (d : ℝ) + 1) * e := by positivity
  have hr : (d : ℝ) * e ^ 2 ≤ ((Real.sqrt (d : ℝ) + 1) * e) ^ 2 := by
    have hroot : (Real.sqrt (d : ℝ)) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
    nlinarith [sq_nonneg (Real.sqrt (d : ℝ)), sq_nonneg e,
      Real.sqrt_nonneg (d : ℝ)]
  exact (sq_le_sq₀ (dist_nonneg) hd).mp (hsq.trans hr)

private theorem diffSq_le_kernel_bound (κ C : ℝ) (hκ : 0 < κ) (hC : 0 < C)
    (u : Eucl d → ℝ) (x y : Eucl d) (hxy : dist x y ≤ C) :
    (u x - u y) ^ 2 ≤ C ^ κ * gagliardoIntegrand κ u (x, y) := by
  by_cases h : x = y
  · subst y
    simp [gagliardoIntegrand]
  · have hr : 0 < dist x y := dist_pos.mpr h
    have hanti := Real.rpow_le_rpow_of_nonpos hr hxy (by linarith : -κ ≤ 0)
    have hpowC : 0 < C ^ κ := Real.rpow_pos_of_pos hC κ
    have hcancel : C ^ κ * C ^ (-κ) = 1 := by
      rw [Real.rpow_neg (le_of_lt hC), mul_inv_cancel₀ (ne_of_gt hpowC)]
    have hmul : 1 ≤ C ^ κ * (dist x y) ^ (-κ) := by
      calc
        1 = C ^ κ * C ^ (-κ) := hcancel.symm
        _ ≤ C ^ κ * (dist x y) ^ (-κ) := mul_le_mul_of_nonneg_left hanti hpowC.le
    have hker : 1 ≤ C ^ κ * gagliardoKernel κ x y := by
      simpa [gagliardoKernel, dist_eq_norm] using hmul
    calc
      (u x - u y) ^ 2 = 1 * (u x - u y) ^ 2 := by ring
      _ ≤ (C ^ κ * gagliardoKernel κ x y) * (u x - u y) ^ 2 :=
        mul_le_mul_of_nonneg_right hker (sq_nonneg _)
      _ = C ^ κ * gagliardoIntegrand κ u (x, y) := by
        simp [gagliardoIntegrand]
        ring

private noncomputable def cellIndices (e R : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d =>
    Finset.Icc (Int.floor (-R / e)) (Int.floor (R / e))

private theorem ball_cell_index (e R : ℝ) (he : 0 < e) {x : Eucl d}
    (hx : x ∈ Metric.closedBall 0 R) :
    (fun i : Fin d => Int.floor (x i / e)) ∈ cellIndices e R := by
  have hnorm : ‖x‖ ≤ R := by simpa using hx
  have hcoord (i : Fin d) : |x i| ≤ ‖x‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le x i
  simp only [cellIndices, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hxi := (abs_le.mp ((hcoord i).trans hnorm))
  constructor
  · apply Int.floor_mono
    exact (div_le_div_iff_of_pos_right he).2 hxi.1
  · apply Int.floor_mono
    exact (div_le_div_iff_of_pos_right he).2 hxi.2

private theorem variance_identity {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (Q : Set X) (hfin : μ Q ≠ ⊤) (hpos : 0 < μ.real Q) (f : X → ℝ)
    (hf : MemLp f 2 μ) :
    ∫ x in Q, (f x - (μ.real Q)⁻¹ * (∫ y in Q, f y ∂μ)) ^ 2 ∂μ =
      (2 * μ.real Q)⁻¹ * ∫ z in Q ×ˢ Q, (f z.1 - f z.2) ^ 2 ∂(μ.prod μ) := by
  let ν := μ.restrict Q
  let m := μ.real Q
  let A := ∫ x, f x ∂ν
  let B := ∫ x, f x ^ 2 ∂ν
  let a := m⁻¹ * A
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin
  have hfν : MemLp f 2 ν := hf.restrict Q
  have hfint : Integrable f ν := hfν.integrable (by norm_num)
  have hf2int : Integrable (fun x => f x ^ 2) ν := hfν.integrable_sq
  have hconst : Integrable (fun _ : X => (1 : ℝ)) ν := integrable_const 1
  have hmeasure : ν.real Set.univ = m := by simp [ν, m, Measure.real_def]
  have hm : ∫ x : X, (1 : ℝ) ∂ν = m := by simp [hmeasure]
  have hA : (∫ x in Q, f x ∂μ) = A := by rfl
  have hL : ∫ x in Q, (f x - a) ^ 2 ∂μ = B - 2 * a * A + a ^ 2 * m := by
    change ∫ x, (f x - a) ^ 2 ∂ν = _
    calc
      ∫ x, (f x - a) ^ 2 ∂ν = ∫ x, (f x ^ 2 - 2 * a * f x) + a ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = (∫ x, f x ^ 2 - 2 * a * f x ∂ν) + ∫ x, (a ^ 2 : ℝ) ∂ν :=
        integral_add (hf2int.sub (hfint.const_mul (2 * a))) (integrable_const (a ^ 2))
      _ = B - 2 * a * A + a ^ 2 * m := by
        rw [integral_sub hf2int (hfint.const_mul (2 * a)), integral_const_mul, hA]
        simp [A, B, a, hm, hmeasure]
        ring_nf
  have hP1 : Integrable (fun z : X × X => f z.1 ^ 2) (ν.prod ν) := by
    simpa using hf2int.mul_prod hconst
  have hP2 : Integrable (fun z : X × X => f z.2 ^ 2) (ν.prod ν) := by
    simpa using hconst.mul_prod hf2int
  have hP3 : Integrable (fun z : X × X => f z.1 * f z.2) (ν.prod ν) := hfint.mul_prod hfint
  have hD : ∫ z : X × X, (f z.1 - f z.2) ^ 2 ∂(ν.prod ν) = 2 * m * B - 2 * A ^ 2 := by
    have hpoint : (fun z : X × X => (f z.1 - f z.2) ^ 2) =
        fun z => (f z.1 ^ 2 + f z.2 ^ 2) - 2 * (f z.1 * f z.2) := by funext z; ring
    have hsum : Integrable (fun z : X × X => f z.1 ^ 2 + f z.2 ^ 2) (ν.prod ν) := hP1.add hP2
    rw [hpoint, integral_sub hsum (hP3.const_mul 2), integral_add hP1 hP2]
    have hp1 : ∫ z : X × X, f z.1 ^ 2 ∂(ν.prod ν) = B * m := by
      calc
        _ = ∫ z : X × X, f z.1 ^ 2 * (1 : ℝ) ∂(ν.prod ν) := by simp
        _ = (∫ x, f x ^ 2 ∂ν) * ∫ y, (1 : ℝ) ∂ν :=
          integral_prod_mul (μ := ν) (ν := ν) (fun x => f x ^ 2) (fun _ => 1)
        _ = B * m := by simp [B, hm]
    have hp2 : ∫ z : X × X, f z.2 ^ 2 ∂(ν.prod ν) = m * B := by
      calc
        _ = ∫ z : X × X, (1 : ℝ) * f z.2 ^ 2 ∂(ν.prod ν) := by simp
        _ = (∫ x, (1 : ℝ) ∂ν) * ∫ y, f y ^ 2 ∂ν :=
          integral_prod_mul (μ := ν) (ν := ν) (fun _ => 1) (fun y => f y ^ 2)
        _ = m * B := by simp [B, hm]
    have hp3 : ∫ z : X × X, f z.1 * f z.2 ∂(ν.prod ν) = A * A := by
      simpa [A] using (integral_prod_mul (μ := ν) (ν := ν) f f)
    rw [integral_const_mul, hp1, hp2, hp3]
    simp [A, B]
    ring
  have hD' : ∫ z in Q ×ˢ Q, (f z.1 - f z.2) ^ 2 ∂(μ.prod μ) =
      ∫ z : X × X, (f z.1 - f z.2) ^ 2 ∂(ν.prod ν) := by
    rw [← Measure.prod_restrict Q Q]
  change ∫ x in Q, (f x - a) ^ 2 ∂μ = (2 * m)⁻¹ *
      ∫ z in Q ×ˢ Q, (f z.1 - f z.2) ^ 2 ∂(μ.prod μ)
  rw [hL, hD', hD]
  have hm0 : m ≠ 0 := ne_of_gt hpos
  dsimp [a]
  field_simp
  <;> ring

private theorem L2_norm_sq_integral (u : L2 d) :
    ‖u‖ ^ 2 = ∫ x : Eucl d, (u x) ^ 2 ∂(volume : Measure (Eucl d)) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [Real.inner_apply]
  ring

private theorem squareDiff_integrableOn {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (Q : Set X) (hfin : μ Q ≠ ⊤) (f : X → ℝ) (hf : MemLp f 2 μ) :
    IntegrableOn (fun z : X × X => (f z.1 - f z.2) ^ 2) (Q ×ˢ Q) (μ.prod μ) := by
  let ν := μ.restrict Q
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin
  have hfν : MemLp f 2 ν := hf.restrict Q
  have hfint : Integrable f ν := hfν.integrable (by norm_num)
  have hf2int : Integrable (fun x => f x ^ 2) ν := hfν.integrable_sq
  have hconst : Integrable (fun _ : X => (1 : ℝ)) ν := integrable_const 1
  have hP1 : Integrable (fun z : X × X => f z.1 ^ 2) (ν.prod ν) := by
    simpa using hf2int.mul_prod hconst
  have hP2 : Integrable (fun z : X × X => f z.2 ^ 2) (ν.prod ν) := by
    simpa using hconst.mul_prod hf2int
  have hP3 : Integrable (fun z : X × X => f z.1 * f z.2) (ν.prod ν) := hfint.mul_prod hfint
  have hpoint : (fun z : X × X => (f z.1 - f z.2) ^ 2) =
      fun z => (f z.1 ^ 2 + f z.2 ^ 2) - 2 * (f z.1 * f z.2) := by funext z; ring
  have hD : Integrable (fun z : X × X => (f z.1 - f z.2) ^ 2) (ν.prod ν) := by
    rw [hpoint]
    exact (hP1.add hP2).sub (hP3.const_mul 2)
  change Integrable (fun z : X × X => (f z.1 - f z.2) ^ 2)
      ((μ.prod μ).restrict (Q ×ˢ Q))
  rw [← Measure.prod_restrict Q Q]
  exact hD

private theorem choose_eps (A B p δ : ℝ) (hp : 0 < p) (hδ : 0 < δ) :
    ∃ e : ℝ, 0 < e ∧ A * e ^ p * B < δ ^ 2 := by
  let u : ℕ → ℝ := fun n => 1 / (n + 1)
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa [u] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpow : Continuous (fun x : ℝ => x ^ p) := Real.continuous_rpow_const hp.le
  have hfirst : Continuous (fun x : ℝ => A * (x ^ p)) := continuous_const.mul hpow
  have hcont : Continuous (fun x : ℝ => (A * x ^ p) * B) := hfirst.mul continuous_const
  have hlim : Tendsto (fun n : ℕ => A * u n ^ p * B) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.zero_rpow hp.ne'] using hcont.continuousAt.tendsto.comp hu
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds (sq_pos_of_pos hδ))).exists
  refine ⟨u n, ?_, hn⟩
  dsimp [u]
  positivity

private theorem scale_identity (s e : ℝ) (he : 0 < e) (d : ℕ) :
    ((2 * e ^ d)⁻¹) * ((Real.sqrt (d : ℝ) + 1) * e) ^ ((d : ℝ) + 2 * s) =
      ((Real.sqrt (d : ℝ) + 1) ^ ((d : ℝ) + 2 * s) / 2) * e ^ (2 * s) := by
  have hc0 : 0 ≤ Real.sqrt (d : ℝ) + 1 := by positivity
  have hsub : ((d : ℝ) + 2 * s) - (d : ℝ) = 2 * s := by ring
  calc
    (2 * e ^ d)⁻¹ * ((Real.sqrt (d : ℝ) + 1) * e) ^ ((d : ℝ) + 2 * s) =
        ((Real.sqrt (d : ℝ) + 1) ^ ((d : ℝ) + 2 * s) / 2) *
          (e ^ ((d : ℝ) + 2 * s) / e ^ (d : ℝ)) := by
      rw [Real.mul_rpow hc0 (le_of_lt he), ← Real.rpow_natCast e d]
      field_simp [ne_of_gt he]
      <;> ring
    _ = (Real.sqrt (d : ℝ) + 1) ^ ((d : ℝ) + 2 * s) * e ^ (2 * s) / 2 := by
      rw [← Real.rpow_sub he, hsub]
      ring
    _ = (Real.sqrt (d : ℝ) + 1) ^ ((d : ℝ) + 2 * s) / 2 * e ^ (2 * s) := by ring

/-- Finite-dimensional approximation of energy-bounded functions supported in
a fixed ball (cube averaging). -/
theorem exists_finiteDimensional_approx (s : ℝ) (hs : 0 < s ∧ s < 1)
    (R : ℝ) (D : Set (Eucl d)) (hDR : D ⊆ Metric.closedBall 0 R)
    (M δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Submodule ℝ (L2 d), FiniteDimensional ℝ S ∧
      ∀ f ∈ formDomain ((d : ℝ) + 2 * s) D, ‖f‖ ≤ 1 →
        gagliardoSeminormSq ((d : ℝ) + 2 * s) (volume : Measure (Eucl d))
            (f : Eucl d → ℝ) ≤ M →
          ∃ p ∈ S, ‖p‖ ≤ 1 ∧ ‖f - p‖ ≤ δ := by
  classical
  let κ : ℝ := (d : ℝ) + 2 * s
  have hκ : 0 < κ := by dsimp [κ]; linarith [hs.1]
  let c0 : ℝ := Real.sqrt (d : ℝ) + 1
  let A : ℝ := c0 ^ κ / 2
  let B : ℝ := max M 0 + 1
  have hA : 0 < A := by
    dsimp [A, c0]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    linarith [le_max_right M 0]
  have hp : 0 < 2 * s := by linarith [hs.1]
  obtain ⟨e, he, heSmall⟩ := choose_eps A B (2 * s) δ hp hδ
  let F : Finset (Fin d → ℤ) := cellIndices e R
  let I := {k : Fin d → ℤ // k ∈ F}
  letI : Fintype I := Fintype.ofFinite I
  let μ : Measure (Eucl d) := volume
  let b : I → L2 d := fun i =>
    indicatorConstLp 2 (cell_meas e he i.1) (cell_finite e he i.1) (1 : ℝ)
  let S : Submodule ℝ (L2 d) := Submodule.span ℝ (Set.range b)
  have hSfin : FiniteDimensional ℝ S := by
    dsimp [S]
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  let U : Set (Eucl d) := ⋃ i : I, cell e i.1
  have hUmeas : MeasurableSet U := by
    exact MeasurableSet.iUnion fun i => cell_meas e he i.1
  have hcellDisj : Pairwise (Disjoint on fun i : I => cell e i.1) := by
    intro i j hij
    apply cell_disjoint e
    intro heq
    exact hij (Subtype.ext heq)
  let pairCell : I → Set (Eucl d × Eucl d) :=
    fun i => cell e i.1 ×ˢ cell e i.1
  have hpairMeas (i : I) : MeasurableSet (pairCell i) := by
    exact (cell_meas e he i.1).prod (cell_meas e he i.1)
  have hpairDisj : Pairwise (Disjoint on pairCell) := by
    intro i j hij
    change Disjoint (pairCell i) (pairCell j)
    rw [Set.disjoint_left]
    intro z hzi hzj
    rcases z with ⟨x, y⟩
    rcases hzi with ⟨hx, hy⟩
    rcases hzj with ⟨hx', hy'⟩
    have hval : i.1 ≠ j.1 := by
      intro heq
      exact hij (Subtype.ext heq)
    exact Set.disjoint_left.mp (cell_disjoint e hval) hx hx'
  refine ⟨S, hSfin, ?_⟩
  intro f hfDom hfNorm hfEnergy
  have hfD : f ∈ formDomain κ D := by simpa [κ] using hfDom
  let u : Eucl d → ℝ := (f : Eucl d → ℝ)
  let Kg : Eucl d × Eucl d → ℝ := fun z => gagliardoIntegrand κ u z
  have hKgInt : Integrable Kg (μ.prod μ) := by
    exact ((mem_formDomain_iff κ D f).mp hfD).2
  have hEbound : ∫ z, Kg z ∂(μ.prod μ) ≤ M := by
    simpa [Kg, κ, u, gagliardoSeminormSq] using hfEnergy
  let a : I → ℝ := fun i =>
    ((μ.real (cell e i.1))⁻¹) *
      (∫ x in cell e i.1, u x ∂μ)
  let q : L2 d := ∑ i : I, a i • b i
  have hqS : q ∈ S := by
    change (∑ i : I, a i • b i) ∈ Submodule.span ℝ (Set.range b)
    apply Submodule.sum_mem
    intro i hi
    apply S.smul_mem
    apply Submodule.subset_span
    exact ⟨i, rfl⟩
  have hsumm : (q : Eucl d → ℝ) =ᵐ[μ]
      fun x => ∑ i : I, a i * (cell e i.1).indicator (fun _ => (1 : ℝ)) x := by
    have hs : (q : Eucl d → ℝ) =ᵐ[μ]
        fun x => ∑ i ∈ Finset.univ, (a i • b i) x := by
      simpa [q] using
        (Lp.coeFn_fun_finsetSum (μ := μ) Finset.univ (fun i : I => a i • b i))
    have hm : ∀ᵐ x ∂μ, ∀ i : I, (a i • b i) x = a i * b i x := by
      apply ae_all_iff.2
      intro i
      filter_upwards [Lp.coeFn_smul (a i) (b i)] with x hx
      simpa using hx
    have hi : ∀ᵐ x ∂μ, ∀ i : I,
        b i x = (cell e i.1).indicator (fun _ => (1 : ℝ)) x := by
      apply ae_all_iff.2
      intro i
      exact indicatorConstLp_coeFn
    filter_upwards [hs, hm, hi] with x hsum hsmul hind
    calc
      q x = ∑ i ∈ Finset.univ, (a i • b i) x := hsum
      _ = ∑ i ∈ Finset.univ, a i * b i x := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsmul i
      _ = ∑ i ∈ Finset.univ, a i * (cell e i.1).indicator (fun _ => 1) x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hind i]
      _ = ∑ i : I, a i * (cell e i.1).indicator (fun _ => 1) x := by simp
  have hqcell : ∀ i : I, ∀ᵐ x ∂μ, x ∈ cell e i.1 → q x = a i := by
    intro i
    filter_upwards [hsumm] with x hq hx
    rw [hq]
    rw [Finset.sum_eq_single i]
    · simp [hx]
    · intro j hj hji
      have hval : i.1 ≠ j.1 := by
        intro heq
        exact hji (Subtype.ext heq.symm)
      have hxnot : x ∉ cell e j.1 := by
        intro hxj
        exact Set.disjoint_left.mp (cell_disjoint e hval) hx hxj
      simp [hxnot]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  let errFun : Eucl d → ℝ := fun x => ((f - q : L2 d) x) ^ 2
  have herrInt : Integrable errFun μ := by
    exact (Lp.memLp (f - q)).integrable_sq
  have hqOutside : ∀ᵐ x ∂μ, x ∉ U → (q : L2 d) x = 0 := by
    filter_upwards [hsumm] with x hq hxU
    rw [hq]
    apply Finset.sum_eq_zero
    intro i hi
    have hxnot : x ∉ cell e i.1 := by
      intro hxi
      apply hxU
      exact Set.mem_iUnion.mpr ⟨i, hxi⟩
    simp [hxnot]
  have hfOutside : ∀ᵐ x ∂μ, x ∉ U → (f : L2 d) x = 0 := by
    have hzeroD : ∀ᵐ x ∂μ, x ∉ D → (f : L2 d) x = 0 :=
      (mem_formDomain_iff κ D f).mp hfD |>.1
    filter_upwards [hzeroD] with x hzero hxU
    apply hzero
    intro hxD
    have hxBall : x ∈ Metric.closedBall 0 R := hDR hxD
    let k : Fin d → ℤ := fun i => Int.floor (x i / e)
    have hk : k ∈ cellIndices e R := by
      simpa [k, F] using ball_cell_index e R he hxBall
    have hxcell : x ∈ cell e k := by
      change ∀ i, Int.floor (x i / e) = k i
      intro i
      rfl
    apply hxU
    change x ∈ ⋃ i : I, cell e i.1
    exact Set.mem_iUnion.mpr ⟨⟨k, by simpa [F] using hk⟩, hxcell⟩
  have hErrOutside : ∀ᵐ x ∂μ, x ∉ U → (f - q : L2 d) x = 0 := by
    filter_upwards [Lp.coeFn_sub f q, hfOutside, hqOutside] with x hsub hf hq hxU
    change ((f - q : L2 d) x) = 0
    calc
      ((f - q : L2 d) x) = (f : L2 d) x - (q : L2 d) x := hsub
      _ = 0 := by rw [hf hxU, hq hxU]; ring
  have hErrZero : ∀ᵐ x ∂μ, x ∉ U → errFun x = 0 := by
    filter_upwards [hErrOutside] with x herr hxU
    change ((f - q : L2 d) x) ^ 2 = 0
    rw [herr hxU]
    simp
  have hglobalIntegral : ∫ x, errFun x ∂μ = ∫ x in U, errFun x ∂μ :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero hErrZero).symm
  have hUIntegral : ∫ x in U, errFun x ∂μ =
      ∑ i : I, ∫ x in cell e i.1, errFun x ∂μ := by
    simpa [U, errFun] using
      (integral_iUnion_fintype (ι := I) (s := fun i : I => cell e i.1)
        (fun i => cell_meas e he i.1) hcellDisj (fun i => herrInt.integrableOn))
  have hlocalEq (i : I) :
      ∫ x in cell e i.1, errFun x ∂μ =
        ∫ x in cell e i.1, (u x - a i) ^ 2 ∂μ := by
    apply setIntegral_congr_ae (cell_meas e he i.1)
    filter_upwards [Lp.coeFn_sub f q, hqcell i] with x hsub havg hx
    have havg' := havg hx
    calc
      errFun x = ((f - q : L2 d) x) ^ 2 := rfl
      _ = ((f : L2 d) x - (q : L2 d) x) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hsub
      _ = (u x - a i) ^ 2 := by rw [havg']
  let C : ℝ := c0 * e
  have hC : 0 < C := by dsimp [C, c0]; positivity
  have hPairDiff (i : I) :
      ∫ z in pairCell i, (u z.1 - u z.2) ^ 2 ∂(μ.prod μ) ≤
        C ^ κ * ∫ z in pairCell i, Kg z ∂(μ.prod μ) := by
    have hdiff : IntegrableOn
        (fun z : Eucl d × Eucl d => (u z.1 - u z.2) ^ 2)
        (pairCell i) (μ.prod μ) :=
      squareDiff_integrableOn μ (cell e i.1) (cell_finite e he i.1) u (Lp.memLp f)
    have hscaled : IntegrableOn
        (fun z : Eucl d × Eucl d => C ^ κ * Kg z) (pairCell i) (μ.prod μ) :=
      (hKgInt.const_mul (C ^ κ)).integrableOn
    calc
      ∫ z in pairCell i, (u z.1 - u z.2) ^ 2 ∂(μ.prod μ) ≤
          ∫ z in pairCell i, C ^ κ * Kg z ∂(μ.prod μ) := by
        apply setIntegral_mono_on hdiff hscaled (hpairMeas i)
        intro z hz
        rcases z with ⟨x, y⟩
        rcases hz with ⟨hx, hy⟩
        exact diffSq_le_kernel_bound κ C hκ hC u x y
          (cell_dist_le e he i.1 hx hy)
      _ = C ^ κ * ∫ z in pairCell i, Kg z ∂(μ.prod μ) := by
        rw [integral_const_mul]
  have hSumPairIntegral :
      ∫ z in ⋃ i : I, pairCell i, Kg z ∂(μ.prod μ) =
        ∑ i : I, ∫ z in pairCell i, Kg z ∂(μ.prod μ) := by
    simpa [pairCell] using
      (integral_iUnion_fintype (ι := I) (s := pairCell) hpairMeas hpairDisj
        (fun i => hKgInt.integrableOn))
  have hSumKernel : (∑ i : I, ∫ z in pairCell i, Kg z ∂(μ.prod μ)) ≤
      ∫ z, Kg z ∂(μ.prod μ) := by
    calc
      _ = ∫ z in ⋃ i : I, pairCell i, Kg z ∂(μ.prod μ) := hSumPairIntegral.symm
      _ ≤ ∫ z, Kg z ∂(μ.prod μ) :=
        setIntegral_le_integral hKgInt
          (ae_of_all _ fun z => gagliardoIntegrand_nonneg κ u z)
  have hSumDiff : (∑ i : I, ∫ z in pairCell i, (u z.1 - u z.2) ^ 2 ∂(μ.prod μ)) ≤
      C ^ κ * ∫ z, Kg z ∂(μ.prod μ) := by
    calc
      _ ≤ ∑ i : I, C ^ κ * ∫ z in pairCell i, Kg z ∂(μ.prod μ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hPairDiff i
      _ = C ^ κ * ∑ i : I, ∫ z in pairCell i, Kg z ∂(μ.prod μ) := by
        rw [Finset.mul_sum]
      _ ≤ C ^ κ * ∫ z, Kg z ∂(μ.prod μ) :=
        mul_le_mul_of_nonneg_left hSumKernel (Real.rpow_nonneg (le_of_lt hC) κ)
  let r : ℝ := (2 * (e ^ d : ℝ))⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hlocal (i : I) :
      ∫ x in cell e i.1, errFun x ∂μ =
        r * ∫ z in pairCell i, (u z.1 - u z.2) ^ 2 ∂(μ.prod μ) := by
    rw [hlocalEq i]
    have hpos : 0 < μ.real (cell e i.1) := by
      rw [cell_real_vol e he i.1]
      positivity
    have hvar := variance_identity μ (cell e i.1)
      (cell_finite e he i.1) hpos u (Lp.memLp f)
    rw [cell_real_vol e he i.1] at hvar
    simpa [a, r, pairCell, μ, cell_real_vol e he i.1] using hvar
  have hSumErr :
      (∑ i : I, ∫ x in cell e i.1, errFun x ∂μ) ≤
        r * C ^ κ * ∫ z, Kg z ∂(μ.prod μ) := by
    calc
      _ = ∑ i : I, r * ∫ z in pairCell i, (u z.1 - u z.2) ^ 2 ∂(μ.prod μ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hlocal i
      _ = r * ∑ i : I, ∫ z in pairCell i, (u z.1 - u z.2) ^ 2 ∂(μ.prod μ) := by
        rw [Finset.mul_sum]
      _ ≤ r * (C ^ κ * ∫ z, Kg z ∂(μ.prod μ)) :=
        mul_le_mul_of_nonneg_left hSumDiff (le_of_lt hr)
      _ = r * C ^ κ * ∫ z, Kg z ∂(μ.prod μ) := by ring
  have hscale : r * C ^ κ = A * e ^ (2 * s) := by
    dsimp [r, C, A, c0, κ]
    exact scale_identity s e he d
  have hqerror : ‖f - q‖ ^ 2 ≤ A * e ^ (2 * s) *
      ∫ z, Kg z ∂(μ.prod μ) := by
    calc
      ‖f - q‖ ^ 2 = ∫ x, errFun x ∂μ := by
        simpa [errFun] using L2_norm_sq_integral (f - q)
      _ = ∫ x in U, errFun x ∂μ := hglobalIntegral
      _ = ∑ i : I, ∫ x in cell e i.1, errFun x ∂μ := hUIntegral
      _ ≤ r * C ^ κ * ∫ z, Kg z ∂(μ.prod μ) := hSumErr
      _ = A * e ^ (2 * s) * ∫ z, Kg z ∂(μ.prod μ) := by rw [hscale]
  have hE0 : ∫ z, Kg z ∂(μ.prod μ) ≤ max M 0 :=
    hEbound.trans (le_max_left M 0)
  have hqerrorSmall : ‖f - q‖ ^ 2 < δ ^ 2 := by
    calc
      ‖f - q‖ ^ 2 ≤ A * e ^ (2 * s) * ∫ z, Kg z ∂(μ.prod μ) := hqerror
      _ ≤ A * e ^ (2 * s) * max M 0 :=
        mul_le_mul_of_nonneg_left hE0 (by positivity)
      _ ≤ A * e ^ (2 * s) * B := by
        apply mul_le_mul_of_nonneg_left
        · dsimp [B]
          linarith [le_max_right M 0]
        · positivity
      _ < δ ^ 2 := heSmall
  letI : FiniteDimensional ℝ S := hSfin
  letI : CompleteSpace S := FiniteDimensional.complete ℝ S
  let p : L2 d := S.starProjection f
  have hpS : p ∈ S := Submodule.starProjection_apply_mem S f
  have hpNorm : ‖p‖ ≤ 1 :=
    (Submodule.norm_starProjection_apply_le S f).trans hfNorm
  have hmin : ‖f - p‖ ≤ ‖f - q‖ := by
    have hbdd : BddBelow (Set.range fun x : S => ‖f - (x : L2 d)‖) :=
      ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
    calc
      ‖f - p‖ = ⨅ x : S, ‖f - x‖ := by
        simpa [p] using Submodule.starProjection_minimal (U := S) f
      _ ≤ ‖f - (⟨q, hqS⟩ : S)‖ := ciInf_le hbdd ⟨q, hqS⟩
      _ = ‖f - q‖ := by simp
  have hprojSq : ‖f - p‖ ^ 2 ≤ ‖f - q‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hmin
  have hfinal : ‖f - p‖ ≤ δ :=
    (sq_le_sq₀ (norm_nonneg _) hδ.le).mp
      (hprojSq.trans (le_of_lt hqerrorSmall))
  exact ⟨p, hpS, hpNorm, hfinal⟩

end Tunneling
