import Tunneling.Euclid.Decomp

/-!
# The interaction bound `eq:gamma-L` and the exact compression `eq:exact-compression`
-/

namespace Tunneling
open MeasureTheory
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace WellGeometry
variable (G : WellGeometry d ι)

private theorem multiWellCrossKernel_le_of_sep
    (G : WellGeometry d ι) {i j : ι} (hij : i ≠ j) {x y : Eucl d}
    (hx : x ∈ G.D) (hy : y ∈ G.D) :
    multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) x y ≤
      2 ^ G.κ * G.L ^ (-G.κ) * ‖G.a i - G.a j‖ ^ (-G.κ) := by
  have hxR : ‖x‖ ≤ G.R := by
    have hx' : dist x 0 < G.R := Metric.mem_ball.mp (G.hDR hx)
    simpa [dist_eq_norm] using hx'.le
  have hyR : ‖y‖ ≤ G.R := by
    have hy' : dist y 0 < G.R := Metric.mem_ball.mp (G.hDR hy)
    simpa [dist_eq_norm] using hy'.le
  set d0 : Eucl d := G.a i - G.a j
  have hsep := G.hsep i j hij
  have hMpos : 0 < G.L * ‖d0‖ := by
    have h4R : 0 < 4 * G.R := mul_pos (by norm_num) G.hR
    simpa [d0] using lt_of_lt_of_le h4R hsep
  have hdpos : 0 < ‖d0‖ := (mul_pos_iff_of_pos_left G.hL).mp hMpos
  let e : Eucl d := (‖d0‖⁻¹ : ℝ) • d0
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos)]
    exact inv_mul_cancel₀ hdpos.ne'
  have hvec : (G.L * ‖d0‖ : ℝ) • e = G.L • d0 := by
    dsimp [e]
    rw [smul_smul]
    congr 1
    field_simp [hdpos.ne']
  have hdist := translatedCrossKernel_separation_of_mem_ball
    (x := -x) (y := y) he (by simpa using hxR) hyR hsep
  have hkernel : translatedCrossKernel G.κ ((G.L * ‖d0‖ : ℝ) • e) (-x) y ≤
      2 ^ G.κ * (G.L * ‖d0‖) ^ (-G.κ) :=
    translatedCrossKernel_le_of_lowerBound G.κ (G.L * ‖d0‖)
      ((G.L * ‖d0‖ : ℝ) • e) (-x) y G.hκ.le hMpos hdist
  have hpow : (G.L * ‖d0‖) ^ (-G.κ) =
      G.L ^ (-G.κ) * ‖d0‖ ^ (-G.κ) :=
    Real.mul_rpow G.hL.le (norm_nonneg d0)
  calc
    multiWellCrossKernel G.κ (G.L • d0) x y =
        translatedCrossKernel G.κ ((G.L * ‖d0‖ : ℝ) • e) (-x) y := by
          rw [multiWellCrossKernel, translatedCrossKernel, hvec]
          congr 1 <;> abel
    _ ≤ 2 ^ G.κ * (G.L * ‖d0‖) ^ (-G.κ) := hkernel
    _ = 2 ^ G.κ * G.L ^ (-G.κ) * ‖d0‖ ^ (-G.κ) := by rw [hpow]; ring

private theorem pieceL2_ae_zero
    (G : WellGeometry d ι) (i : ι) (f : L2 d) :
    ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D →
      (G.pieceL2 i f : Eucl d → ℝ) x = 0 := by
  filter_upwards [indicatorL2_ae G.D G.hDm
    (translateL2 (-(G.L • G.a i)) f)] with x hx
  intro hnot
  change ((indicatorL2 G.D G.hDm (translateL2 (-(G.L • G.a i)) f) : L2 d) : Eucl d → ℝ) x = 0
  simpa [Set.indicator_apply, hnot] using hx

private theorem ae_comp_snd_of_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {p : X → Prop} (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ z : X × X ∂(μ.prod μ), p z.2 := by
  exact Measure.quasiMeasurePreserving_snd.ae h

private theorem kernelCrossPairing_restrict_of_ae_zero
    (D : Set (Eucl d)) (hD : MeasurableSet D) (K : Eucl d → Eucl d → ℝ)
    (u v : L2 d)
    (hu : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ D → u x = 0)
    (hv : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ D → v x = 0) :
    kernelCrossPairing K (volume : Measure (Eucl d)) (u : Eucl d → ℝ) (v : Eucl d → ℝ) =
      kernelCrossPairing K (volume.restrict D) (u : Eucl d → ℝ) (v : Eucl d → ℝ) := by
  let A : Set (Eucl d × Eucl d) := D ×ˢ D
  have hA : MeasurableSet A := hD.prod hD
  have hu1 := ae_comp_fst_of_ae hu
  have hv2 := ae_comp_snd_of_ae (μ := (volume : Measure (Eucl d))) hv
  have hfun : (fun z : Eucl d × Eucl d =>
      (u : Eucl d → ℝ) z.1 * (v : Eucl d → ℝ) z.2 * K z.1 z.2) =ᵐ[volume.prod volume]
      A.indicator (fun z : Eucl d × Eucl d =>
        (u : Eucl d → ℝ) z.1 * (v : Eucl d → ℝ) z.2 * K z.1 z.2) := by
    filter_upwards [hu1, hv2] with z hux hvy
    rcases z with ⟨x, y⟩
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
    · simp [A, hx, hy]
    · have hzero := hvy hy
      simp [A, hx, hy, hzero]
    · have hzero := hux hx
      simp [A, hx, hy, hzero]
    · have hzero := hux hx
      simp [A, hx, hy, hzero]
  simp only [kernelCrossPairing]
  calc
    (∫ z : Eucl d × Eucl d,
        (u : Eucl d → ℝ) z.1 * (v : Eucl d → ℝ) z.2 * K z.1 z.2 ∂(volume.prod volume)) =
      ∫ z : Eucl d × Eucl d,
        A.indicator (fun z : Eucl d × Eucl d =>
          (u : Eucl d → ℝ) z.1 * (v : Eucl d → ℝ) z.2 * K z.1 z.2) z ∂(volume.prod volume) :=
        integral_congr_ae hfun
    _ = ∫ z : Eucl d × Eucl d,
        (u : Eucl d → ℝ) z.1 * (v : Eucl d → ℝ) z.2 * K z.1 z.2
          ∂((volume.prod volume).restrict A) := by rw [integral_indicator hA]
    _ = ∫ z : Eucl d × Eucl d,
        (u : Eucl d → ℝ) z.1 * (v : Eucl d → ℝ) z.2 * K z.1 z.2
          ∂((volume.restrict D).prod (volume.restrict D)) := by rw [← Measure.prod_restrict]

private theorem finite_schur_bound (a : ι → Eucl d) (κ σ : ℝ)
    (hσ : 0 ≤ σ)
    (hrow : ∀ i, ∑ j, (if i = j then (0 : ℝ) else ‖a i - a j‖ ^ (-κ)) ≤ σ)
    (r s : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) :
    ∑ i, ∑ j, (if i = j then (0 : ℝ) else ‖a i - a j‖ ^ (-κ)) * r i * s j ≤
      σ * Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ j, s j ^ 2) := by
  classical
  let w : ι → ι → ℝ := fun i j => if i = j then 0 else ‖a i - a j‖ ^ (-κ)
  have hw0 : ∀ i j, 0 ≤ w i j := by
    intro i j
    by_cases h : i = j
    · simp [w,h]
    · simp [w,h,Real.rpow_nonneg]
  have hwsym : ∀ i j, w i j = w j i := by
    intro i j
    by_cases h : i = j
    · simp [w,h]
    · have hji : j ≠ i := fun hh => h hh.symm
      simp [w,h,hji,norm_sub_rev]
  have hCS0 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (ι × ι))
    (r := fun p : ι × ι => w p.1 p.2 * r p.1 * s p.2)
    (f := fun p : ι × ι => w p.1 p.2 * r p.1 ^ 2)
    (g := fun p : ι × ι => w p.1 p.2 * s p.2 ^ 2)
    (fun p hp => mul_nonneg (hw0 p.1 p.2) (sq_nonneg (r p.1)))
    (fun p hp => mul_nonneg (hw0 p.1 p.2) (sq_nonneg (s p.2)))
    (fun p hp => by
      have heq : (w p.1 p.2 * r p.1 * s p.2) ^ 2 =
          (w p.1 p.2 * r p.1 ^ 2) * (w p.1 p.2 * s p.2 ^ 2) := by ring
      rw [heq])
  have hCS : (∑ i, ∑ j, w i j * r i * s j) ^ 2 ≤
      (∑ i, ∑ j, w i j * r i ^ 2) * (∑ i, ∑ j, w i j * s j ^ 2) := by
    simpa only [Fintype.sum_prod_type] using hCS0
  have hAeq : (∑ i, ∑ j, w i j * r i ^ 2) =
      ∑ i, r i ^ 2 * (∑ j, w i j) := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      ∑ j, w i j * r i ^ 2 = ∑ j, r i ^ 2 * w i j := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = r i ^ 2 * (∑ j, w i j) := (Finset.mul_sum _ _ _).symm
  have hBcol : ∀ j, ∑ i, w i j ≤ σ := by
    intro j
    calc
      ∑ i, w i j = ∑ i, w j i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hwsym i j
      _ ≤ σ := hrow j
  have hBeq : (∑ i, ∑ j, w i j * s j ^ 2) =
      ∑ j, s j ^ 2 * (∑ i, w i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      ∑ i, w i j * s j ^ 2 = ∑ i, s j ^ 2 * w i j := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = s j ^ 2 * (∑ i, w i j) := (Finset.mul_sum _ _ _).symm
  have hA : (∑ i, ∑ j, w i j * r i ^ 2) ≤ σ * ∑ i, r i ^ 2 := by
    rw [hAeq]
    calc
      ∑ i, r i ^ 2 * (∑ j, w i j) ≤ ∑ i, r i ^ 2 * σ :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
      _ = σ * ∑ i, r i ^ 2 := by rw [← Finset.sum_mul]; ring
  have hB : (∑ i, ∑ j, w i j * s j ^ 2) ≤ σ * ∑ j, s j ^ 2 := by
    rw [hBeq]
    calc
      ∑ j, s j ^ 2 * (∑ i, w i j) ≤ ∑ j, s j ^ 2 * σ :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hBcol j) (sq_nonneg _)
      _ = σ * ∑ j, s j ^ 2 := by rw [← Finset.sum_mul]; ring
  have hA0 : 0 ≤ ∑ i, ∑ j, w i j * r i ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hw0 i j) (sq_nonneg _)
  have hB0 : 0 ≤ ∑ i, ∑ j, w i j * s j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hw0 i j) (sq_nonneg _)
  have hRU : 0 ≤ ∑ i, r i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSV : 0 ≤ ∑ j, s j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hAB : (∑ i, ∑ j, w i j * r i ^ 2) *
      (∑ i, ∑ j, w i j * s j ^ 2) ≤ (σ * ∑ i, r i ^ 2) * (σ * ∑ j, s j ^ 2) := by
    apply mul_le_mul hA hB hB0
    exact mul_nonneg hσ hRU
  have hS0 : 0 ≤ ∑ i, ∑ j, w i j * r i * s j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hw0 i j) (hr i)) (hs j)
  have hbound0 : 0 ≤ σ * Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ j, s j ^ 2) := by positivity
  have hSq : (∑ i, ∑ j, w i j * r i * s j) ^ 2 ≤
      (σ * Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ j, s j ^ 2)) ^ 2 := by
    calc
      _ ≤ (∑ i, ∑ j, w i j * r i ^ 2) * (∑ i, ∑ j, w i j * s j ^ 2) := hCS
      _ ≤ (σ * ∑ i, r i ^ 2) * (σ * ∑ j, s j ^ 2) := hAB
      _ = (σ * Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ j, s j ^ 2)) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt hRU, Real.sq_sqrt hSV]
        ring
  have hS := (sq_le_sq₀ hS0 hbound0).mp hSq
  simpa [w] using hS

private theorem kernelCrossPairing_supported_le
    (G : WellGeometry d ι) {i j : ι} (hij : i ≠ j) (u v : L2 d)
    (hu : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → u x = 0)
    (hv : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → v x = 0) :
    |kernelCrossPairing (multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)))
      (volume : Measure (Eucl d)) (u : Eucl d → ℝ) (v : Eucl d → ℝ)| ≤
      (2 ^ G.κ * G.L ^ (-G.κ) * ‖G.a i - G.a j‖ ^ (-G.κ)) *
        (volume G.D).toReal * ‖u‖ * ‖v‖ := by
  classical
  have hDvol : volume G.D < ⊤ := by
    calc
      volume G.D ≤ volume (Metric.ball 0 G.R) := measure_mono G.hDR
      _ < ⊤ := measure_ball_lt_top
  let μD : Measure (Eucl d) := volume.restrict G.D
  haveI : IsFiniteMeasure μD := by
    constructor
    simpa [μD] using hDvol
  let C : ℝ := 2 ^ G.κ * G.L ^ (-G.κ) * ‖G.a i - G.a j‖ ^ (-G.κ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (Real.rpow_nonneg G.hL.le _))
      (Real.rpow_nonneg (norm_nonneg _) _)
  let K : Eucl d → Eucl d → ℝ := fun x y =>
    if x ∈ G.D ∧ y ∈ G.D then
      multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) x y else 0
  have hK : ∀ x y, |K x y| ≤ C := by
    intro x y
    by_cases hxy : x ∈ G.D ∧ y ∈ G.D
    · simp only [K]
      rw [if_pos hxy]
      have hk := multiWellCrossKernel_le_of_sep G hij hxy.1 hxy.2
      have hknonneg : 0 ≤ multiWellCrossKernel G.κ
          (G.L • (G.a i - G.a j)) x y := Real.rpow_nonneg (norm_nonneg _) _
      rw [abs_of_nonneg hknonneg]
      simpa [C] using hk
    · simp [K, hxy]
      exact hC
  have uMem : MemLp (u : Eucl d → ℝ) 2 μD := MemLp.restrict G.D (Lp.memLp u)
  have vMem : MemLp (v : Eucl d → ℝ) 2 μD := MemLp.restrict G.D (Lp.memLp v)
  let uD : Lp ℝ 2 μD := uMem.toLp (u : Eucl d → ℝ)
  let vD : Lp ℝ 2 μD := vMem.toLp (v : Eucl d → ℝ)
  have hnormu : ‖uD‖ ≤ ‖u‖ := by
    calc
      ‖uD‖ = ENNReal.toReal (eLpNorm (u : Eucl d → ℝ) 2 μD) := by
        dsimp [uD]
        exact Lp.norm_toLp _ _
      _ ≤ ENNReal.toReal (eLpNorm (u : Eucl d → ℝ) 2 (volume : Measure (Eucl d))) := by
        apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
        exact eLpNorm_restrict_le _ _ _ _
      _ = ‖u‖ := by rw [Lp.norm_def]
  have hnormv : ‖vD‖ ≤ ‖v‖ := by
    calc
      ‖vD‖ = ENNReal.toReal (eLpNorm (v : Eucl d → ℝ) 2 μD) := by
        dsimp [vD]
        exact Lp.norm_toLp _ _
      _ ≤ ENNReal.toReal (eLpNorm (v : Eucl d → ℝ) 2 (volume : Measure (Eucl d))) := by
        apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top v)
        exact eLpNorm_restrict_le _ _ _ _
      _ = ‖v‖ := by rw [Lp.norm_def]
  have hfull := kernelCrossPairing_restrict_of_ae_zero G.D G.hDm
    (multiWellCrossKernel G.κ (G.L • (G.a i - G.a j))) u v hu hv
  have hmem : ∀ᵐ x ∂μD, x ∈ G.D := ae_restrict_mem G.hDm
  have hfst := ae_comp_fst_of_ae (mu := μD) hmem
  have hsnd := ae_comp_snd_of_ae (μ := μD) hmem
  have hcap : kernelCrossPairing
      (multiWellCrossKernel G.κ (G.L • (G.a i - G.a j))) μD
      (u : Eucl d → ℝ) (v : Eucl d → ℝ) =
      kernelCrossPairing K μD (u : Eucl d → ℝ) (v : Eucl d → ℝ) := by
    simp only [kernelCrossPairing]
    apply integral_congr_ae
    filter_upwards [hfst, hsnd] with z hx hy
    rcases z with ⟨x, y⟩
    simp [K, hx, hy]
  have hrep : kernelCrossPairing K μD (u : Eucl d → ℝ) (v : Eucl d → ℝ) =
      kernelCrossPairing K μD (uD : Eucl d → ℝ) (vD : Eucl d → ℝ) := by
    simp only [kernelCrossPairing]
    apply integral_congr_ae
    have hu' := ae_comp_fst_of_ae (mu := μD) uMem.coeFn_toLp
    have hv' := ae_comp_snd_of_ae (μ := μD) vMem.coeFn_toLp
    filter_upwards [hu', hv'] with z hx hy
    rcases z with ⟨x, y⟩
    change (u : Eucl d → ℝ) x * (v : Eucl d → ℝ) y * K x y =
      (uD : Eucl d → ℝ) x * (vD : Eucl d → ℝ) y * K x y
    rw [← hx, ← hy]
  have hCross := kernelCrossPairing_Lp_le K C hC hK μD uD vD
  have hmass : 0 ≤ μD.real Set.univ := measureReal_nonneg
  have hnormprod : ‖uD‖ * ‖vD‖ ≤ ‖u‖ * ‖v‖ :=
    mul_le_mul hnormu hnormv (norm_nonneg _) (norm_nonneg _)
  calc
    |kernelCrossPairing (multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)))
       (volume : Measure (Eucl d)) (u : Eucl d → ℝ) (v : Eucl d → ℝ)| =
      |kernelCrossPairing K μD (uD : Eucl d → ℝ) (vD : Eucl d → ℝ)| := by
        rw [hfull, hcap, hrep]
    _ ≤ C * μD.real Set.univ * ‖uD‖ * ‖vD‖ := hCross
    _ ≤ C * μD.real Set.univ * ‖u‖ * ‖v‖ := by
        calc
          C * μD.real Set.univ * ‖uD‖ * ‖vD‖ =
              (C * μD.real Set.univ) * (‖uD‖ * ‖vD‖) := by ring
          _ ≤ (C * μD.real Set.univ) * (‖u‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left hnormprod (mul_nonneg hC hmass)
          _ = C * μD.real Set.univ * ‖u‖ * ‖v‖ := by ring
    _ = (2 ^ G.κ * G.L ^ (-G.κ) * ‖G.a i - G.a j‖ ^ (-G.κ)) *
        (volume G.D).toReal * ‖u‖ * ‖v‖ := by
        rw [MeasureTheory.measureReal_restrict_apply_univ]
        rfl

/-- The operator-norm bound `‖𝒱_L‖ ≤ γ_L` of equation `eq:gamma-L`. -/
theorem abs_interaction_le (c : ℝ) (hc : 0 ≤ c) (ψ χ : formDomain G.κ G.Ω) :
    |G.interaction c ψ χ| ≤
      c * 2 ^ G.κ * (volume G.D).toReal * sigmaKappa G.a G.κ * G.L ^ (-G.κ) *
        ‖(ψ : L2 d)‖ * ‖(χ : L2 d)‖ := by
  let r : ι → ℝ := fun i => ‖G.pieceL2 i (ψ : L2 d)‖
  let s : ι → ℝ := fun j => ‖G.pieceL2 j (χ : L2 d)‖
  let w : ι → ι → ℝ := fun i j =>
    if i = j then 0 else ‖G.a i - G.a j‖ ^ (-G.κ)
  let C0 : ℝ := 2 ^ G.κ * (volume G.D).toReal * G.L ^ (-G.κ)
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        MeasureTheory.measureReal_nonneg)
      (Real.rpow_nonneg G.hL.le _)
  have hr : ∀ i, 0 ≤ r i := fun i => norm_nonneg _
  have hs : ∀ j, 0 ≤ s j := fun j => norm_nonneg _
  have hterm (i j : ι) :
      |if i = j then (0 : ℝ) else
        G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))| ≤
        C0 * w i j * r i * s j := by
    by_cases hij : i = j
    · subst j
      simp [w]
    · simp only [if_neg hij]
      have hcross := kernelCrossPairing_supported_le G hij
        (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))
        (pieceL2_ae_zero G i (ψ : L2 d))
        (pieceL2_ae_zero G j (χ : L2 d))
      calc
        |G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))| ≤
          (2 ^ G.κ * G.L ^ (-G.κ) * ‖G.a i - G.a j‖ ^ (-G.κ)) *
            (volume G.D).toReal *
              ‖G.pieceL2 i (ψ : L2 d)‖ * ‖G.pieceL2 j (χ : L2 d)‖ := by
                simpa only [WellGeometry.crossPair] using hcross
        _ = C0 * w i j * r i * s j := by
          simp only [C0, w, r, s, if_neg hij]
          ring
  have hsum :
      |∑ i, ∑ j, if i = j then (0 : ℝ) else
        G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))| ≤
        C0 * sigmaKappa G.a G.κ *
          Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ j, s j ^ 2) := by
    calc
      _ ≤ ∑ i, |∑ j, if i = j then (0 : ℝ) else
          G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))| :=
        Finset.abs_sum_le_sum_abs
          (fun i : ι => ∑ j, if i = j then (0 : ℝ) else
            G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d)))
          Finset.univ
      _ ≤ ∑ i, ∑ j, C0 * w i j * r i * s j := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          |∑ j, if i = j then (0 : ℝ) else
              G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))| ≤
              ∑ j, |if i = j then (0 : ℝ) else
                G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))| :=
            Finset.abs_sum_le_sum_abs
              (fun j : ι => if i = j then (0 : ℝ) else
                G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d)))
              Finset.univ
          _ ≤ ∑ j, C0 * w i j * r i * s j :=
            Finset.sum_le_sum fun j hj => hterm i j
      _ = C0 * (∑ i, ∑ j, w i j * r i * s j) := by
        calc
          ∑ i, ∑ j, C0 * w i j * r i * s j =
              ∑ i, C0 * (∑ j, w i j * r i * s j) := by
                apply Finset.sum_congr rfl
                intro i hi
                calc
                  ∑ j, C0 * w i j * r i * s j =
                      ∑ j, C0 * (w i j * r i * s j) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
                  _ = C0 * ∑ j, w i j * r i * s j :=
                    (Finset.mul_sum _ _ _).symm
          _ = C0 * (∑ i, ∑ j, w i j * r i * s j) :=
            (Finset.mul_sum _ _ _).symm
      _ ≤ C0 * (sigmaKappa G.a G.κ *
          Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ j, s j ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (by
            simpa [w] using finite_schur_bound G.a G.κ (sigmaKappa G.a G.κ)
              (sigmaKappa_nonneg G.a G.κ)
              (fun i => row_le_sigmaKappa G.a G.κ i) r s hr hs)
          hC0
      _ = C0 * sigmaKappa G.a G.κ *
          Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ j, s j ^ 2) := by ring
  have hψnorm : (∑ i, r i ^ 2) = ‖(ψ : L2 d)‖ ^ 2 := by
    simpa [r, real_inner_self_eq_norm_sq] using (G.inner_eq_sum ψ ψ).symm
  have hχnorm : (∑ j, s j ^ 2) = ‖(χ : L2 d)‖ ^ 2 := by
    simpa [s, real_inner_self_eq_norm_sq] using (G.inner_eq_sum χ χ).symm
  have hψroot : Real.sqrt (∑ i, r i ^ 2) = ‖(ψ : L2 d)‖ := by
    rw [hψnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hχroot : Real.sqrt (∑ j, s j ^ 2) = ‖(χ : L2 d)‖ := by
    rw [hχnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    |G.interaction c ψ χ| =
        c * |∑ i, ∑ j, if i = j then (0 : ℝ) else
          G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))| := by
      rw [G.interaction_apply]
      simp [WellGeometry.interactionFun, abs_mul, abs_of_nonneg hc]
    _ ≤ c * (C0 * sigmaKappa G.a G.κ *
        Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ j, s j ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum hc
    _ = c * 2 ^ G.κ * (volume G.D).toReal * sigmaKappa G.a G.κ *
        G.L ^ (-G.κ) * ‖(ψ : L2 d)‖ * ‖(χ : L2 d)‖ := by
      rw [hψroot, hχroot]
      dsimp [C0]
      ring

/-- The compression of `𝒱_L` to the translated ground states is the matrix
`T_L` of equation `eq:exact-compression`. -/
theorem interaction_Φ (c : ℝ) (φ : formDomain G.κ G.D) (i j : ι) :
    G.interaction c (G.Φ φ i) (G.Φ φ j) =
      multiWellCompressionMatrix (volume : Measure (Eucl d)) G.κ c
        ((φ : L2 d) : Eucl d → ℝ) G.a G.L i j := by
  rw [G.interaction_apply]
  simp only [WellGeometry.interactionFun]
  have hterm (p q : ι) :
      (if p = q then (0 : ℝ) else
        G.crossPair p q (if p = i then (φ : L2 d) else 0)
          (if q = j then (φ : L2 d) else 0)) =
      if p = i then
        if q = j then (if i = j then (0 : ℝ) else G.crossPair i j φ φ)
        else 0
      else 0 := by
    by_cases hpi : p = i
    · subst p
      by_cases hqj : q = j
      · subst q
        by_cases hij : i = j <;> simp [hij]
      · simp [hqj, WellGeometry.crossPair, kernelCrossPairing]
    · simp [hpi, WellGeometry.crossPair, kernelCrossPairing]
  simp_rw [G.pieceL2_Φ]
  simp_rw [hterm]
  simp [WellGeometry.crossPair, multiWellCompressionMatrix_apply]
end WellGeometry
end Tunneling

