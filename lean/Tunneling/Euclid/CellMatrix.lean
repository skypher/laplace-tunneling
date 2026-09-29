import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Prod
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
open Filter
open scoped Topology

private noncomputable def lineCoord : Eucl 1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

private theorem lineCoord_apply (x : Eucl 1) : lineCoord x = x 0 := by
  rfl

private theorem lineCoord_mp : MeasurePreserving lineCoord volume volume := by
  change MeasurePreserving
    ((MeasurableEquiv.funUnique (Fin 1) ℝ) ∘ (WithLp.ofLp : Eucl 1 → (Fin 1 → ℝ))) volume volume
  exact (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))

/-- The cell of length `h` centred at `a` on the line `ℝ = Eucl 1`. -/
def lineCell (a h : ℝ) : Set (Eucl 1) := {x | |x 0 - a| < h / 2}

private theorem lineCell_eq_preimage (a h : ℝ) :
    lineCell a h = lineCoord ⁻¹' Set.Ioo (a - h / 2) (a + h / 2) := by
  ext x
  simp only [lineCell, Set.mem_setOf_eq, Set.mem_preimage, lineCoord_apply, Set.mem_Ioo, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem measurableSet_lineCell (a h : ℝ) : MeasurableSet (lineCell a h) := by
  rw [lineCell_eq_preimage]
  exact measurableSet_Ioo.preimage lineCoord.measurable

theorem volume_lineCell (a h : ℝ) (hh : 0 ≤ h) :
    volume (lineCell a h) = ENNReal.ofReal h := by
  rw [lineCell_eq_preimage,
    lineCoord_mp.measure_preimage measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo]
  congr 1
  ring

theorem volume_lineCell_ne_top (a h : ℝ) : volume (lineCell a h) ≠ ⊤ := by
  rw [lineCell_eq_preimage,
    lineCoord_mp.measure_preimage measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo]
  have hlen : (a + h / 2) - (a - h / 2) = h := by ring
  rw [hlen]
  exact ENNReal.ofReal_ne_top

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
  rw [cellVec, norm_smul, norm_indicatorConstLp (by norm_num) (by norm_num)]
  change ‖h ^ (-(1 / 2 : ℝ))‖ * (‖(1 : ℝ)‖ *
    (volume (lineCell a h)).toReal ^ (1 / (2 : ENNReal).toReal)) = 1
  rw [volume_lineCell a h hh.le, ENNReal.toReal_ofReal hh.le]
  have hpow : 1 / (2 : ENNReal).toReal = (1 / 2 : ℝ) := by norm_num
  rw [hpow, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hh _)]
  simp only [norm_one, one_mul]
  rw [← Real.rpow_add hh]
  norm_num

private noncomputable def realCellFun (l r x : ℝ) : ℝ :=
  (Set.Ioo l r).indicator (fun _ : ℝ => 1) x

private theorem intShiftTail {p x r : ℝ} (hp : p < -1) (hxr : x < r) :
    ∫ t in Set.Ioi r, (t - x) ^ p = - (r - x) ^ (p + 1) / (p + 1) := by
  have hden : p + 1 ≠ 0 := ne_of_lt (by linarith)
  have hd : ∀ t ∈ Set.Ici r,
      HasDerivAt (fun z : ℝ => (z - x) ^ (p + 1) / (p + 1)) ((t - x) ^ p) t := by
    intro t ht
    have hpos : 0 < t - x := by linarith [Set.mem_Ici.mp ht]
    have hpow := Real.hasDerivAt_rpow_const (x := t - x) (p := p + 1) (Or.inl hpos.ne')
    have hsub : HasDerivAt (fun z : ℝ => z - x) 1 t := (hasDerivAt_id t).sub_const x
    convert! (hpow.comp t hsub).div_const (p + 1) using 1
    simp [hden]
  have hint : IntegrableOn (fun t : ℝ => (t - x) ^ p) (Set.Ioi r) := by
    have hc : -(-x) < r := by linarith
    simpa [sub_eq_add_neg] using (integrableOn_add_rpow_Ioi_of_lt hp (m := -x) hc)
  have ht : Tendsto (fun t : ℝ => (t - x) ^ (p + 1) / (p + 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < -(p + 1))).comp
      (tendsto_atTop_add_const_right _ (-x) tendsto_id)
    simpa [sub_eq_add_neg] using h.div_const (p + 1)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint ht]
  ring

private theorem intIooShiftRpow (l r c p : ℝ) (hlr:l<r) (hp:-1<p) :
    ∫ x in Set.Ioo l r, (c-x)^p =
      ((c-l)^(p+1)-(c-r)^(p+1))/(p+1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlr.le]
  rw [intervalIntegral.integral_comp_sub_left (fun t:ℝ=>t^p) c]
  rw [integral_rpow (Or.inl hp)]

private theorem intIooShiftRpowInt (l r c p : ℝ) (hlr:l<r) (hp:-1<p):
    IntegrableOn (fun x:ℝ => (c-x)^p) (Set.Ioo l r) := by
  have hbase : IntervalIntegrable (fun t:ℝ => t^p) volume (c-r) (c-l) :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hcomp := hbase.comp_sub_left c
  have hcomp' : IntervalIntegrable (fun x:ℝ => (c-x)^p) volume l r := by
    convert hcomp.symm using 1 <;> congr 1 <;> ring
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr.le).mp hcomp'

private noncomputable def realTailBox (l r c p : ℝ) (z : ℝ × ℝ) : ℝ :=
  (Set.Ioo l r ×ˢ Set.Ioi c).indicator (fun z : ℝ × ℝ => |z.1-z.2|^p) z

private theorem realTailBox_inner {l r c p : ℝ} (hlr:l<r) (hrc:r≤c) (hp:p < -1) :
  ∀ x, ∫ y : ℝ, realTailBox l r c p (x,y) =
    (Set.Ioo l r).indicator (fun x => -((c-x)^(p+1))/(p+1)) x := by
  intro x
  by_cases hx : x ∈ Set.Ioo l r
  · have hxc : x < c := lt_of_lt_of_le hx.2 hrc
    have hfun : (fun y : ℝ => realTailBox l r c p (x,y)) =
        (Set.Ioi c).indicator (fun y => |x-y|^p) := by
      funext y
      by_cases hy : y ∈ Set.Ioi c
      · have hp : (x,y) ∈ Set.Ioo l r ×ˢ Set.Ioi c := ⟨hx,hy⟩
        simp [realTailBox, hp, hy]
      · have hn : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioi c := fun hz => hy hz.2
        simp [realTailBox, hn, hy]
    rw [hfun]
    calc
      ∫ y : ℝ, (Set.Ioi c).indicator (fun y => |x-y|^p) y =
          ∫ y in Set.Ioi c, |x-y|^p :=
        MeasureTheory.integral_indicator measurableSet_Ioi
      _ = ∫ y in Set.Ioi c, (y-x)^p := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        rw [abs_of_neg (sub_neg.mpr (lt_trans hxc (Set.mem_Ioi.mp hy)))]
        rw [show -(x-y) = y-x by ring]
      _ = -((c-x)^(p+1))/(p+1) := intShiftTail hp hxc
      _ = (Set.Ioo l r).indicator (fun x => -((c-x)^(p+1))/(p+1)) x := by
        simp [hx]
  · have hfun : (fun y : ℝ => realTailBox l r c p (x,y)) = 0 := by
      funext y
      have hn : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioi c := fun hz => hx hz.1
      simp [realTailBox, hn]
    rw [hfun]
    simp [hx]

private theorem realTailBox_integrable {l r c p : ℝ} (hlr:l<r) (hrc:r≤c)
    (hp : -2 < p ∧ p < -1) : Integrable (realTailBox l r c p) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (realTailBox l r c p) (volume.prod volume) := by
    have hm : Measurable (fun z : ℝ × ℝ => |z.1-z.2|^p) :=
      ((continuous_abs.comp (continuous_fst.sub continuous_snd)).measurable).pow_const p
    exact hm.aestronglyMeasurable.indicator (measurableSet_Ioo.prod measurableSet_Ioi)
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with x
    by_cases hx : x ∈ Set.Ioo l r
    · have hxc : x < c := lt_of_lt_of_le hx.2 hrc
      have htail : IntegrableOn (fun y : ℝ => (y-x)^p) (Set.Ioi c) := by
        have hc : -(-x) < c := by simpa using hxc
        simpa [sub_eq_add_neg] using (integrableOn_add_rpow_Ioi_of_lt hp.2 (m := -x) hc)
      have hfun : (fun y : ℝ => realTailBox l r c p (x,y)) =
        (Set.Ioi c).indicator (fun y => (y-x)^p) := by
        funext y
        by_cases hy : y ∈ Set.Ioi c
        · have hprod : (x,y) ∈ Set.Ioo l r ×ˢ Set.Ioi c := ⟨hx, hy⟩
          simp [realTailBox, hprod, hy, abs_of_neg (sub_neg.mpr (lt_trans hxc hy))]
        · have hn : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioi c := fun hz => hy hz.2
          simp [realTailBox, hn, hy]
      rw [hfun]
      exact htail.integrable_indicator measurableSet_Ioi
    · have hfun : (fun y : ℝ => realTailBox l r c p (x,y)) = 0 := by
        funext y
        have hn : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioi c := fun hz => hx hz.1
        simp [realTailBox, hn]
      rw [hfun]
      simpa using (integrable_zero (μ := volume) (E := ℝ))
  · have houter : Integrable
      ((Set.Ioo l r).indicator (fun x : ℝ => -((c-x)^(p+1))/(p+1))) volume := by
        have hpow := intIooShiftRpowInt l r c (p+1) hlr (by linarith [hp.1])
        have hmul : IntegrableOn (fun x : ℝ => (-1/(p+1)) * (c-x)^(p+1)) (Set.Ioo l r) :=
          hpow.const_mul _
        have hmul' : Integrable ((Set.Ioo l r).indicator
          (fun x : ℝ => (-1/(p+1)) * (c-x)^(p+1))) volume :=
          hmul.integrable_indicator measurableSet_Ioo
        convert hmul' using 1
        congr 1
        funext x
        ring_nf
    have hnorm : (fun x : ℝ => ∫ y, ‖realTailBox l r c p (x,y)‖) =
        (Set.Ioo l r).indicator (fun x => -((c-x)^(p+1))/(p+1)) := by
      funext x
      rw [← realTailBox_inner hlr hrc hp.2]
      apply integral_congr_ae
      filter_upwards with y
      apply Real.norm_of_nonneg
      change 0 ≤ (Set.Ioo l r ×ˢ Set.Ioi c).indicator
        (fun z : ℝ×ℝ => |z.1-z.2|^p) (x,y)
      by_cases hz : (x,y) ∈ Set.Ioo l r ×ˢ Set.Ioi c
      · rw [Set.indicator_of_mem hz]
        exact Real.rpow_nonneg (abs_nonneg _) _
      · rw [Set.indicator_of_notMem hz]
    rw [hnorm]
    exact houter

private theorem realTailBox_integral {l r c p : ℝ} (hlr:l<r) (hrc:r≤c)
    (hp : -2 < p ∧ p < -1) :
    ∫ z : ℝ×ℝ, realTailBox l r c p z ∂(volume.prod volume) =
    -(((c-l)^(p+2)-(c-r)^(p+2))/(p+2))/(p+1) := by
  have hint := realTailBox_integrable hlr hrc hp
  rw [integral_prod _ hint]
  rw [show (fun x : ℝ => ∫ y : ℝ, realTailBox l r c p (x,y)) =
      (Set.Ioo l r).indicator (fun x => -((c-x)^(p+1))/(p+1)) from by
    funext x; exact realTailBox_inner hlr hrc hp.2 x]
  rw [integral_indicator measurableSet_Ioo]
  calc
    ∫ x in Set.Ioo l r, -((c-x)^(p+1))/(p+1) =
        ∫ x in Set.Ioo l r, (-1/(p+1)) * (c-x)^(p+1) := by
      apply integral_congr_ae
      exact MeasureTheory.ae_of_all _ (fun x => by ring)
    _ = (-1/(p+1)) * ∫ x in Set.Ioo l r, (c-x)^(p+1) := integral_const_mul _ _
    _ = -(((c-l)^(p+2)-(c-r)^(p+2))/(p+2))/(p+1) := by
      rw [intIooShiftRpow l r c (p+1) hlr (by linarith [hp.1])]
      ring_nf



private noncomputable def realStepEnergy (l r p : ℝ) (z : ℝ × ℝ) : ℝ :=
  (realCellFun l r z.1 - realCellFun l r z.2)^2 * |z.1-z.2|^p
private noncomputable def realRightBox (l r p : ℝ) (z : ℝ × ℝ) : ℝ :=
  (Set.Ioo l r ×ˢ Set.Ioi r).indicator (fun z : ℝ × ℝ => |z.1-z.2|^p) z
private noncomputable def realLeftBox (l r p : ℝ) (z : ℝ × ℝ) : ℝ :=
  (Set.Ioo l r ×ˢ Set.Iio l).indicator (fun z : ℝ × ℝ => |z.1-z.2|^p) z
private theorem realStep_box_eq {l r p x y : ℝ} (hlr : l < r)
    (hxl : x ≠ l) (hxr : x ≠ r) (hyl : y ≠ l) (hyr : y ≠ r) :
    realStepEnergy l r p (x,y) =
      realRightBox l r p (x,y) + realLeftBox l r p (x,y) +
        realRightBox l r p (y,x) + realLeftBox l r p (y,x) := by
  by_cases hx : x ∈ Set.Ioo l r
  · by_cases hy : y ∈ Set.Ioo l r
    · have hRxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
        rintro ⟨_, hg⟩
        linarith [hy.2, Set.mem_Ioi.mp hg]
      have hLxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
        rintro ⟨_, hg⟩
        linarith [hy.1, Set.mem_Iio.mp hg]
      have hRyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
        rintro ⟨_, hg⟩
        linarith [hx.2, Set.mem_Ioi.mp hg]
      have hLyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
        rintro ⟨_, hg⟩
        linarith [hx.1, Set.mem_Iio.mp hg]
      simp [realStepEnergy, realCellFun, realRightBox, realLeftBox,
        hx, hy, hRxy, hLxy, hRyx, hLyx]
    · have hyout : y < l ∨ r < y := by
        rcases lt_trichotomy y l with hlt | heq | hgt
        · exact Or.inl hlt
        · exact (hyl heq).elim
        · rcases lt_trichotomy y r with h | heq' | h
          · exact (hy ⟨hgt,h⟩).elim
          · exact (hyr heq').elim
          · exact Or.inr h
      rcases hyout with hylo | hyhi
      · have hRxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
          rintro ⟨_, hg⟩
          linarith [hlr, hylo, Set.mem_Ioi.mp hg]
        have hLxy : (x,y) ∈ Set.Ioo l r ×ˢ Set.Iio l := ⟨hx,hylo⟩
        have hRyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
          rintro ⟨hg,_⟩
          exact hy hg
        have hLyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
          rintro ⟨hg,_⟩
          exact hy hg
        simp [realStepEnergy, realCellFun, realRightBox, realLeftBox,
          hx, hy, hRxy, hLxy, hRyx, hLyx]
      · have hRxy : (x,y) ∈ Set.Ioo l r ×ˢ Set.Ioi r := ⟨hx,hyhi⟩
        have hLxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
          rintro ⟨_, hg⟩
          linarith [hyhi, Set.mem_Iio.mp hg, hlr]
        have hRyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
          rintro ⟨hg,_⟩
          exact hy hg
        have hLyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
          rintro ⟨hg,_⟩
          exact hy hg
        simp [realStepEnergy, realCellFun, realRightBox, realLeftBox,
          hx, hy, hRxy, hLxy, hRyx, hLyx]
  · by_cases hy : y ∈ Set.Ioo l r
    · have hxout : x < l ∨ r < x := by
        rcases lt_trichotomy x l with hlt | heq | hgt
        · exact Or.inl hlt
        · exact (hxl heq).elim
        · rcases lt_trichotomy x r with h | heq' | h
          · exact (hx ⟨hgt,h⟩).elim
          · exact (hxr heq').elim
          · exact Or.inr h
      rcases hxout with hxlo | hxhi
      · have hRxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
          rintro ⟨hg,_⟩
          exact hx hg
        have hLxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
          rintro ⟨hg,_⟩
          exact hx hg
        have hRyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
          rintro ⟨_, hg⟩
          linarith [hxlo, Set.mem_Ioi.mp hg, hlr]
        have hLyx : (y,x) ∈ Set.Ioo l r ×ˢ Set.Iio l := ⟨hy,hxlo⟩
        simp [realStepEnergy, realCellFun, realRightBox, realLeftBox,
          hx, hy, hRxy, hLxy, hRyx, hLyx, abs_sub_comm]
      · have hRxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
          rintro ⟨hg,_⟩
          exact hx hg
        have hLxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
          rintro ⟨hg,_⟩
          exact hx hg
        have hRyx : (y,x) ∈ Set.Ioo l r ×ˢ Set.Ioi r := ⟨hy,hxhi⟩
        have hLyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
          rintro ⟨_, hg⟩
          linarith [hxhi, Set.mem_Iio.mp hg, hlr]
        simp [realStepEnergy, realCellFun, realRightBox, realLeftBox,
          hx, hy, hRxy, hLxy, hRyx, hLyx, abs_sub_comm]
    · have hRxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
        rintro ⟨hg,_⟩
        exact hx hg
      have hLxy : (x,y) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
        rintro ⟨hg,_⟩
        exact hx hg
      have hRyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Ioi r := by
        rintro ⟨hg,_⟩
        exact hy hg
      have hLyx : (y,x) ∉ Set.Ioo l r ×ˢ Set.Iio l := by
        rintro ⟨hg,_⟩
        exact hy hg
      simp [realStepEnergy, realCellFun, realRightBox, realLeftBox,
        hx, hy, hRxy, hLxy, hRyx, hLyx]

private theorem ae_no_cell_endpoints {l r : ℝ} :
    ∀ᵐ z : ℝ×ℝ ∂(volume.prod volume),
      z.1 ≠ l ∧ z.1 ≠ r ∧ z.2 ≠ l ∧ z.2 ≠ r := by
  have hl : ∀ᵐ x : ℝ ∂volume, x ≠ l := volume.ae_ne l
  have hr : ∀ᵐ x : ℝ ∂volume, x ≠ r := volume.ae_ne r
  have hl1 : ∀ᵐ z : ℝ×ℝ ∂(volume.prod volume), z.1 ≠ l :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae hl
  have hr1 : ∀ᵐ z : ℝ×ℝ ∂(volume.prod volume), z.1 ≠ r :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae hr
  have hl2 : ∀ᵐ z : ℝ×ℝ ∂(volume.prod volume), z.2 ≠ l :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae hl
  have hr2 : ∀ᵐ z : ℝ×ℝ ∂(volume.prod volume), z.2 ≠ r :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae hr
  filter_upwards [hl1, hr1, hl2, hr2] with z hz1 hz2 hz3 hz4
  exact ⟨hz1,hz2,hz3,hz4⟩
private theorem realRightBox_integrable {l r p : ℝ} (hlr:l<r) (hp:-2<p ∧ p < -1) :
    Integrable (realRightBox l r p) (volume.prod volume) := by
  change Integrable (realTailBox l r r p) (volume.prod volume)
  exact realTailBox_integrable hlr le_rfl hp
private noncomputable def realNegPair : ℝ×ℝ ≃ᵐ ℝ×ℝ :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.neg ℝ)
private theorem realLeftBox_integrable {l r p : ℝ} (hlr:l<r) (hp:-2<p ∧ p < -1) :
    Integrable (realLeftBox l r p) (volume.prod volume) := by
  have hneg : MeasurePreserving realNegPair (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hbase : Integrable (realTailBox (-r) (-l) (-l) p) (volume.prod volume) :=
    realTailBox_integrable (by linarith) le_rfl hp
  have hcomp := hneg.integrable_comp_of_integrable hbase
  have heq : realLeftBox l r p = realTailBox (-r) (-l) (-l) p ∘ realNegPair := by
    funext z
    change (Set.Ioo l r ×ˢ Set.Iio l).indicator
        (fun w : ℝ×ℝ => |w.1-w.2|^p) z =
      (Set.Ioo (-r) (-l) ×ˢ Set.Ioi (-l)).indicator
        (fun w : ℝ×ℝ => |w.1-w.2|^p) (realNegPair z)
    have hmem : z ∈ Set.Ioo l r ×ˢ Set.Iio l ↔
        realNegPair z ∈ Set.Ioo (-r) (-l) ×ˢ Set.Ioi (-l) := by
      rcases z with ⟨x,y⟩
      change ((l < x ∧ x < r) ∧ y < l) ↔
        ((-r < -x ∧ -x < -l) ∧ -l < -y)
      constructor
      · rintro ⟨⟨h₁,h₂⟩,h₃⟩
        exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
      · rintro ⟨⟨h₁,h₂⟩,h₃⟩
        exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    by_cases hz : z ∈ Set.Ioo l r ×ˢ Set.Iio l
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hmem.mp hz)]
      have hn : realNegPair z = (-z.1,-z.2) := by rfl
      rw [hn]
      have habs : |z.1-z.2| = |(-z.1)-(-z.2)| := by
        rw [show (-z.1)-(-z.2) = -(z.1-z.2) by ring, abs_neg]
      rw [habs]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun hh => hz (hmem.mpr hh))]
  rw [heq]
  exact hcomp
private theorem realStepEnergy_integrable {l r p : ℝ} (hlr:l<r) (hp:-2<p ∧ p < -1) :
    Integrable (realStepEnergy l r p) (volume.prod volume) := by
  have hR := realRightBox_integrable hlr hp
  have hL := realLeftBox_integrable hlr hp
  have hswap : MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume) :=
    MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  have hRs := hswap.integrable_comp_of_integrable hR
  have hLs := hswap.integrable_comp_of_integrable hL
  have hsum : Integrable
      (fun z : ℝ×ℝ => realRightBox l r p z + realLeftBox l r p z +
        realRightBox l r p (z.2,z.1) + realLeftBox l r p (z.2,z.1))
      (volume.prod volume) := by exact ((hR.add hL).add hRs).add hLs
  have heq : realStepEnergy l r p =ᵐ[volume.prod volume]
      (fun z => realRightBox l r p z + realLeftBox l r p z +
        realRightBox l r p (z.2,z.1) + realLeftBox l r p (z.2,z.1)) := by
    filter_upwards [ae_no_cell_endpoints (l:=l) (r:=r)] with z hz
    exact realStep_box_eq hlr hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  exact hsum.congr heq.symm



private theorem lineCoord_norm_sub (x y : Eucl 1) :
    ‖x-y‖ = |lineCoord x-lineCoord y| := by
  simp [EuclideanSpace.norm_eq, lineCoord_apply, Real.sqrt_sq_eq_abs]
private theorem lineCell_indicator_eq (a h : ℝ) (x : Eucl 1) :
    (lineCell a h).indicator (fun _ : Eucl 1 => (1:ℝ)) x =
      realCellFun (a-h/2) (a+h/2) (lineCoord x) := by
  have hmem : x ∈ lineCell a h ↔ lineCoord x ∈ Set.Ioo (a-h/2) (a+h/2) := by
    rw [lineCell_eq_preimage]
    exact Set.mem_preimage
  by_cases hx : x ∈ lineCell a h
  · simp [realCellFun, hx, hmem.mp hx]
  · have hnot : lineCoord x ∉ Set.Ioo (a-h/2) (a+h/2) := fun hy => hx (hmem.mpr hy)
    simp [realCellFun, hx, hnot]
private theorem cellVec_line_rep (a h : ℝ) :
    (cellVec a h : Eucl 1 → ℝ) =ᵐ[volume]
      (fun x => h ^ (-(1/2:ℝ)) * realCellFun (a-h/2) (a+h/2) (lineCoord x)) := by
  have hs := Lp.coeFn_smul (h ^ (-(1/2:ℝ)))
    (indicatorConstLp 2 (measurableSet_lineCell a h) (volume_lineCell_ne_top a h) (1:ℝ))
  have hs' :
      (cellVec a h : Eucl 1 → ℝ) =ᵐ[volume]
        (fun x => h ^ (-(1/2:ℝ)) *
          (indicatorConstLp 2 (measurableSet_lineCell a h)
            (volume_lineCell_ne_top a h) (1:ℝ) : Eucl 1 → ℝ) x) := by
    filter_upwards [hs] with x hx
    change ((h ^ (-(1/2:ℝ)) •
      indicatorConstLp 2 (measurableSet_lineCell a h)
        (volume_lineCell_ne_top a h) (1:ℝ) : L2 1) : Eucl 1 → ℝ) x =
      h ^ (-(1/2:ℝ)) *
        (indicatorConstLp 2 (measurableSet_lineCell a h)
          (volume_lineCell_ne_top a h) (1:ℝ) : Eucl 1 → ℝ) x
    simpa only [Pi.smul_apply, smul_eq_mul] using hx
  have hi :
      (indicatorConstLp 2 (measurableSet_lineCell a h)
        (volume_lineCell_ne_top a h) (1:ℝ) : L2 1) =ᵐ[volume]
        (lineCell a h).indicator (fun _ : Eucl 1 => (1:ℝ)) := by
    exact indicatorConstLp_coeFn
  filter_upwards [hs',hi] with x hsx hix
  rw [hsx,hix,lineCell_indicator_eq]

private noncomputable def linePairEquiv : Eucl 1 × Eucl 1 ≃ᵐ ℝ×ℝ :=
  MeasurableEquiv.prodCongr lineCoord lineCoord
private theorem linePair_mp : MeasurePreserving linePairEquiv (volume.prod volume) (volume.prod volume) :=
  lineCoord_mp.prod lineCoord_mp
private theorem cellVec_gag_ae (a h κ : ℝ) :
    (fun z : Eucl 1 × Eucl 1 =>
      gagliardoIntegrand κ (cellVec a h : Eucl 1 → ℝ) z) =ᵐ[volume.prod volume]
    (fun z => (h ^ (-(1/2:ℝ)))^2 *
      realStepEnergy (a-h/2) (a+h/2) (-κ) (linePairEquiv z)) := by
  have hr := cellVec_line_rep a h
  have hfst := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Eucl 1))) (ν := (volume : Measure (Eucl 1)))).ae_eq_comp hr
  have hsnd := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Eucl 1))) (ν := (volume : Measure (Eucl 1)))).ae_eq_comp hr
  filter_upwards [hfst,hsnd] with z hz₁ hz₂
  have hz₁' :
      (cellVec a h : Eucl 1 → ℝ) z.1 =
        h ^ (-(1/2:ℝ)) * realCellFun (a-h/2) (a+h/2) (lineCoord z.1) := by
    simpa using hz₁
  have hz₂' :
      (cellVec a h : Eucl 1 → ℝ) z.2 =
        h ^ (-(1/2:ℝ)) * realCellFun (a-h/2) (a+h/2) (lineCoord z.2) := by
    simpa using hz₂
  simp only [gagliardoIntegrand, gagliardoKernel]
  rw [hz₁',hz₂',lineCoord_norm_sub]
  change (h ^ (-(1/2:ℝ)) *
      realCellFun (a-h/2) (a+h/2) (lineCoord z.1) -
      h ^ (-(1/2:ℝ)) *
      realCellFun (a-h/2) (a+h/2) (lineCoord z.2))^2 *
      |lineCoord z.1-lineCoord z.2|^(-κ) =
    (h ^ (-(1/2:ℝ)))^2 *
      ((realCellFun (a-h/2) (a+h/2) (lineCoord z.1) -
        realCellFun (a-h/2) (a+h/2) (lineCoord z.2))^2 *
        |lineCoord z.1-lineCoord z.2|^(-κ))
  ring



private theorem realStepEnergy_integral {l r p : ℝ} (hlr:l<r) (hp:-2<p ∧ p < -1) :
    ∫ z : ℝ×ℝ, realStepEnergy l r p z ∂(volume.prod volume) =
      -4 * (((r-l)^(p+2)-0^(p+2))/(p+2))/(p+1) := by
  have hR := realRightBox_integrable hlr hp
  have hL := realLeftBox_integrable hlr hp
  have hswap : MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume) :=
    MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
  have hRs := hswap.integrable_comp_of_integrable hR
  have hLs := hswap.integrable_comp_of_integrable hL
  have hsum : Integrable
      (fun z : ℝ×ℝ => realRightBox l r p z + realLeftBox l r p z +
        realRightBox l r p (z.2,z.1) + realLeftBox l r p (z.2,z.1))
      (volume.prod volume) := by exact ((hR.add hL).add hRs).add hLs
  have heq : realStepEnergy l r p =ᵐ[volume.prod volume]
      (fun z => realRightBox l r p z + realLeftBox l r p z +
        realRightBox l r p (z.2,z.1) + realLeftBox l r p (z.2,z.1)) := by
    filter_upwards [ae_no_cell_endpoints (l:=l) (r:=r)] with z hz
    exact realStep_box_eq hlr hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  have hneg : MeasurePreserving realNegPair (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hLval : ∫ z : ℝ×ℝ, realLeftBox l r p z ∂(volume.prod volume) =
      ∫ z : ℝ×ℝ, realTailBox (-r) (-l) (-l) p z ∂(volume.prod volume) := by
    have heqL : realLeftBox l r p = realTailBox (-r) (-l) (-l) p ∘ realNegPair := by
      funext z
      change (Set.Ioo l r ×ˢ Set.Iio l).indicator
          (fun w : ℝ×ℝ => |w.1-w.2|^p) z =
        (Set.Ioo (-r) (-l) ×ˢ Set.Ioi (-l)).indicator
          (fun w : ℝ×ℝ => |w.1-w.2|^p) (realNegPair z)
      have hmem : z ∈ Set.Ioo l r ×ˢ Set.Iio l ↔
          realNegPair z ∈ Set.Ioo (-r) (-l) ×ˢ Set.Ioi (-l) := by
        rcases z with ⟨x,y⟩
        change ((l < x ∧ x < r) ∧ y < l) ↔
          ((-r < -x ∧ -x < -l) ∧ -l < -y)
        constructor
        · rintro ⟨⟨h₁,h₂⟩,h₃⟩
          exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
        · rintro ⟨⟨h₁,h₂⟩,h₃⟩
          exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
      by_cases hz : z ∈ Set.Ioo l r ×ˢ Set.Iio l
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hmem.mp hz)]
        have hn : realNegPair z = (-z.1,-z.2) := by rfl
        rw [hn]
        have habs : |z.1-z.2| = |(-z.1)-(-z.2)| := by
          rw [show (-z.1)-(-z.2) = -(z.1-z.2) by ring, abs_neg]
        rw [habs]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun hh => hz (hmem.mpr hh))]
    rw [heqL]
    change ∫ z : ℝ×ℝ, realTailBox (-r) (-l) (-l) p (realNegPair z)
      ∂(volume.prod volume) = _
    exact hneg.integral_comp realNegPair.measurableEmbedding _
  have hLtoR :
      ∫ z : ℝ×ℝ, realTailBox (-r) (-l) (-l) p z ∂(volume.prod volume) =
      ∫ z : ℝ×ℝ, realRightBox l r p z ∂(volume.prod volume) := by
    rw [realTailBox_integral (by linarith) le_rfl hp]
    rw [show realRightBox l r p = realTailBox l r r p from by
      funext z; rfl]
    rw [realTailBox_integral hlr le_rfl hp]
    rw [show (-l)-(-r)=r-l by ring, show (-l)-(-l)=0 by ring, sub_self]
  have hswR : ∫ z : ℝ×ℝ, realRightBox l r p (z.2,z.1) ∂(volume.prod volume) =
      ∫ z : ℝ×ℝ, realRightBox l r p z ∂(volume.prod volume) := by
    change ∫ z, realRightBox l r p (Prod.swap z) ∂(volume.prod volume) = _
    rw [hswap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding _]
  have hswL : ∫ z : ℝ×ℝ, realLeftBox l r p (z.2,z.1) ∂(volume.prod volume) =
      ∫ z : ℝ×ℝ, realLeftBox l r p z ∂(volume.prod volume) := by
    change ∫ z, realLeftBox l r p (Prod.swap z) ∂(volume.prod volume) = _
    rw [hswap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding _]
  calc
    ∫ z : ℝ×ℝ, realStepEnergy l r p z ∂(volume.prod volume) =
      ∫ z : ℝ×ℝ, realRightBox l r p z + realLeftBox l r p z +
        realRightBox l r p (z.2,z.1) + realLeftBox l r p (z.2,z.1) ∂(volume.prod volume) :=
      integral_congr_ae heq
    _ = (∫ z, realRightBox l r p z ∂(volume.prod volume)) +
        (∫ z, realLeftBox l r p z ∂(volume.prod volume)) +
        (∫ z, realRightBox l r p (z.2,z.1) ∂(volume.prod volume)) +
        (∫ z, realLeftBox l r p (z.2,z.1) ∂(volume.prod volume)) := by
      calc
        _ = ∫ z, (realRightBox l r p z + realLeftBox l r p z) +
              (realRightBox l r p (z.2,z.1) + realLeftBox l r p (z.2,z.1))
              ∂(volume.prod volume) := by
          apply integral_congr_ae
          filter_upwards with z
          ring
        _ = (∫ z, realRightBox l r p z + realLeftBox l r p z
                ∂(volume.prod volume)) +
              ∫ z, realRightBox l r p (z.2,z.1) + realLeftBox l r p (z.2,z.1)
                ∂(volume.prod volume) :=
          integral_add (hR.add hL) (hRs.add hLs)
        _ = (∫ z, realRightBox l r p z ∂(volume.prod volume)) +
              (∫ z, realLeftBox l r p z ∂(volume.prod volume)) +
              (∫ z, realRightBox l r p (z.2,z.1) ∂(volume.prod volume)) +
              (∫ z, realLeftBox l r p (z.2,z.1) ∂(volume.prod volume)) := by
          have hswadd :
              ∫ z : ℝ×ℝ, realRightBox l r p (z.2,z.1) +
                realLeftBox l r p (z.2,z.1) ∂(volume.prod volume) =
              (∫ z, realRightBox l r p (z.2,z.1) ∂(volume.prod volume)) +
                ∫ z, realLeftBox l r p (z.2,z.1) ∂(volume.prod volume) := by
            change ∫ z : ℝ×ℝ, (realRightBox l r p ∘ Prod.swap) z +
                (realLeftBox l r p ∘ Prod.swap) z ∂(volume.prod volume) = _
            exact integral_add hRs hLs
          rw [hswadd, integral_add hR hL]
          ring_nf
    _ = 4 * (∫ z, realRightBox l r p z ∂(volume.prod volume)) := by
      have hLvalR := hLval.trans hLtoR
      rw [hLvalR, hswR, hswL, hLvalR]
      ring
    _ = -4 * (((r-l)^(p+2)-0^(p+2))/(p+2))/(p+1) := by
      rw [show realRightBox l r p = realTailBox l r r p from by funext z; rfl]
      rw [realTailBox_integral hlr le_rfl hp]
      ring_nf

private theorem cellVec_gag_integral (a h κ : ℝ) :
    ∫ z : Eucl 1×Eucl 1, gagliardoIntegrand κ (cellVec a h : Eucl 1 → ℝ) z
        ∂(volume.prod volume) =
      (h ^ (-(1/2:ℝ)))^2 *
        ∫ z : ℝ×ℝ,
          realStepEnergy (a-h/2) (a+h/2) (-κ) z ∂(volume.prod volume) := by
  calc
    ∫ z : Eucl 1×Eucl 1, gagliardoIntegrand κ (cellVec a h : Eucl 1 → ℝ) z
        ∂(volume.prod volume) =
      ∫ z : Eucl 1×Eucl 1,
        (h ^ (-(1/2:ℝ)))^2 *
          realStepEnergy (a-h/2) (a+h/2) (-κ) (linePairEquiv z)
        ∂(volume.prod volume) := integral_congr_ae (cellVec_gag_ae a h κ)
    _ = ∫ z : ℝ×ℝ,
        (h ^ (-(1/2:ℝ)))^2 *
          realStepEnergy (a-h/2) (a+h/2) (-κ) z
        ∂(volume.prod volume) := by
      change ∫ z : Eucl 1×Eucl 1,
        (fun w : ℝ×ℝ => (h ^ (-(1/2:ℝ)))^2 *
          realStepEnergy (a-h/2) (a+h/2) (-κ) w) (linePairEquiv z)
        ∂(volume.prod volume) = _
      exact linePair_mp.integral_comp linePairEquiv.measurableEmbedding
        (fun w : ℝ×ℝ => (h ^ (-(1/2:ℝ)))^2 *
          realStepEnergy (a-h/2) (a+h/2) (-κ) w)
    _ = (h ^ (-(1/2:ℝ)))^2 *
          ∫ z : ℝ×ℝ,
            realStepEnergy (a-h/2) (a+h/2) (-κ) z
            ∂(volume.prod volume) := integral_const_mul _ _


private theorem cellVec_domain_proof
    (s : ℝ) (hs : 0 < s ∧ s < 1 / 2) (a h : ℝ) (hh : 0 < h)
    (G : Set (Eucl 1)) (hG : lineCell a h ⊆ G) :
    cellVec a h ∈ formDomain (1 + 2 * s) G := by
  rw [mem_formDomain_iff]
  constructor
  · have hrep := cellVec_line_rep a h
    filter_upwards [hrep] with x hrep
    intro hxG
    have hxcell : x ∉ lineCell a h := fun hx => hxG (hG hx)
    rw [hrep]
    have hxcoord : lineCoord x ∉ Set.Ioo (a-h/2) (a+h/2) := by
      intro hcoord
      apply hxcell
      rw [lineCell_eq_preimage]
      exact Set.mem_preimage.mpr hcoord
    simp [realCellFun, hxcoord]
  · have hp : -2 < -(1 + 2*s) ∧ -(1 + 2*s) < -1 := by
      constructor <;> nlinarith [hs.1, hs.2]
    have hlr : a - h/2 < a + h/2 := by linarith
    have hreal : Integrable
        (realStepEnergy (a-h/2) (a+h/2) (-(1+2*s))) (volume.prod volume) :=
      realStepEnergy_integrable hlr hp
    have hscaled : Integrable
        (fun z : ℝ×ℝ => (h ^ (-(1/2:ℝ)))^2 *
          realStepEnergy (a-h/2) (a+h/2) (-(1+2*s)) z) (volume.prod volume) :=
      hreal.const_mul _
    have hcomp : Integrable
        (fun z : Eucl 1×Eucl 1 => (h ^ (-(1/2:ℝ)))^2 *
          realStepEnergy (a-h/2) (a+h/2) (-(1+2*s)) (linePairEquiv z))
        (volume.prod volume) := by
      change Integrable
        ((fun w : ℝ×ℝ => (h ^ (-(1/2:ℝ)))^2 *
          realStepEnergy (a-h/2) (a+h/2) (-(1+2*s)) w) ∘ linePairEquiv)
        (volume.prod volume)
      exact linePair_mp.integrable_comp_of_integrable hscaled
    have ha := cellVec_gag_ae a h (1+2*s)
    exact hcomp.congr ha.symm


private theorem cellMatrix_diag_proof (c s : ℝ) (hs : 0 < s ∧ s < 1 / 2)
    (a h : ℝ) (hh : 0 < h) :
    formBilin c (1 + 2 * s) (cellVec a h) (cellVec a h) =
      c / h * (2 * h ^ (1 - 2 * s) / (2 * s * (1 - 2 * s))) := by
  have hq : 0 < 1 - 2*s := by nlinarith [hs.2]
  have hp : -2 < -(1 + 2*s) ∧ -(1 + 2*s) < -1 := by
    constructor <;> nlinarith [hs.1, hs.2]
  have hlr : a-h/2 < a+h/2 := by linarith
  have htsq : (h ^ (-(1/2:ℝ)))^2 = h⁻¹ := by
    rw [pow_two, ← Real.rpow_add hh]
    norm_num [Real.rpow_neg_one]
  have hs0 : 2*s ≠ 0 := ne_of_gt (mul_pos (by norm_num) hs.1)
  have hq0 : 1 - 2*s ≠ 0 := hq.ne'
  have hh0 : h ≠ 0 := hh.ne'
  unfold formBilin
  have hcross :
      (fun z : Eucl 1×Eucl 1 =>
        ((cellVec a h : Eucl 1 → ℝ) z.1 - (cellVec a h : Eucl 1 → ℝ) z.2) *
        ((cellVec a h : Eucl 1 → ℝ) z.1 - (cellVec a h : Eucl 1 → ℝ) z.2) *
        gagliardoKernel (1+2*s) z.1 z.2) =ᵐ[volume.prod volume]
      (fun z => gagliardoIntegrand (1+2*s) (cellVec a h : Eucl 1 → ℝ) z) := by
    filter_upwards with z
    simp only [gagliardoIntegrand]
    ring
  rw [integral_congr_ae hcross, cellVec_gag_integral]
  rw [realStepEnergy_integral hlr hp]
  have hpow2 : -(1+2*s)+2 = 1-2*s := by ring
  have hpow1 : -(1+2*s)+1 = -2*s := by ring
  rw [hpow2, hpow1]
  rw [Real.zero_rpow (ne_of_gt hq)]
  rw [show a+h/2-(a-h/2)=h by ring]
  rw [htsq]
  field_simp [hh0, hs0, hq0]
  <;> ring


private noncomputable def realFiniteCellBox (l r c d p : ℝ) (z : ℝ×ℝ) : ℝ :=
  (Set.Ioo l r ×ˢ Set.Ioo c d).indicator
    (fun z : ℝ×ℝ => |z.1-z.2|^p) z

private theorem intIooShiftRightRpow (c d x p : ℝ) (hcd:c<d) (hxc:x<c)
    (hp:p < -1) :
    ∫ y in Set.Ioo c d, (y-x)^p =
      ((d-x)^(p+1)-(c-x)^(p+1))/(p+1) := by
  have hcdx : c-x < d-x := by linarith
  have hzero : (0:ℝ) ∉ Set.uIcc (c-x) (d-x) := by
    intro hz
    rw [Set.uIcc_of_le hcdx.le] at hz
    rcases Set.mem_Icc.mp hz with ⟨hz₁, hz₂⟩
    linarith
  have hden : p ≠ -1 := ne_of_lt (by linarith)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hcd.le]
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => t^p) x]
  rw [integral_rpow (Or.inr ⟨hden,hzero⟩)]

private theorem realFiniteCellBox_inner {l r c d p : ℝ}
    (hlr:l<r) (hrc:r≤c) (hcd:c<d) (hp:-2<p ∧ p < -1) :
    ∀ x, ∫ y : ℝ, realFiniteCellBox l r c d p (x,y) =
      (Set.Ioo l r).indicator
        (fun x => ((d-x)^(p+1)-(c-x)^(p+1))/(p+1)) x := by
  intro x
  by_cases hx : x ∈ Set.Ioo l r
  · have hxc : x < c := lt_of_lt_of_le hx.2 hrc
    have hfun : (fun y : ℝ => realFiniteCellBox l r c d p (x,y)) =
        (Set.Ioo c d).indicator (fun y => (y-x)^p) := by
      funext y
      by_cases hy : y ∈ Set.Ioo c d
      · have hrect : (x,y) ∈ Set.Ioo l r ×ˢ Set.Ioo c d := ⟨hx,hy⟩
        have hyx : x-y < 0 := by
          have hyc : c < y := hy.1
          linarith
        simp [realFiniteCellBox,hrect,hy,abs_of_neg hyx]
      · have hn : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioo c d := fun hz => hy hz.2
        simp [realFiniteCellBox,hn,hy]
    rw [hfun]
    calc
      ∫ y : ℝ, (Set.Ioo c d).indicator (fun y => (y-x)^p) y =
        ∫ y in Set.Ioo c d, (y-x)^p := integral_indicator measurableSet_Ioo
      _ = ((d-x)^(p+1)-(c-x)^(p+1))/(p+1) :=
        intIooShiftRightRpow c d x p hcd hxc hp.2
      _ = (Set.Ioo l r).indicator
          (fun x => ((d-x)^(p+1)-(c-x)^(p+1))/(p+1)) x := by simp [hx]
  · have hfun : (fun y : ℝ => realFiniteCellBox l r c d p (x,y)) = 0 := by
      funext y
      have hn : (x,y) ∉ Set.Ioo l r ×ˢ Set.Ioo c d := fun hz => hx hz.1
      simp [realFiniteCellBox,hn]
    rw [hfun]
    simp [hx]

private theorem realFiniteCellBox_integrable {l r c d p : ℝ}
    (hlr:l<r) (hrc:r≤c) (hcd:c<d) (hp:-2<p ∧ p < -1) :
    Integrable (realFiniteCellBox l r c d p) (volume.prod volume) := by
  have htail := realTailBox_integrable hlr hrc hp
  have hm : AEStronglyMeasurable (realFiniteCellBox l r c d p) (volume.prod volume) := by
    have hm0 : Measurable (fun z : ℝ×ℝ => |z.1-z.2|^p) :=
      ((continuous_abs.comp (continuous_fst.sub continuous_snd)).measurable).pow_const p
    exact hm0.aestronglyMeasurable.indicator (measurableSet_Ioo.prod measurableSet_Ioo)
  apply htail.mono_nonneg hm
  · filter_upwards with z
    by_cases hz : z ∈ Set.Ioo l r ×ˢ Set.Ioo c d
    · simp [realFiniteCellBox,hz,Real.rpow_nonneg]
    · simp [realFiniteCellBox,hz]
  · filter_upwards with z
    by_cases hz : z ∈ Set.Ioo l r ×ˢ Set.Ioo c d
    · have hzy : z.2 ∈ Set.Ioi c := hz.2.1
      have hbase : z ∈ Set.Ioo l r ×ˢ Set.Ioi c := ⟨hz.1,hzy⟩
      simp [realFiniteCellBox,realTailBox,hz,hbase]
    · have htailnonneg : 0 ≤ realTailBox l r c p z := by
        unfold realTailBox
        by_cases hz' : z ∈ Set.Ioo l r ×ˢ Set.Ioi c
        · simp [hz']
          exact Real.rpow_nonneg (abs_nonneg _) _
        · simp [hz']
      simpa [realFiniteCellBox,hz] using htailnonneg

private theorem realFiniteCellBox_integral {l r c d p : ℝ}
    (hlr:l<r) (hrc:r≤c) (hcd:c<d) (hp:-2<p ∧ p < -1) :
    ∫ z : ℝ×ℝ, realFiniteCellBox l r c d p z ∂(volume.prod volume) =
      (((d-l)^(p+2)-(d-r)^(p+2)) -
        ((c-l)^(p+2)-(c-r)^(p+2))) / ((p+1)*(p+2)) := by
  have hbox := realFiniteCellBox_integrable hlr hrc hcd hp
  have hD := intIooShiftRpowInt l r d (p+1) hlr (by linarith [hp.1])
  have hC := intIooShiftRpowInt l r c (p+1) hlr (by linarith [hp.1])
  rw [integral_prod _ hbox]
  rw [show (fun x : ℝ => ∫ y : ℝ, realFiniteCellBox l r c d p (x,y)) =
      (Set.Ioo l r).indicator
        (fun x => ((d-x)^(p+1)-(c-x)^(p+1))/(p+1)) from by
    funext x
    exact realFiniteCellBox_inner hlr hrc hcd hp x]
  rw [integral_indicator measurableSet_Ioo]
  have houter :
      ∫ x in Set.Ioo l r,
        ((d-x)^(p+1)-(c-x)^(p+1))/(p+1) =
      (1/(p+1)) *
        ((∫ x in Set.Ioo l r, (d-x)^(p+1)) -
          (∫ x in Set.Ioo l r, (c-x)^(p+1))) := by
    calc
      ∫ x in Set.Ioo l r,
          ((d-x)^(p+1)-(c-x)^(p+1))/(p+1) =
        ∫ x in Set.Ioo l r,
          (1/(p+1))*((d-x)^(p+1)-(c-x)^(p+1)) := by
            apply integral_congr_ae
            exact MeasureTheory.ae_of_all _ (fun x => by ring)
      _ = (1/(p+1)) *
          ∫ x in Set.Ioo l r, (d-x)^(p+1)-(c-x)^(p+1) := integral_const_mul _ _
      _ = (1/(p+1)) *
          ((∫ x in Set.Ioo l r, (d-x)^(p+1)) -
            (∫ x in Set.Ioo l r, (c-x)^(p+1))) := by rw [integral_sub hD hC]
  rw [houter]
  change (1/(p+1)) *
      ((∫ x in Set.Ioo l r, (d-x)^(p+1)) -
       (∫ x in Set.Ioo l r, (c-x)^(p+1))) = _
  rw [intIooShiftRpow l r d (p+1) hlr (by linarith [hp.1]),
    intIooShiftRpow l r c (p+1) hlr (by linarith [hp.1])]
  field_simp
  ring



private noncomputable def realCrossEnergy (l r c d p : ℝ) (z : ℝ×ℝ) : ℝ :=
  (realCellFun l r z.1 - realCellFun l r z.2) *
    (realCellFun c d z.1 - realCellFun c d z.2) * |z.1-z.2|^p

private theorem realCross_box_eq {l r c d p : ℝ} (hrc : r ≤ c)
    (z : ℝ×ℝ) :
    realCrossEnergy l r c d p z =
      - realFiniteCellBox l r c d p z -
        realFiniteCellBox l r c d p (z.2,z.1) := by
  rcases z with ⟨x,y⟩
  have hdisj (w : ℝ) : ¬ (w ∈ Set.Ioo l r ∧ w ∈ Set.Ioo c d) := by
    rintro ⟨⟨_, hwr⟩, ⟨hwc, _⟩⟩
    linarith
  by_cases hxi : x ∈ Set.Ioo l r <;> by_cases hxj : x ∈ Set.Ioo c d <;>
    by_cases hyi : y ∈ Set.Ioo l r <;> by_cases hyj : y ∈ Set.Ioo c d
  all_goals
    first
    | exact False.elim (hdisj x ⟨hxi,hxj⟩)
    | exact False.elim (hdisj y ⟨hyi,hyj⟩)
    | (simp [realCrossEnergy, realFiniteCellBox, realCellFun, hxi, hxj, hyi, hyj, abs_sub_comm] <;> ring)


private theorem realCrossEnergy_integrable {l r c d p : ℝ}
    (hlr : l < r) (hrc : r ≤ c) (hcd : c < d)
    (hp : -2 < p ∧ p < -1) :
    Integrable (realCrossEnergy l r c d p) (volume.prod volume) := by
  have hbox := realFiniteCellBox_integrable hlr hrc hcd hp
  have hswap : MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume) :=
    MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
  have hboxswap := hswap.integrable_comp_of_integrable hbox
  have hsum : Integrable
      (fun z : ℝ×ℝ => -realFiniteCellBox l r c d p z -
        realFiniteCellBox l r c d p (z.2,z.1)) (volume.prod volume) :=
    hbox.neg.sub hboxswap
  have heq : realCrossEnergy l r c d p =ᵐ[volume.prod volume]
      (fun z => -realFiniteCellBox l r c d p z -
        realFiniteCellBox l r c d p (z.2,z.1)) := by
    filter_upwards with z
    exact realCross_box_eq hrc z
  exact hsum.congr heq.symm

private theorem realCrossEnergy_integral {l r c d p : ℝ}
    (hlr : l < r) (hrc : r ≤ c) (hcd : c < d)
    (hp : -2 < p ∧ p < -1) :
    ∫ z : ℝ×ℝ, realCrossEnergy l r c d p z ∂(volume.prod volume) =
      -2 * (((d-l)^(p+2)-(d-r)^(p+2) -
        ((c-l)^(p+2)-(c-r)^(p+2))) / ((p+1)*(p+2))) := by
  have hbox := realFiniteCellBox_integrable hlr hrc hcd hp
  have hswap : MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume) :=
    MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
  have hboxswap := hswap.integrable_comp_of_integrable hbox
  have heq : realCrossEnergy l r c d p =ᵐ[volume.prod volume]
      (fun z => -realFiniteCellBox l r c d p z -
        realFiniteCellBox l r c d p (z.2,z.1)) := by
    filter_upwards with z
    exact realCross_box_eq hrc z
  have hsw :
      ∫ z : ℝ×ℝ, realFiniteCellBox l r c d p (Prod.swap z) ∂(volume.prod volume) =
        ∫ z : ℝ×ℝ, realFiniteCellBox l r c d p z ∂(volume.prod volume) := by
    exact hswap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding _
  rw [integral_congr_ae heq]
  change ∫ z : ℝ×ℝ, -realFiniteCellBox l r c d p z -
      (realFiniteCellBox l r c d p ∘ Prod.swap) z ∂(volume.prod volume) = _
  calc
    _ = (∫ z : ℝ×ℝ, -realFiniteCellBox l r c d p z ∂(volume.prod volume)) -
        (∫ z : ℝ×ℝ, realFiniteCellBox l r c d p (Prod.swap z) ∂(volume.prod volume)) :=
      integral_sub hbox.neg hboxswap
    _ = -(∫ z : ℝ×ℝ, realFiniteCellBox l r c d p z ∂(volume.prod volume)) -
        (∫ z : ℝ×ℝ, realFiniteCellBox l r c d p z ∂(volume.prod volume)) := by
      rw [integral_neg, hsw]
    _ = -2 * (((d-l)^(p+2)-(d-r)^(p+2) -
        ((c-l)^(p+2)-(c-r)^(p+2))) / ((p+1)*(p+2))) := by
      rw [realFiniteCellBox_integral hlr hrc hcd hp]
      ring



private theorem cellCross_integrand_ae (a b h κ : ℝ) :
    (fun z : Eucl 1×Eucl 1 =>
      ((cellVec a h : Eucl 1 → ℝ) z.1 - (cellVec a h : Eucl 1 → ℝ) z.2) *
      ((cellVec b h : Eucl 1 → ℝ) z.1 - (cellVec b h : Eucl 1 → ℝ) z.2) *
        gagliardoKernel κ z.1 z.2) =ᵐ[volume.prod volume]
    (fun z => (h ^ (-(1/2:ℝ)))^2 *
      realCrossEnergy (a-h/2) (a+h/2) (b-h/2) (b+h/2) (-κ)
        (linePairEquiv z)) := by
  have ha := cellVec_line_rep a h
  have hb := cellVec_line_rep b h
  have hqf : Measure.QuasiMeasurePreserving Prod.fst
      (volume.prod volume) (volume : Measure (Eucl 1)) :=
    Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (Eucl 1))) (ν := (volume : Measure (Eucl 1)))
  have hqs : Measure.QuasiMeasurePreserving Prod.snd
      (volume.prod volume) (volume : Measure (Eucl 1)) :=
    Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Eucl 1))) (ν := (volume : Measure (Eucl 1)))
  have ha1 := hqf.ae_eq_comp ha
  have hb1 := hqf.ae_eq_comp hb
  have ha2 := hqs.ae_eq_comp ha
  have hb2 := hqs.ae_eq_comp hb
  filter_upwards [ha1,hb1,ha2,hb2] with z h1 h2 h3 h4
  have h1' :
      (cellVec a h : Eucl 1 → ℝ) z.1 =
        h ^ (-(1/2:ℝ)) *
          realCellFun (a-h/2) (a+h/2) (lineCoord z.1) := by simpa using h1
  have h2' :
      (cellVec b h : Eucl 1 → ℝ) z.1 =
        h ^ (-(1/2:ℝ)) *
          realCellFun (b-h/2) (b+h/2) (lineCoord z.1) := by simpa using h2
  have h3' :
      (cellVec a h : Eucl 1 → ℝ) z.2 =
        h ^ (-(1/2:ℝ)) *
          realCellFun (a-h/2) (a+h/2) (lineCoord z.2) := by simpa using h3
  have h4' :
      (cellVec b h : Eucl 1 → ℝ) z.2 =
        h ^ (-(1/2:ℝ)) *
          realCellFun (b-h/2) (b+h/2) (lineCoord z.2) := by simpa using h4
  simp only [gagliardoKernel]
  rw [h1',h2',h3',h4',lineCoord_norm_sub]
  change (h ^ (-(1/2:ℝ)) *
        realCellFun (a-h/2) (a+h/2) (lineCoord z.1) -
      h ^ (-(1/2:ℝ)) *
        realCellFun (a-h/2) (a+h/2) (lineCoord z.2)) *
      (h ^ (-(1/2:ℝ)) *
        realCellFun (b-h/2) (b+h/2) (lineCoord z.1) -
      h ^ (-(1/2:ℝ)) *
        realCellFun (b-h/2) (b+h/2) (lineCoord z.2)) *
      |lineCoord z.1-lineCoord z.2|^(-κ) =
    (h ^ (-(1/2:ℝ)))^2 *
      ((realCellFun (a-h/2) (a+h/2) (lineCoord z.1) -
        realCellFun (a-h/2) (a+h/2) (lineCoord z.2)) *
       (realCellFun (b-h/2) (b+h/2) (lineCoord z.1) -
        realCellFun (b-h/2) (b+h/2) (lineCoord z.2)) *
       |lineCoord z.1-lineCoord z.2|^(-κ))
  ring

private theorem cellCross_integral (a b h κ : ℝ) :
    ∫ z : Eucl 1×Eucl 1,
      ((cellVec a h : Eucl 1 → ℝ) z.1 - (cellVec a h : Eucl 1 → ℝ) z.2) *
      ((cellVec b h : Eucl 1 → ℝ) z.1 - (cellVec b h : Eucl 1 → ℝ) z.2) *
        gagliardoKernel κ z.1 z.2 ∂(volume.prod volume) =
      (h ^ (-(1/2:ℝ)))^2 *
        ∫ z : ℝ×ℝ,
          realCrossEnergy (a-h/2) (a+h/2) (b-h/2) (b+h/2) (-κ) z
            ∂(volume.prod volume) := by
  calc
    ∫ z : Eucl 1×Eucl 1,
      ((cellVec a h : Eucl 1 → ℝ) z.1 - (cellVec a h : Eucl 1 → ℝ) z.2) *
      ((cellVec b h : Eucl 1 → ℝ) z.1 - (cellVec b h : Eucl 1 → ℝ) z.2) *
        gagliardoKernel κ z.1 z.2 ∂(volume.prod volume) =
      ∫ z : Eucl 1×Eucl 1,
        (h ^ (-(1/2:ℝ)))^2 *
          realCrossEnergy (a-h/2) (a+h/2) (b-h/2) (b+h/2) (-κ)
            (linePairEquiv z) ∂(volume.prod volume) :=
        integral_congr_ae (cellCross_integrand_ae a b h κ)
    _ = ∫ z : ℝ×ℝ,
          (h ^ (-(1/2:ℝ)))^2 *
            realCrossEnergy (a-h/2) (a+h/2) (b-h/2) (b+h/2) (-κ) z
            ∂(volume.prod volume) := by
      change ∫ z : Eucl 1×Eucl 1,
        (fun w : ℝ×ℝ => (h ^ (-(1/2:ℝ)))^2 *
          realCrossEnergy (a-h/2) (a+h/2) (b-h/2) (b+h/2) (-κ) w)
            (linePairEquiv z) ∂(volume.prod volume) = _
      exact linePair_mp.integral_comp linePairEquiv.measurableEmbedding
        (fun w : ℝ×ℝ => (h ^ (-(1/2:ℝ)))^2 *
          realCrossEnergy (a-h/2) (a+h/2) (b-h/2) (b+h/2) (-κ) w)
    _ = (h ^ (-(1/2:ℝ)))^2 *
          ∫ z : ℝ×ℝ,
            realCrossEnergy (a-h/2) (a+h/2) (b-h/2) (b+h/2) (-κ) z
              ∂(volume.prod volume) := integral_const_mul _ _


private theorem realCrossEnergy_comm (l r c d p : ℝ) (z : ℝ×ℝ) :
    realCrossEnergy l r c d p z = realCrossEnergy c d l r p z := by
  unfold realCrossEnergy
  ring

private theorem realCross_cell_integral (a b h s : ℝ)
    (hs : 0 < s ∧ s < 1/2) (hh : 0 < h) (hab : h ≤ |a-b|) :
    ∫ z : ℝ×ℝ,
      realCrossEnergy (a-h/2) (a+h/2) (b-h/2) (b+h/2) (-(1+2*s)) z
        ∂(volume.prod volume) =
      -2 * ((2*|a-b|^(1-2*s) - (|a-b|+h)^(1-2*s) -
        (|a-b|-h)^(1-2*s))/(2*s*(1-2*s)) ) := by
  have hp : -2 < -(1+2*s) ∧ -(1+2*s) < -1 := by
    constructor <;> nlinarith [hs.1,hs.2]
  have hp1 : -(1+2*s)+1 = -2*s := by ring
  have hp2 : -(1+2*s)+2 = 1-2*s := by ring
  have hq : 0 < 1-2*s := by nlinarith [hs.2]
  have hs0 : 2*s ≠ 0 := ne_of_gt (mul_pos (by norm_num) hs.1)
  have hq0 : 1-2*s ≠ 0 := hq.ne'
  have habpos : 0 < |a-b| := lt_of_lt_of_le hh hab
  by_cases hab' : a ≤ b
  · have hababs : |a-b| = b-a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hab')]
      ring
    have hgap : a+h/2 ≤ b-h/2 := by rw [hababs] at hab; linarith
    have hlr : a-h/2 < a+h/2 := by linarith
    have hcd : b-h/2 < b+h/2 := by linarith
    have hdl : (b+h/2)-(a-h/2) = |a-b|+h := by rw [hababs]; ring
    have hdr : (b+h/2)-(a+h/2) = |a-b| := by rw [hababs]; ring
    have hcl : (b-h/2)-(a-h/2) = |a-b| := by rw [hababs]; ring
    have hcr : (b-h/2)-(a+h/2) = |a-b|-h := by rw [hababs]; ring
    rw [realCrossEnergy_integral hlr hgap hcd hp, hdl, hdr, hcl, hcr, hp1, hp2]
    field_simp [hs0,hq0]
    ring
  · have hba : b ≤ a := le_of_not_ge hab'
    have hababs : |a-b| = a-b := abs_of_nonneg (sub_nonneg.mpr hba)
    have hgap : b+h/2 ≤ a-h/2 := by rw [hababs] at hab; linarith
    have hlr : b-h/2 < b+h/2 := by linarith
    have hcd : a-h/2 < a+h/2 := by linarith
    have hdl : (a+h/2)-(b-h/2) = |a-b|+h := by rw [hababs]; ring
    have hdr : (a+h/2)-(b+h/2) = |a-b| := by rw [hababs]; ring
    have hcl : (a-h/2)-(b-h/2) = |a-b| := by rw [hababs]; ring
    have hcr : (a-h/2)-(b+h/2) = |a-b|-h := by rw [hababs]; ring
    have hcomm :
        ∫ z : ℝ×ℝ,
          realCrossEnergy (a-h/2) (a+h/2) (b-h/2) (b+h/2) (-(1+2*s)) z
            ∂(volume.prod volume) =
        ∫ z : ℝ×ℝ,
          realCrossEnergy (b-h/2) (b+h/2) (a-h/2) (a+h/2) (-(1+2*s)) z
            ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards with z
      exact realCrossEnergy_comm _ _ _ _ _ z
    rw [hcomm, realCrossEnergy_integral hlr hgap hcd hp,
      hdl, hdr, hcl, hcr, hp1, hp2]
    field_simp [hs0,hq0]
    ring

private theorem cellMatrix_offdiag_proof (c s : ℝ) (hs : 0 < s ∧ s < 1/2)
    (a b h : ℝ) (hh : 0 < h) (hab : h ≤ |a-b|) :
    formBilin c (1+2*s) (cellVec a h) (cellVec b h) =
      -(c/h) * ((2*|a-b|^(1-2*s) - (|a-b|+h)^(1-2*s) -
        (|a-b|-h)^(1-2*s))/(2*s*(1-2*s))) := by
  have htsq : (h ^ (-(1/2:ℝ)))^2 = h⁻¹ := by
    rw [pow_two, ← Real.rpow_add hh]
    norm_num [Real.rpow_neg_one]
  have hreal := realCross_cell_integral a b h s hs hh hab
  unfold formBilin
  rw [cellCross_integral a b h (1+2*s), hreal, htsq]
  field_simp [hh.ne']


/-- Cell indicators have finite form energy when `s < 1/2`. -/
theorem cellVec_mem_formDomain (s : ℝ) (hs : 0 < s ∧ s < 1 / 2) (a h : ℝ) (hh : 0 < h)
    (G : Set (Eucl 1)) (hG : lineCell a h ⊆ G) :
    cellVec a h ∈ formDomain (1 + 2 * s) G := by
  exact cellVec_domain_proof s hs a h hh G hG

/-- `B` is half the polar form of `Q_G` on the form domain. -/
theorem formBilin_eq_polar (c κ : ℝ) (G : Set (Eucl 1)) (u v : formDomain κ G) :
    formBilin c κ (u : L2 1) (v : L2 1) = QuadraticMap.polar (formQ c κ G) u v / 2 := by
  rw [formBilin, formQ_polar]
  ring

/-- Paper equation `eq:cell-diagonal`. -/
theorem cellMatrix_diag (c s : ℝ) (hs : 0 < s ∧ s < 1 / 2) (a h : ℝ) (hh : 0 < h) :
    formBilin c (1 + 2 * s) (cellVec a h) (cellVec a h) =
      c / h * (2 * h ^ (1 - 2 * s) / (2 * s * (1 - 2 * s))) := by
  exact cellMatrix_diag_proof c s hs a h hh

/-- Paper equation `eq:cell-offdiagonal`. -/
theorem cellMatrix_offdiag (c s : ℝ) (hs : 0 < s ∧ s < 1 / 2) (a b h : ℝ) (hh : 0 < h)
    (hab : h ≤ |a - b|) :
    formBilin c (1 + 2 * s) (cellVec a h) (cellVec b h) =
      -(c / h) * ((2 * |a - b| ^ (1 - 2 * s) - (|a - b| + h) ^ (1 - 2 * s) -
        (|a - b| - h) ^ (1 - 2 * s)) / (2 * s * (1 - 2 * s))) := by
  exact cellMatrix_offdiag_proof c s hs a b h hh hab

end Tunneling
