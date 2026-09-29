Status

- `tent_mem_formDomain` — proved.
- `exists_finrank_formDomain` — proved.
- Added private helpers: `tentKernel_integrable`, `bumpTent`, and `bumpTent_gagIntegrable`.
- Type-checked the complete file from stdin with Lean v4.33.0 and the project `LEAN_PATH`. The final check exited successfully with warnings only; there were no errors or `sorry` warnings. The original theorem statements and docstrings are preserved.

===BEGIN FILE Tunneling/Euclid/Bump.lean===
import Tunneling.Euclid.FormDomain
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Nontriviality of the form domain

An open nonempty set in `ℝ^d` (`d ≥ 1`) contains any finite number of
pairwise disjoint balls, and Lipschitz tent functions supported in these balls belong
to `H^s_0(G)` for `0 < s < 1`.  Hence the form domain has subspaces of every
finite dimension, so every Courant--Fischer level of `Q_G` is an infimum over a
nonempty family.
-/

namespace Tunneling

open MeasureTheory
open scoped InnerProductSpace

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
private theorem tentKernel_integrable (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (r : ℝ) (hr : 0 < r) :
    Integrable (fun z : Eucl d =>
      min (‖z‖ ^ 2) (r ^ 2) * ‖z‖ ^ (-((d : ℝ) + 2 * s))) volume := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let q : Eucl d → ℝ := fun z => min (‖z‖ ^ 2) (r ^ 2) * ‖z‖ ^ (-κ)
  have hdimR : (Module.finrank ℝ (Eucl d) : ℝ) = (d : ℝ) := by simp [Eucl]
  have hdimN : Module.finrank ℝ (Eucl d) = d := by exact_mod_cast hdimR
  have hdim : 1 ≤ Module.finrank ℝ (Eucl d) := by rw [hdimN]; exact hd
  have hκd : (Module.finrank ℝ (Eucl d) : ℝ) < κ := by
    rw [hdimR]
    dsimp [κ]
    linarith [hs.1]
  have hα : κ - 2 < Module.finrank ℝ (Eucl d) := by
    rw [hdimR]
    dsimp [κ]
    linarith [hs.2]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hκpos : 0 < κ := by dsimp [κ]; linarith [hdR, hs.1]
  have hq_nonneg (z : Eucl d) : 0 ≤ q z := by
    dsimp [q]
    exact mul_nonneg (le_min (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hq_meas : Measurable q := by
    dsimp [q]
    fun_prop
  have hdecay_point (z : Eucl d) :
      ‖q z‖ ≤ 1 * ‖z‖ ^ (-(κ - 2)) := by
    by_cases hz : ‖z‖ = 0
    · have hqz : q z = 0 := by
        dsimp [q]
        have hnormsq : ‖z‖ ^ 2 = 0 := by rw [hz]; norm_num
        rw [hnormsq, min_eq_left (sq_nonneg r)]
        simp
      simpa [hqz] using
        (mul_nonneg (by norm_num : 0 ≤ (1 : ℝ))
          (Real.rpow_nonneg (norm_nonneg z) (-(κ - 2))))
    · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      rw [Real.norm_eq_abs, abs_of_nonneg (hq_nonneg z)]
      calc
        min (‖z‖ ^ 2) (r ^ 2) * ‖z‖ ^ (-κ) ≤
            ‖z‖ ^ 2 * ‖z‖ ^ (-κ) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
        _ = ‖z‖ ^ (2 : ℝ) * ‖z‖ ^ (-κ) := by simp
        _ = ‖z‖ ^ ((2 : ℝ) + (-κ)) := (Real.rpow_add hzpos _ _).symm
        _ = 1 * ‖z‖ ^ (-(κ - 2)) := by congr 1 <;> ring_nf
  have hlocalOn : IntegrableOn q (Metric.ball (0 : Eucl d) 1) volume := by
    apply MeasureTheory.integrableOn_ball_of_norm_le_rpow hdim
    · exact hα
    · exact ae_of_all _ hdecay_point
    · exact hq_meas.aestronglyMeasurable
  have hlocal : Integrable ((Metric.ball (0 : Eucl d) 1).indicator q) volume :=
    hlocalOn.integrable_indicator measurableSet_ball
  let C : ℝ := r ^ 2 * 2 ^ κ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase : Integrable (fun z : Eucl d => (1 + ‖z‖) ^ (-κ)) volume :=
    integrable_one_add_norm hκd
  have htail : Integrable ((Metric.ball (0 : Eucl d) 1)ᶜ.indicator q) volume := by
    apply (hbase.const_mul C).mono'
    · exact (hq_meas.indicator measurableSet_ball.compl).aestronglyMeasurable
    · filter_upwards [] with z
      by_cases hz : z ∈ Metric.ball (0 : Eucl d) 1
      · have hbr : 0 ≤ (1 + ‖z‖) ^ (-κ) :=
          Real.rpow_nonneg (add_nonneg (by norm_num) (norm_nonneg z)) _
        simpa [hz] using mul_nonneg hC hbr
      · have hn : 1 ≤ ‖z‖ := by
          have hnot : ¬ ‖z‖ < 1 := by
            simpa [Metric.mem_ball, dist_zero_right] using hz
          exact le_of_not_gt hnot
        have hnormpos : 0 < ‖z‖ := by linarith [norm_nonneg z, hn]
        have hpow : ‖z‖ ^ (-κ) ≤ 2 ^ κ * (1 + ‖z‖) ^ (-κ) := by
          calc
            ‖z‖ ^ (-κ) ≤ ((1 + ‖z‖) / 2) ^ (-κ) :=
              Real.rpow_le_rpow_of_nonpos
                (div_pos (by linarith [norm_nonneg z]) (by norm_num))
                (by nlinarith [hn]) (by linarith [hκpos])
            _ = (1 + ‖z‖) ^ (-κ) / (2 : ℝ) ^ (-κ) := by
              rw [Real.div_rpow (by positivity) (by norm_num)]
            _ = 2 ^ κ * (1 + ‖z‖) ^ (-κ) := by
              rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) κ]
              simp [div_eq_mul_inv, mul_comm]
        have hqle : q z ≤ C * (1 + ‖z‖) ^ (-κ) := by
          calc
            q z ≤ r ^ 2 * ‖z‖ ^ (-κ) := by
              dsimp [q]
              exact mul_le_mul_of_nonneg_right (min_le_right _ _)
                (Real.rpow_nonneg (norm_nonneg _) _)
            _ ≤ r ^ 2 * (2 ^ κ * (1 + ‖z‖) ^ (-κ)) :=
              mul_le_mul_of_nonneg_left hpow (sq_nonneg r)
            _ = C * (1 + ‖z‖) ^ (-κ) := by dsimp [C]; ring
        have hb : ((Metric.ball (0 : Eucl d) 1)ᶜ.indicator q) z = q z := by
          simp [hz]
        rw [hb, Real.norm_eq_abs, abs_of_nonneg (hq_nonneg z)]
        exact hqle
  have hsplit : q =ᵐ[volume] (fun z =>
      (Metric.ball (0 : Eucl d) 1).indicator q z +
        (Metric.ball (0 : Eucl d) 1)ᶜ.indicator q z) := by
    filter_upwards [] with z
    by_cases hz : z ∈ Metric.ball (0 : Eucl d) 1 <;> simp [hz]
  have hqint : Integrable q volume := (hlocal.add htail).congr hsplit.symm
  simpa [q, κ] using hqint

private noncomputable def bumpTent (x₀ : Eucl d) (r : ℝ) : Eucl d → ℝ :=
  fun x => max 0 (r - ‖x - x₀‖)

set_option maxHeartbeats 1000000 in
private theorem bumpTent_gagIntegrable (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (x₀ : Eucl d) (r : ℝ) (hr : 0 < r) :
    Integrable
      (fun z : Eucl d × Eucl d =>
        gagliardoIntegrand ((d : ℝ) + 2 * s) (bumpTent x₀ r) z)
      (volume.prod volume) := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let g := bumpTent x₀ r
  let K := Metric.closedBall x₀ r
  let q : Eucl d → ℝ := fun z => min (‖z‖ ^ 2) (r ^ 2) * ‖z‖ ^ (-κ)
  let w : Eucl d → ℝ := K.indicator (fun _ => (1 : ℝ))
  have hq : Integrable q volume := by
    simpa [q, κ] using tentKernel_integrable hd s hs r hr
  have hqnonneg (z : Eucl d) : 0 ≤ q z := by
    dsimp [q]
    exact mul_nonneg (le_min (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hqmeas : Measurable q := by dsimp [q]; fun_prop
  have hw : Integrable w volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (isCompact_closedBall x₀ r).measure_lt_top.ne
  have hfirst : Integrable
      (fun z : Eucl d × Eucl d => q (z.2 - z.1) * w z.1) (volume.prod volume) := by
    have hp := hw.mul_prod hq
    have hcomp := (measurePreserving_prod_sub (volume : Measure (Eucl d))
      (volume : Measure (Eucl d))).integrable_comp_of_integrable hp
    exact hcomp.congr (ae_of_all _ (fun z => by simp [q, norm_sub_rev, mul_comm]))
  have hsecond : Integrable
      (fun z : Eucl d × Eucl d => q (z.1 - z.2) * w z.2) (volume.prod volume) := by
    have hp := hq.mul_prod hw
    have hcomp := (measurePreserving_sub_prod (volume : Measure (Eucl d))
      (volume : Measure (Eucl d))).integrable_comp_of_integrable hp
    exact hcomp.congr (ae_of_all _ (fun z => by simp [q]))
  have hupper : Integrable
      (fun z : Eucl d × Eucl d => q (z.1 - z.2) * (w z.1 + w z.2))
      (volume.prod volume) := by
    have hfirst' : Integrable
        (fun z : Eucl d × Eucl d => q (z.1 - z.2) * w z.1)
        (volume.prod volume) := by
      exact hfirst.congr (ae_of_all _ (fun z => by simp [q, norm_sub_rev]))
    have hsecond' : Integrable
        (fun z : Eucl d × Eucl d => q (z.1 - z.2) * w z.2)
        (volume.prod volume) := hsecond
    have heq : (fun z : Eucl d × Eucl d => q (z.1 - z.2) * (w z.1 + w z.2)) =
        (fun z => q (z.1 - z.2) * w z.1) + (fun z => q (z.1 - z.2) * w z.2) := by
      funext z
      change q (z.1 - z.2) * (w z.1 + w z.2) =
        q (z.1 - z.2) * w z.1 + q (z.1 - z.2) * w z.2
      ring
    rw [heq]
    exact hfirst'.add hsecond'
  have hgcont : Continuous g := by
    dsimp [g, bumpTent]
    exact continuous_const.max
      (continuous_const.sub (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hgcompact : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall x₀ r)
    intro x hx
    have hx' : r < dist x x₀ := by
      have hxnot : ¬ dist x x₀ ≤ r := by simpa [Metric.mem_closedBall] using hx
      exact lt_of_not_ge hxnot
    have hxnorm : r < ‖x - x₀‖ := by simpa [dist_eq_norm] using hx'
    dsimp [g, bumpTent]
    rw [max_eq_left (sub_nonpos.mpr (le_of_lt hxnorm))]
  have hgLip (x y : Eucl d) : |g x - g y| ≤ dist x y := by
    dsimp [g, bumpTent]
    calc
      |max 0 (r - ‖x - x₀‖) - max 0 (r - ‖y - x₀‖)| =
          |max (r - ‖x - x₀‖) 0 - max (r - ‖y - x₀‖) 0| := by
        rw [max_comm 0 (r - ‖x - x₀‖), max_comm 0 (r - ‖y - x₀‖)]
      _ ≤ |(r - ‖x - x₀‖) - (r - ‖y - x₀‖)| :=
        abs_max_sub_max_le_abs _ _ _
      _ = |‖y - x₀‖ - ‖x - x₀‖| := by congr 1 <;> ring_nf
      _ = |‖x - x₀‖ - ‖y - x₀‖| := abs_sub_comm _ _
      _ ≤ ‖(x - x₀) - (y - x₀)‖ := abs_norm_sub_norm_le _ _
      _ = dist x y := by rw [dist_eq_norm]; congr 1 <;> abel
  have hgBound (x : Eucl d) : 0 ≤ g x ∧ g x ≤ r := by
    constructor
    · dsimp [g, bumpTent]
      exact le_max_left _ _
    · dsimp [g, bumpTent]
      exact max_le hr.le (sub_le_self r (norm_nonneg _))
  have hw_nonneg (x : Eucl d) : 0 ≤ w x := by
    by_cases hx : x ∈ K <;> simp [w, K, hx]
  have hpoint (x y : Eucl d) :
      gagliardoIntegrand κ g (x, y) ≤ q (x - y) * (w x + w y) := by
    have hdiffSq : (g x - g y) ^ 2 ≤ min (dist x y ^ 2) (r ^ 2) := by
      have h1 := hgLip x y
      have h2 : |g x - g y| ≤ r := by
        rcases hgBound x with ⟨h0x, hrx⟩
        rcases hgBound y with ⟨h0y, hry⟩
        rw [abs_le]
        constructor <;> linarith
      have h1sq : (g x - g y) ^ 2 ≤ dist x y ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (dist_nonneg)).2 h1
      have h2sq : (g x - g y) ^ 2 ≤ r ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hr.le).2 h2
      exact le_min h1sq h2sq
    have hdiffSqNorm : (g x - g y) ^ 2 ≤ min (‖x - y‖ ^ 2) (r ^ 2) := by
      simpa [dist_eq_norm] using hdiffSq
    have hbase : gagliardoIntegrand κ g (x, y) ≤ q (x - y) := by
      rw [gagliardoIntegrand, gagliardoKernel]
      dsimp [q]
      exact mul_le_mul_of_nonneg_right hdiffSqNorm
        (Real.rpow_nonneg (norm_nonneg _) _)
    by_cases hx : x ∈ K
    · have hwx : w x = 1 := by simp [w, K, hx]
      have hwy : 0 ≤ w y := hw_nonneg y
      calc
        gagliardoIntegrand κ g (x, y) ≤ q (x - y) := hbase
        _ ≤ q (x - y) * (w x + w y) := by
          rw [hwx]
          nlinarith [mul_nonneg (hqnonneg (x - y)) hwy]
    · by_cases hy : y ∈ K
      · have hwx : w x = 0 := by simp [w, K, hx]
        have hwy : w y = 1 := by simp [w, K, hy]
        simpa [hwx, hwy] using hbase
      · have hwx : w x = 0 := by simp [w, K, hx]
        have hwy : w y = 0 := by simp [w, K, hy]
        have hgx : g x = 0 := by
          have hx' : r ≤ dist x x₀ := by
            have hnot : ¬ dist x x₀ ≤ r := by
              simpa [K, Metric.mem_closedBall] using hx
            exact le_of_lt (lt_of_not_ge hnot)
          have hxnorm : r ≤ ‖x - x₀‖ := by simpa [dist_eq_norm] using hx'
          dsimp [g, bumpTent]
          rw [max_eq_left (sub_nonpos.mpr hxnorm)]
        have hgy : g y = 0 := by
          have hy' : r ≤ dist y x₀ := by
            have hnot : ¬ dist y x₀ ≤ r := by
              simpa [K, Metric.mem_closedBall] using hy
            exact le_of_lt (lt_of_not_ge hnot)
          have hynorm : r ≤ ‖y - x₀‖ := by simpa [dist_eq_norm] using hy'
          dsimp [g, bumpTent]
          rw [max_eq_left (sub_nonpos.mpr hynorm)]
        simp [gagliardoIntegrand, hgx, hgy, hwx, hwy]
  have hupper_nonneg (z : Eucl d × Eucl d) :
      0 ≤ q (z.1 - z.2) * (w z.1 + w z.2) :=
    mul_nonneg (hqnonneg _) (add_nonneg (hw_nonneg _) (hw_nonneg _))
  have hmeas : AEStronglyMeasurable
      (fun z : Eucl d × Eucl d => gagliardoIntegrand κ g z) (volume.prod volume) :=
    gagliardoIntegrand_aestronglyMeasurable κ volume
      (gagliardoKernel_aestronglyMeasurable κ volume) hgcont.measurable.aestronglyMeasurable
  have hpointNorm (z : Eucl d × Eucl d) :
      ‖gagliardoIntegrand ((d : ℝ) + 2 * s) (bumpTent x₀ r) z‖ ≤
        q (z.1 - z.2) * (w z.1 + w z.2) := by
    change ‖gagliardoIntegrand κ g z‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (gagliardoIntegrand_nonneg κ g z)]
    exact hpoint z.1 z.2
  exact hupper.mono' hmeas (ae_of_all _ hpointNorm)

/-- A Lipschitz tent function supported in a ball has finite Gagliardo
energy for `0 < s < 1`: the local singularity is integrable because `s < 1`
and the tail because `s > 0`. -/
theorem tent_mem_formDomain (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (x₀ : Eucl d) (r : ℝ) (hr : 0 < r) :
    ∃ f : L2 d, f ∈ formDomain ((d : ℝ) + 2 * s) (Metric.ball x₀ r) ∧ f ≠ 0 := by
  let g := bumpTent x₀ r
  have hgcont : Continuous g := by
    dsimp [g, bumpTent]
    exact continuous_const.max
      (continuous_const.sub (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hgcompact : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall x₀ r)
    intro x hx
    have hx' : r < dist x x₀ := by
      have hxnot : ¬ dist x x₀ ≤ r := by simpa [Metric.mem_closedBall] using hx
      exact lt_of_not_ge hxnot
    have hxnorm : r < ‖x - x₀‖ := by simpa [dist_eq_norm] using hx'
    dsimp [g, bumpTent]
    rw [max_eq_left (sub_nonpos.mpr (le_of_lt hxnorm))]
  have hmemlp : MemLp g 2 (volume : Measure (Eucl d)) :=
    hgcont.memLp_of_hasCompactSupport hgcompact
  let f : L2 d := hmemlp.toLp g
  have hfae : (f : Eucl d → ℝ) =ᵐ[volume] g := hmemlp.coeFn_toLp
  have hvanish : ∀ᵐ x ∂(volume : Measure (Eucl d)),
      x ∉ Metric.ball x₀ r → f x = 0 := by
    filter_upwards [hfae] with x hx
    intro hxball
    have hdist : r ≤ dist x x₀ := le_of_not_gt (by
      simpa [Metric.mem_ball] using hxball)
    have hdistnorm : r ≤ ‖x - x₀‖ := by simpa [dist_eq_norm] using hdist
    have hgzero : g x = 0 := by
      dsimp [g, bumpTent]
      rw [max_eq_left (sub_nonpos.mpr hdistnorm)]
    rw [hx, hgzero]
  have henergy : Integrable
      (fun z : Eucl d × Eucl d =>
        gagliardoIntegrand ((d : ℝ) + 2 * s) (f : Eucl d → ℝ) z)
      (volume.prod volume) := by
    have hcont := bumpTent_gagIntegrable hd s hs x₀ r hr
    have hcongr : (fun z : Eucl d × Eucl d =>
        gagliardoIntegrand ((d : ℝ) + 2 * s) (f : Eucl d → ℝ) z) =ᵐ[volume.prod volume]
      (fun z => gagliardoIntegrand ((d : ℝ) + 2 * s) g z) := by
      have hfst : (fun z : Eucl d × Eucl d => (f : Eucl d → ℝ) z.1) =ᵐ[volume.prod volume]
          (fun z => g z.1) :=
        (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Eucl d)))
          (ν := (volume : Measure (Eucl d)))).ae_eq_comp hfae
      have hsnd : (fun z : Eucl d × Eucl d => (f : Eucl d → ℝ) z.2) =ᵐ[volume.prod volume]
          (fun z => g z.2) :=
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Eucl d)))
          (ν := (volume : Measure (Eucl d)))).ae_eq_comp hfae
      filter_upwards [hfst, hsnd] with z h1 h2
      simp [gagliardoIntegrand, h1, h2]
    exact hcont.congr hcongr.symm
  have hmem : f ∈ formDomain ((d : ℝ) + 2 * s) (Metric.ball x₀ r) := by
    apply (mem_formDomain_iff _ _ _).2
    exact ⟨hvanish, henergy⟩
  have hnonzero : f ≠ 0 := by
    intro hf
    have hzero : g =ᵐ[volume] (0 : Eucl d → ℝ) := by
      have h0 : (f : Eucl d → ℝ) =ᵐ[volume] (0 : Eucl d → ℝ) := by
        simpa only [hf] using (Lp.coeFn_zero ℝ 2 (volume : Measure (Eucl d)))
      exact hfae.symm.trans h0
    have hpos : ∀ x ∈ Metric.ball x₀ (r / 2), 0 < g x := by
      intro x hx
      have hdist : dist x x₀ < r / 2 := by simpa [Metric.mem_ball] using hx
      have hdistnorm : ‖x - x₀‖ < r / 2 := by simpa [dist_eq_norm] using hdist
      dsimp [g, bumpTent]
      apply lt_of_lt_of_le ?_ (le_max_right _ _)
      exact sub_pos.mpr (by linarith)
    have hballAE : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ Metric.ball x₀ (r / 2) := by
      filter_upwards [hzero] with x hx
      intro hxball
      exact (ne_of_gt (hpos x hxball)) hx
    have hballNull : volume (Metric.ball x₀ (r / 2)) = 0 := by
      simpa [Metric.ball] using (ae_iff.mp hballAE)
    have hballpos : 0 < volume (Metric.ball x₀ (r / 2)) :=
      Metric.measure_ball_pos volume x₀ (by positivity)
    exact (ne_of_gt hballpos) hballNull
  exact ⟨f, hmem, hnonzero⟩

/-- The form domain of an open nonempty set has subspaces of every finite
dimension. -/
theorem exists_finrank_formDomain (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (G : Set (Eucl d)) (hG : IsOpen G) (hne : G.Nonempty) (n : ℕ) :
    ∃ W : Submodule ℝ (formDomain ((d : ℝ) + 2 * s) G), Module.finrank ℝ W = n := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨⊥, by simp⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨ρ, hρpos, hρsub⟩ := (Metric.isOpen_iff.mp hG) x₀ hx₀
    let δ : ℝ := ρ / (2 * n)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have htwo : (0 : ℝ) < 2 := by norm_num
    have hdelta_eq : 2 * (n : ℝ) * δ = ρ := by
      dsimp [δ]
      field_simp [ne_of_gt (mul_pos htwo hnR)]
    have hdpos : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_one hd
    let i₀ : Fin d := ⟨0, hdpos⟩
    let e : Eucl d := EuclideanSpace.single i₀ 1
    have he : ‖e‖ = 1 := by simp [e]
    let a : Fin n → ℝ := fun j => 2 * (j.val : ℝ) * δ
    let c : Fin n → Eucl d := fun j => x₀ + a j • e
    have ha_nonneg (j : Fin n) : 0 ≤ a j := by dsimp [a]; positivity
    have hcenterSub (j : Fin n) : c j - x₀ = a j • e := by
      dsimp [c]
      abel
    have hcenterDist (j : Fin n) : dist (c j) x₀ = a j := by
      rw [dist_eq_norm, hcenterSub, norm_smul, he]
      simp [Real.norm_eq_abs, abs_of_nonneg (ha_nonneg j)]
    have hcenterDiff (i j : Fin n) : c i - c j = (a i - a j) • e := by
      dsimp [c]
      calc
        _ = a i • e - a j • e := by abel
        _ = (a i - a j) • e := by rw [sub_smul]
    have hdistCenter (i j : Fin n) : dist (c i) (c j) = |a i - a j| := by
      rw [dist_eq_norm, hcenterDiff, norm_smul, he]
      simp [Real.norm_eq_abs]
    have hgap (i j : Fin n) (hij : i ≠ j) :
        (1 : ℝ) ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
      have hval : i.val ≠ j.val := by
        intro heq
        exact hij (Fin.ext heq)
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · have hnat : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hlt
        have hcast : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hnat
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hnat : j.val + 1 ≤ i.val := Nat.succ_le_iff.mpr hgt
        have hcast : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hnat
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hsep (i j : Fin n) (hij : i ≠ j) :
        2 * δ ≤ dist (c i) (c j) := by
      rw [hdistCenter]
      have hfac : a i - a j =
          2 * δ * ((i.val : ℝ) - (j.val : ℝ)) := by dsimp [a]; ring
      have hcoeff : 0 ≤ 2 * δ := mul_nonneg (by norm_num) hδ.le
      calc
        2 * δ ≤ 2 * δ * |(i.val : ℝ) - (j.val : ℝ)| := by
          nlinarith [hgap i j hij]
        _ = |2 * δ * ((i.val : ℝ) - (j.val : ℝ))| := by
          rw [abs_mul, abs_of_nonneg hcoeff]
        _ = |a i - a j| := by rw [hfac]
    have hcenterBound (j : Fin n) : a j + δ ≤ ρ := by
      have hjNat : j.val + 1 ≤ n := Nat.succ_le_iff.mpr j.isLt
      have hjCast : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjNat
      have hremain : 0 ≤ ((n : ℝ) - (j.val : ℝ) - 1) * δ :=
        mul_nonneg (by linarith [hjCast]) hδ.le
      dsimp [a]
      nlinarith [hdelta_eq, hremain]
    have hballG (j : Fin n) : Metric.ball (c j) δ ⊆ G := by
      intro x hx
      have htriangle : dist x x₀ ≤ dist x (c j) + dist (c j) x₀ := dist_triangle _ _ _
      have hdistx : dist x (c j) < δ := by
        simpa [dist_comm] using Metric.mem_ball.mp hx
      apply hρsub
      rw [Metric.mem_ball]
      calc
        dist x x₀ ≤ dist x (c j) + dist (c j) x₀ := htriangle
        _ < δ + a j := by rw [hcenterDist]; linarith
        _ ≤ ρ := by linarith [hcenterBound j]
    have htent : ∀ j : Fin n, ∃ f : L2 d,
        f ∈ formDomain ((d : ℝ) + 2 * s) (Metric.ball (c j) δ) ∧
        f ≠ 0 ∧ f ∈ formDomain ((d : ℝ) + 2 * s) G := by
      intro j
      obtain ⟨f, hf, hfnz⟩ := tent_mem_formDomain hd s hs (c j) δ hδ
      have hfG : f ∈ formDomain ((d : ℝ) + 2 * s) G := by
        apply (mem_formDomain_iff _ _ _).2
        rcases (mem_formDomain_iff _ _ _).mp hf with ⟨hoff, henergy⟩
        refine ⟨?_, henergy⟩
        filter_upwards [hoff] with x hx
        intro hxG
        apply hx
        intro hxball
        exact hxG (hballG j hxball)
      exact ⟨f, hf, hfnz, hfG⟩
    choose f hsmall hfNe hfG using htent
    let v : Fin n → formDomain ((d : ℝ) + 2 * s) G := fun j => ⟨f j, hfG j⟩
    have hvanish (j : Fin n) :
        ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ Metric.ball (c j) δ → f j x = 0 :=
      ((mem_formDomain_iff _ _ _).mp (hsmall j)).1
    have hdisj (i j : Fin n) (hij : i ≠ j) :
        Disjoint (Metric.ball (c i) δ) (Metric.ball (c j) δ) := by
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      have hci : dist (c i) (c j) ≤ dist (c i) x + dist x (c j) :=
        dist_triangle _ _ _
      have hi' : dist (c i) x < δ := by
        simpa [dist_comm] using Metric.mem_ball.mp hxi
      have hj' : dist x (c j) < δ := Metric.mem_ball.mp hxj
      have hlt : dist (c i) (c j) < 2 * δ := by linarith
      exact (not_lt_of_ge (hsep i j hij)) hlt
    have horthProd (i j : Fin n) (hij : i ≠ j) :
        (fun x : Eucl d => f i x * f j x) =ᵐ[volume] (fun _ => 0) := by
      filter_upwards [hvanish i, hvanish j] with x hi hj
      by_cases hxi : x ∈ Metric.ball (c i) δ
      · have hxj : x ∉ Metric.ball (c j) δ := by
          intro hxj
          exact Set.disjoint_left.mp (hdisj i j hij) hxi hxj
        rw [hj hxj]
        simp
      · rw [hi hxi]
        simp
    have horth : Pairwise (fun i j : Fin n => inner ℝ (v i) (v j) = 0) := by
      intro i j hij
      change inner ℝ (f i) (f j) = 0
      rw [L2.inner_def]
      have hae : (fun x : Eucl d => inner ℝ (f i x) (f j x)) =ᵐ[volume] (fun _ => 0) := by
        filter_upwards [horthProd i j hij] with x hx
        rw [Real.inner_apply]
        exact hx
      rw [integral_congr_ae hae]
      simp
    have hli : LinearIndependent ℝ v := by
      apply linearIndependent_of_ne_zero_of_inner_eq_zero
      · intro j hj
        apply hfNe j
        have hv := congrArg Subtype.val hj
        simpa [v] using hv
      · exact horth
    refine ⟨Submodule.span ℝ (Set.range v), ?_⟩
    rw [finrank_span_eq_card hli]
    simp

end Tunneling
===END FILE===