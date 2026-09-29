import Tunneling.Euclid.FormDomain

/-!
# Absolute values and the sign of minimizers

For real `a, b`,
`|a - b|² - ||a| - |b||² = 2 (|a| |b| - a b) = 4 (a⁺ b⁻ + a⁻ b⁺)`.
Hence `[|u|] ≤ [u]`, and equality forces `u⁺(x) u⁻(y) = 0` for a.e.
`(x, y)`, because the Gagliardo kernel is positive off the diagonal.  By
Tonelli this means that `u⁺ = 0` a.e. or `u⁻ = 0` a.e.  This is the linear case
of the ground-state argument cited from [BrascoParini2016, Theorem 2.8].
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- The absolute value `|f|` of an `L²` function. -/
noncomputable def absL2 (f : L2 d) : L2 d :=
  (Lp.memLp f).norm.toLp (fun x => ‖(f : Eucl d → ℝ) x‖)

theorem absL2_ae (f : L2 d) :
    ((absL2 f : L2 d) : Eucl d → ℝ) =ᵐ[volume] fun x => |f x| := by
  unfold absL2
  filter_upwards [(Lp.memLp f).norm.coeFn_toLp] with x hx
  simpa only [Real.norm_eq_abs] using hx

theorem norm_absL2 (f : L2 d) : ‖absL2 f‖ = ‖f‖ := by
  unfold absL2
  rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_norm]

theorem absL2_nonneg (f : L2 d) : 0 ≤ᵐ[volume] ((absL2 f : L2 d) : Eucl d → ℝ) := by
  filter_upwards [absL2_ae f] with x hx
  rw [hx]
  exact abs_nonneg (f x)

private theorem gagliardoIntegrand_absL2_le_ae (κ : ℝ) (f : L2 d) :
    (fun z : Eucl d × Eucl d =>
      gagliardoIntegrand κ ((absL2 f : L2 d) : Eucl d → ℝ) z) ≤ᵐ[volume.prod volume]
    (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f : Eucl d → ℝ) z) := by
  have hfst : (fun z : Eucl d × Eucl d => ((absL2 f : L2 d) : Eucl d → ℝ) z.1) =ᵐ[volume.prod volume]
      (fun z => |(f : Eucl d → ℝ) z.1|) :=
    ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Eucl d)))
      (ν := (volume : Measure (Eucl d)))).ae_eq_comp (absL2_ae f))
  have hsnd : (fun z : Eucl d × Eucl d => ((absL2 f : L2 d) : Eucl d → ℝ) z.2) =ᵐ[volume.prod volume]
      (fun z => |(f : Eucl d → ℝ) z.2|) :=
    ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Eucl d)))
      (ν := (volume : Measure (Eucl d)))).ae_eq_comp (absL2_ae f))
  filter_upwards [hfst, hsnd] with z hz₁ hz₂
  rcases z with ⟨x, y⟩
  simp only at hz₁ hz₂
  simp only [gagliardoIntegrand, gagliardoKernel]
  rw [hz₁, hz₂]
  have hk : 0 ≤ ‖x - y‖ ^ (-κ) := Real.rpow_nonneg (norm_nonneg _) _
  apply mul_le_mul_of_nonneg_right _ hk
  have hdiff : |(|(f : Eucl d → ℝ) x| - |(f : Eucl d → ℝ) y|)| ≤
      |(f : Eucl d → ℝ) x - (f : Eucl d → ℝ) y| := by
    simpa only [Real.norm_eq_abs] using
      (abs_norm_sub_norm_le ((f : Eucl d → ℝ) x) ((f : Eucl d → ℝ) y))
  exact (sq_le_sq).2 hdiff

theorem absL2_mem_formDomain (κ : ℝ) (G : Set (Eucl d)) {f : L2 d}
    (hf : f ∈ formDomain κ G) : absL2 f ∈ formDomain κ G := by
  have hf' := (mem_formDomain_iff κ G f).mp hf
  apply (mem_formDomain_iff κ G (absL2 f)).2
  constructor
  · filter_upwards [hf'.1, absL2_ae f] with x hx hxe
    intro hnot
    rw [hxe]
    simpa using congrArg abs (hx hnot)
  · have hK := gagliardoKernel_aestronglyMeasurable κ (volume : Measure (Eucl d))
    have hmeas := gagliardoIntegrand_aestronglyMeasurable κ (volume : Measure (Eucl d)) hK
      (Lp.aestronglyMeasurable (absL2 f))
    exact hf'.2.mono_nonneg hmeas
      (MeasureTheory.ae_of_all _ (fun z => gagliardoIntegrand_nonneg κ _ z))
      (gagliardoIntegrand_absL2_le_ae κ f)

theorem gagliardoSeminormSq_absL2_le (κ : ℝ) (G : Set (Eucl d)) {f : L2 d}
    (hf : f ∈ formDomain κ G) :
    gagliardoSeminormSq κ (volume : Measure (Eucl d)) ((absL2 f : L2 d) : Eucl d → ℝ) ≤
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ) := by
  have hf' := (mem_formDomain_iff κ G f).mp hf
  have hfa : absL2 f ∈ formDomain κ G := absL2_mem_formDomain κ G hf
  have hfa' := (mem_formDomain_iff κ G (absL2 f)).mp hfa
  exact integral_mono_ae hfa'.2 hf'.2 (gagliardoIntegrand_absL2_le_ae κ f)

/-- Equality of the energies of `u` and `|u|` forces a constant sign. -/
theorem ae_nonneg_or_nonpos_of_gagliardoSeminormSq_absL2_eq (hd : 1 ≤ d) (κ : ℝ)
    (G : Set (Eucl d)) {f : L2 d} (hf : f ∈ formDomain κ G)
    (heq : gagliardoSeminormSq κ (volume : Measure (Eucl d))
        ((absL2 f : L2 d) : Eucl d → ℝ) =
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ)) :
    (0 ≤ᵐ[volume] (f : Eucl d → ℝ)) ∨ ((f : Eucl d → ℝ) ≤ᵐ[volume] 0) := by
  have hf' := (mem_formDomain_iff κ G f).mp hf
  have hfa : absL2 f ∈ formDomain κ G := absL2_mem_formDomain κ G hf
  have hfa' := (mem_formDomain_iff κ G (absL2 f)).mp hfa
  have hle := gagliardoIntegrand_absL2_le_ae κ f
  have hnonneg : 0 ≤ᵐ[volume.prod volume]
      (fun z : Eucl d × Eucl d =>
        gagliardoIntegrand κ (f : Eucl d → ℝ) z -
          gagliardoIntegrand κ ((absL2 f : L2 d) : Eucl d → ℝ) z) := by
    filter_upwards [hle] with z hz
    exact sub_nonneg.mpr hz
  have hdiffInt : Integrable
      (fun z : Eucl d × Eucl d =>
        gagliardoIntegrand κ (f : Eucl d → ℝ) z -
          gagliardoIntegrand κ ((absL2 f : L2 d) : Eucl d → ℝ) z)
      (volume.prod volume) := hf'.2.sub hfa'.2
  have hdiffZero : ∫ z : Eucl d × Eucl d,
      gagliardoIntegrand κ (f : Eucl d → ℝ) z -
        gagliardoIntegrand κ ((absL2 f : L2 d) : Eucl d → ℝ) z ∂(volume.prod volume) = 0 := by
    rw [integral_sub hf'.2 hfa'.2]
    change gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ) -
      gagliardoSeminormSq κ (volume : Measure (Eucl d))
        ((absL2 f : L2 d) : Eucl d → ℝ) = 0
    linarith
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hdiffInt).mp hdiffZero
  have hfst : (fun z : Eucl d × Eucl d => ((absL2 f : L2 d) : Eucl d → ℝ) z.1) =ᵐ[volume.prod volume]
      (fun z => |(f : Eucl d → ℝ) z.1|) :=
    ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Eucl d)))
      (ν := (volume : Measure (Eucl d)))).ae_eq_comp (absL2_ae f))
  have hsnd : (fun z : Eucl d × Eucl d => ((absL2 f : L2 d) : Eucl d → ℝ) z.2) =ᵐ[volume.prod volume]
      (fun z => |(f : Eucl d → ℝ) z.2|) :=
    ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Eucl d)))
      (ν := (volume : Measure (Eucl d)))).ae_eq_comp (absL2_ae f))
  have hpair : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
      0 ≤ (f : Eucl d → ℝ) z.1 * (f : Eucl d → ℝ) z.2 := by
    filter_upwards [hzero, hfst, hsnd] with z hz hz₁ hz₂
    rcases z with ⟨x, y⟩
    by_cases hxy : x = y
    · subst y
      exact mul_self_nonneg _
    · have hk : 0 < ‖x - y‖ ^ (-κ) :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
      have hid : ((f : Eucl d → ℝ) x - (f : Eucl d → ℝ) y) ^ 2 -
          (|(f : Eucl d → ℝ) x| - |(f : Eucl d → ℝ) y|) ^ 2 =
            2 * (|(f : Eucl d → ℝ) x| * |(f : Eucl d → ℝ) y| -
              (f : Eucl d → ℝ) x * (f : Eucl d → ℝ) y) := by
        linear_combination -sq_abs ((f : Eucl d → ℝ) x) - sq_abs ((f : Eucl d → ℝ) y)
      have hfac : 2 * (|(f : Eucl d → ℝ) x| * |(f : Eucl d → ℝ) y| -
          (f : Eucl d → ℝ) x * (f : Eucl d → ℝ) y) * (‖x - y‖ ^ (-κ)) = 0 := by
        dsimp [gagliardoIntegrand, gagliardoKernel] at hz
        rw [hz₁, hz₂] at hz
        rw [← sub_mul, hid] at hz
        exact hz
      have habsprod : 0 ≤ |(f : Eucl d → ℝ) x| * |(f : Eucl d → ℝ) y| -
          (f : Eucl d → ℝ) x * (f : Eucl d → ℝ) y := by
        rw [← abs_mul]
        exact sub_nonneg.mpr (le_abs_self _)
      rcases mul_eq_zero.mp hfac with hleft | hker
      · have hex : |(f : Eucl d → ℝ) x| * |(f : Eucl d → ℝ) y| -
            (f : Eucl d → ℝ) x * (f : Eucl d → ℝ) y = 0 := by
          exact (mul_eq_zero.mp hleft).resolve_left (by norm_num)
        have hprod : (f : Eucl d → ℝ) x * (f : Eucl d → ℝ) y =
            |(f : Eucl d → ℝ) x| * |(f : Eucl d → ℝ) y| := by linarith
        rw [hprod]
        positivity
      · linarith
  by_cases h : (0 ≤ᵐ[volume] (f : Eucl d → ℝ)) ∨
      ((f : Eucl d → ℝ) ≤ᵐ[volume] 0)
  · exact h
  · have hnotpos : ¬ (0 ≤ᵐ[volume] (f : Eucl d → ℝ)) := by
      intro hpos
      exact h (Or.inl hpos)
    have hnotneg : ¬ ((f : Eucl d → ℝ) ≤ᵐ[volume] 0) := by
      intro hneg
      exact h (Or.inr hneg)
    have hN : volume {x : Eucl d | (f : Eucl d → ℝ) x < 0} ≠ 0 := by
      intro hN0
      apply hnotpos
      show ∀ᵐ x ∂(volume : Measure (Eucl d)), (0 : Eucl d → ℝ) x ≤ (f : Eucl d → ℝ) x
      rw [ae_iff]
      simpa [not_le] using hN0
    have hP : volume {x : Eucl d | 0 < (f : Eucl d → ℝ) x} ≠ 0 := by
      intro hP0
      apply hnotneg
      show ∀ᵐ x ∂(volume : Measure (Eucl d)), (f : Eucl d → ℝ) x ≤ (0 : Eucl d → ℝ) x
      rw [ae_iff]
      simpa [not_le] using hP0
    let P : Set (Eucl d) := {x | 0 < (f : Eucl d → ℝ) x}
    let N : Set (Eucl d) := {x | (f : Eucl d → ℝ) x < 0}
    have hrect : volume.prod volume (P ×ˢ N) = volume P * volume N := Measure.prod_prod P N
    have hbad : (volume.prod volume) {z : Eucl d × Eucl d |
        ¬ 0 ≤ (f : Eucl d → ℝ) z.1 * (f : Eucl d → ℝ) z.2} = 0 := ae_iff.mp hpair
    have hsubset : P ×ˢ N ⊆ {z : Eucl d × Eucl d |
        ¬ 0 ≤ (f : Eucl d → ℝ) z.1 * (f : Eucl d → ℝ) z.2} := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact not_le_of_gt (mul_neg_of_pos_of_neg hx hy)
    have hzeroProd : volume P * volume N = 0 := by
      rw [← hrect]
      exact measure_mono_null hsubset hbad
    exact ((mul_ne_zero (by simpa [P] using hP) (by simpa [N] using hN)) hzeroProd).elim

end Tunneling
