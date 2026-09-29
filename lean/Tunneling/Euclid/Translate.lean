import Tunneling.Euclid.FormDomain

/-!
# Translations and indicator restrictions on `L²(ℝ^d)`

Translation invariance of Lebesgue measure and of the Gagliardo kernel gives
the diagonal identifications in paper Lemmas 2.1 and 4.1.
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- Translation `(τ_a f)(x) = f (x - a)` on `L²(ℝ^d)`. -/
noncomputable def translateL2 (a : Eucl d) : L2 d →ₗᵢ[ℝ] L2 d :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : Eucl d => x - a)
    (measurePreserving_sub_right (volume : Measure (Eucl d)) a)

private theorem translatePairMeasurePreserving (a : Eucl d) :
    MeasurePreserving (fun z : Eucl d × Eucl d => (z.1 - a, z.2 - a))
      ((volume : Measure (Eucl d)).prod volume) (volume.prod volume) := by
  convert MeasurePreserving.prod
    (measurePreserving_sub_right (volume : Measure (Eucl d)) a)
    (measurePreserving_sub_right (volume : Measure (Eucl d)) a) using 1
  funext z
  rcases z with ⟨x, y⟩
  rfl

private def translatePairMeasurableEquiv (a : Eucl d) :
    Eucl d × Eucl d ≃ᵐ Eucl d × Eucl d :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.subRight a) (MeasurableEquiv.subRight a)

theorem translateL2_ae (a : Eucl d) (f : L2 d) :
    ((translateL2 a f : L2 d) : Eucl d → ℝ) =ᵐ[volume] fun x => f (x - a) := by
  change (Lp.compMeasurePreserving (fun x : Eucl d => x - a)
    (measurePreserving_sub_right (volume : Measure (Eucl d)) a) f) =ᵐ[volume] _
  simpa [Function.comp_def] using
    (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_sub_right (volume : Measure (Eucl d)) a))

theorem translateL2_neg_translateL2 (a : Eucl d) (f : L2 d) :
    translateL2 (-a) (translateL2 a f) = f := by
  apply Lp.ext
  have h₁ := translateL2_ae (-a) (translateL2 a f)
  have h₂ : (fun x : Eucl d => (translateL2 a f : L2 d) (x - (-a))) =ᵐ[volume]
      fun x => f ((x - (-a)) - a) := by
    simpa [Function.comp_def] using
      ((measurePreserving_sub_right (volume : Measure (Eucl d)) (-a)).quasiMeasurePreserving.ae_eq_comp
        (translateL2_ae a f))
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  simpa [sub_eq_add_neg, add_assoc] using hx₁.trans hx₂

theorem translateL2_zero (f : L2 d) : translateL2 (0 : Eucl d) f = f := by
  apply Lp.ext
  filter_upwards [translateL2_ae (0 : Eucl d) f] with x hx
  simpa using hx

theorem integral_translateL2 (a : Eucl d) (f : L2 d) :
    ∫ x, (translateL2 a f : L2 d) x = ∫ x, f x := by
  calc
    ∫ x, (translateL2 a f : L2 d) x = ∫ x, f (x - a) :=
      integral_congr_ae (translateL2_ae a f)
    _ = ∫ x, f x := by
      exact (measurePreserving_sub_right (volume : Measure (Eucl d)) a).integral_comp'
        (f := MeasurableEquiv.subRight a) f

private theorem gagliardoIntegrand_translateL2_ae (κ : ℝ) (a : Eucl d) (f : L2 d) :
    (fun z : Eucl d × Eucl d =>
      gagliardoIntegrand κ ((translateL2 a f : L2 d) : Eucl d → ℝ) z) =ᵐ[volume.prod volume]
    fun z => gagliardoIntegrand κ (f : Eucl d → ℝ) (z.1 - a, z.2 - a) := by
  have htr := translateL2_ae a f
  have hfst : (fun z : Eucl d × Eucl d => (translateL2 a f : L2 d) z.1) =ᵐ[volume.prod volume]
      fun z => f (z.1 - a) :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Eucl d)))
      (ν := (volume : Measure (Eucl d)))).ae_eq_comp htr
  have hsnd : (fun z : Eucl d × Eucl d => (translateL2 a f : L2 d) z.2) =ᵐ[volume.prod volume]
      fun z => f (z.2 - a) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Eucl d)))
      (ν := (volume : Measure (Eucl d)))).ae_eq_comp htr
  filter_upwards [hfst, hsnd] with z hz₁ hz₂
  rcases z with ⟨x, y⟩
  dsimp [gagliardoIntegrand, gagliardoKernel]
  rw [hz₁, hz₂]
  rw [show x - a - (y - a) = x - y by abel]

private theorem gagliardoIntegrand_comp_translate (κ : ℝ) (a : Eucl d) (f : L2 d)
    (z : Eucl d × Eucl d) :
    gagliardoIntegrand κ (fun x => f (x - a)) z =
      gagliardoIntegrand κ (f : Eucl d → ℝ) (z.1 - a, z.2 - a) := by
  rcases z with ⟨x, y⟩
  simp [gagliardoIntegrand, gagliardoKernel,
    show x - a - (y - a) = x - y by abel]

/-- Translation invariance of the Gagliardo seminorm. -/
theorem gagliardoSeminormSq_translateL2 (κ : ℝ) (a : Eucl d) (f : L2 d) :
    gagliardoSeminormSq κ (volume : Measure (Eucl d)) ((translateL2 a f : L2 d) : Eucl d → ℝ) =
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ) := by
  calc
    gagliardoSeminormSq κ (volume : Measure (Eucl d))
        ((translateL2 a f : L2 d) : Eucl d → ℝ) =
      gagliardoSeminormSq κ (volume : Measure (Eucl d))
        (fun x => f (x - a)) :=
      gagliardoSeminormSq_congr_ae κ volume (translateL2_ae a f)
    _ = ∫ z : Eucl d × Eucl d,
        gagliardoIntegrand κ (f : Eucl d → ℝ) (z.1 - a, z.2 - a) ∂(volume.prod volume) := by
      unfold gagliardoSeminormSq
      exact integral_congr_ae (ae_of_all _ (gagliardoIntegrand_comp_translate κ a f))
    _ = gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ) := by
      rw [gagliardoSeminormSq]
      calc
        ∫ z : Eucl d × Eucl d,
            gagliardoIntegrand κ (f : Eucl d → ℝ) (z.1 - a, z.2 - a) ∂(volume.prod volume) =
          ∫ z : Eucl d × Eucl d,
            gagliardoIntegrand κ (f : Eucl d → ℝ) (translatePairMeasurableEquiv a z)
              ∂(volume.prod volume) := by
          apply integral_congr_ae
          exact ae_of_all _ (fun z => by rcases z with ⟨x, y⟩; rfl)
        _ = ∫ z : Eucl d × Eucl d,
            gagliardoIntegrand κ (f : Eucl d → ℝ) z ∂(volume.prod volume) :=
          (translatePairMeasurePreserving a).integral_comp'
            (f := translatePairMeasurableEquiv a)
            (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f : Eucl d → ℝ) z)

private theorem pairIntegrand_eq_equiv (κ : ℝ) (a : Eucl d) (f : L2 d) :
    (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f : Eucl d → ℝ) (z.1 - a, z.2 - a)) =
      (fun z => gagliardoIntegrand κ (f : Eucl d → ℝ) (translatePairMeasurableEquiv a z)) := by
  funext z
  rcases z with ⟨x, y⟩
  rfl

/-- Translation maps `H^s_0(G)` onto `H^s_0(G + a)`. -/
theorem translateL2_mem_formDomain (κ : ℝ) (a : Eucl d) {G : Set (Eucl d)} {f : L2 d}
    (hf : f ∈ formDomain κ G) :
    translateL2 a f ∈ formDomain κ {x | x - a ∈ G} := by
  rw [mem_formDomain_iff] at hf ⊢
  constructor
  · have hzero : ∀ᵐ x ∂(volume : Measure (Eucl d)), x - a ∉ G → f (x - a) = 0 :=
      (measurePreserving_sub_right (volume : Measure (Eucl d)) a).quasiMeasurePreserving.ae hf.1
    filter_upwards [translateL2_ae a f, hzero] with x htr hvanish
    intro hx
    rw [htr]
    exact hvanish hx
  · have hcomp : Integrable
        (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f : Eucl d → ℝ) (z.1 - a, z.2 - a))
        (volume.prod volume) := by
      have hcomp' : Integrable
          (fun z : Eucl d × Eucl d =>
            gagliardoIntegrand κ (f : Eucl d → ℝ) (translatePairMeasurableEquiv a z))
          (volume.prod volume) :=
        ((translatePairMeasurePreserving a).integrable_comp_emb
          (translatePairMeasurableEquiv a).measurableEmbedding).2 hf.2
      rw [pairIntegrand_eq_equiv κ a f]
      exact hcomp'
    exact hcomp.congr (gagliardoIntegrand_translateL2_ae κ a f).symm

theorem formQ_translate (c κ : ℝ) (a : Eucl d) {G : Set (Eucl d)} (f : formDomain κ G) :
    formQ c κ {x | x - a ∈ G}
        ⟨translateL2 a (f : L2 d), translateL2_mem_formDomain κ a f.2⟩ =
      formQ c κ G f := by
  rw [formQ_apply, formQ_apply, gagliardoSeminormSq_translateL2]

theorem indicatorL2_map_add (s : Set (Eucl d)) (hs : MeasurableSet s) (f g : L2 d) :
    ((Lp.memLp (f + g)).indicator hs).toLp (s.indicator ((f + g : L2 d) : Eucl d → ℝ)) =
      ((Lp.memLp f).indicator hs).toLp (s.indicator (f : Eucl d → ℝ)) +
        ((Lp.memLp g).indicator hs).toLp (s.indicator (g : Eucl d → ℝ)) := by
  apply Lp.ext
  grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
  filter_upwards [Lp.coeFn_add f g] with x hx
  by_cases hxs : x ∈ s
  · simpa [Set.indicator, hxs] using hx
  · simp [Set.indicator, hxs]

theorem indicatorL2_map_smul (s : Set (Eucl d)) (hs : MeasurableSet s) (t : ℝ) (f : L2 d) :
    ((Lp.memLp (t • f)).indicator hs).toLp (s.indicator ((t • f : L2 d) : Eucl d → ℝ)) =
      t • ((Lp.memLp f).indicator hs).toLp (s.indicator (f : Eucl d → ℝ)) := by
  apply Lp.ext
  grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
  filter_upwards [Lp.coeFn_smul t f] with x hx
  by_cases hxs : x ∈ s
  · simp [Set.indicator, hxs, hx]
  · simp [Set.indicator, hxs]

/-- Multiplication by the indicator of a measurable set on `L²(ℝ^d)`. -/
noncomputable def indicatorL2 (s : Set (Eucl d)) (hs : MeasurableSet s) :
    L2 d →ₗ[ℝ] L2 d where
  toFun f := ((Lp.memLp f).indicator hs).toLp (s.indicator (f : Eucl d → ℝ))
  map_add' f g := indicatorL2_map_add s hs f g
  map_smul' t f := indicatorL2_map_smul s hs t f

private theorem indicatorL2_apply (s : Set (Eucl d)) (hs : MeasurableSet s) (f : L2 d) :
    indicatorL2 s hs f = ((Lp.memLp f).indicator hs).toLp (s.indicator (f : Eucl d → ℝ)) := by
  rw [indicatorL2, LinearMap.coe_mk, AddHom.coe_mk]

theorem indicatorL2_ae (s : Set (Eucl d)) (hs : MeasurableSet s) (f : L2 d) :
    ((indicatorL2 s hs f : L2 d) : Eucl d → ℝ) =ᵐ[volume] s.indicator (f : Eucl d → ℝ) := by
  rw [indicatorL2_apply]
  exact MemLp.coeFn_toLp _

theorem indicatorL2_of_ae_zero (s : Set (Eucl d)) (hs : MeasurableSet s) (f : L2 d)
    (hf : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ s → f x = 0) :
    indicatorL2 s hs f = f := by
  apply Lp.ext
  filter_upwards [indicatorL2_ae s hs f, hf] with x hindicator hzero
  by_cases hxs : x ∈ s
  · simpa [Set.indicator, hxs] using hindicator
  · calc
      (indicatorL2 s hs f : L2 d) x = s.indicator (f : Eucl d → ℝ) x := hindicator
      _ = f x := by simp [Set.indicator, hxs, hzero hxs]

end Tunneling
