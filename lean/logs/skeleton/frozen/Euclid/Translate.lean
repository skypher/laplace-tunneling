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

theorem translateL2_ae (a : Eucl d) (f : L2 d) :
    ((translateL2 a f : L2 d) : Eucl d → ℝ) =ᵐ[volume] fun x => f (x - a) := by
  sorry

theorem translateL2_neg_translateL2 (a : Eucl d) (f : L2 d) :
    translateL2 (-a) (translateL2 a f) = f := by
  sorry

theorem translateL2_zero (f : L2 d) : translateL2 (0 : Eucl d) f = f := by
  sorry

theorem integral_translateL2 (a : Eucl d) (f : L2 d) :
    ∫ x, (translateL2 a f : L2 d) x = ∫ x, f x := by
  sorry

/-- Translation invariance of the Gagliardo seminorm. -/
theorem gagliardoSeminormSq_translateL2 (κ : ℝ) (a : Eucl d) (f : L2 d) :
    gagliardoSeminormSq κ (volume : Measure (Eucl d)) ((translateL2 a f : L2 d) : Eucl d → ℝ) =
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ) := by
  sorry

/-- Translation maps `H^s_0(G)` onto `H^s_0(G + a)`. -/
theorem translateL2_mem_formDomain (κ : ℝ) (a : Eucl d) {G : Set (Eucl d)} {f : L2 d}
    (hf : f ∈ formDomain κ G) :
    translateL2 a f ∈ formDomain κ {x | x - a ∈ G} := by
  sorry

theorem formQ_translate (c κ : ℝ) (a : Eucl d) {G : Set (Eucl d)} (f : formDomain κ G) :
    formQ c κ {x | x - a ∈ G}
        ⟨translateL2 a (f : L2 d), translateL2_mem_formDomain κ a f.2⟩ =
      formQ c κ G f := by
  sorry

theorem indicatorL2_map_add (s : Set (Eucl d)) (hs : MeasurableSet s) (f g : L2 d) :
    ((Lp.memLp (f + g)).indicator hs).toLp (s.indicator ((f + g : L2 d) : Eucl d → ℝ)) =
      ((Lp.memLp f).indicator hs).toLp (s.indicator (f : Eucl d → ℝ)) +
        ((Lp.memLp g).indicator hs).toLp (s.indicator (g : Eucl d → ℝ)) := by
  sorry

theorem indicatorL2_map_smul (s : Set (Eucl d)) (hs : MeasurableSet s) (t : ℝ) (f : L2 d) :
    ((Lp.memLp (t • f)).indicator hs).toLp (s.indicator ((t • f : L2 d) : Eucl d → ℝ)) =
      t • ((Lp.memLp f).indicator hs).toLp (s.indicator (f : Eucl d → ℝ)) := by
  sorry

/-- Multiplication by the indicator of a measurable set on `L²(ℝ^d)`. -/
noncomputable def indicatorL2 (s : Set (Eucl d)) (hs : MeasurableSet s) :
    L2 d →ₗ[ℝ] L2 d where
  toFun f := ((Lp.memLp f).indicator hs).toLp (s.indicator (f : Eucl d → ℝ))
  map_add' f g := indicatorL2_map_add s hs f g
  map_smul' t f := indicatorL2_map_smul s hs t f

theorem indicatorL2_ae (s : Set (Eucl d)) (hs : MeasurableSet s) (f : L2 d) :
    ((indicatorL2 s hs f : L2 d) : Eucl d → ℝ) =ᵐ[volume] s.indicator (f : Eucl d → ℝ) := by
  sorry

theorem indicatorL2_of_ae_zero (s : Set (Eucl d)) (hs : MeasurableSet s) (f : L2 d)
    (hf : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ s → f x = 0) :
    indicatorL2 s hs f = f := by
  sorry

end Tunneling
