import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Tunneling.FractionalForm
import Tunneling.Spectral.MinMax

/-!
# The restricted fractional Laplacian on `ℝ^d` as a closed form

This file fixes the concrete objects of paper Section 2.  For an open set
`G ⊆ ℝ^d` the form domain is

  `H^s_0(G) = { u ∈ H^s(ℝ^d) : u = 0 a.e. on ℝ^d \ G }`,

realized as a submodule of `L²(ℝ^d)`, and the zero-exterior form is equation
`eq:form`:

  `Q_G[u] = (c/2) ∬_{ℝ^d × ℝ^d} |u(x) - u(y)|² / |x - y|^κ dx dy`.

The eigenvalues `λ_{k+1}(G)` of the associated operator `A_G`, repeated
according to multiplicity, are the Courant--Fischer levels of this form.
-/

namespace Tunneling

open MeasureTheory

/-- The ambient Euclidean space `ℝ^d`. -/
abbrev Eucl (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `L²(ℝ^d)` with Lebesgue measure. -/
noncomputable abbrev L2 (d : ℕ) := Lp ℝ 2 (volume : Measure (Eucl d))

variable {d : ℕ}

theorem formDomain_zero_mem (κ : ℝ) (G : Set (Eucl d)) :
    (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → (0 : L2 d) x = 0) ∧
      Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ ((0 : L2 d) : Eucl d → ℝ) z)
        (volume.prod volume) := by
  sorry

theorem formDomain_add_mem (κ : ℝ) (G : Set (Eucl d)) {f g : L2 d}
    (hf : (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → f x = 0) ∧
      Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f : Eucl d → ℝ) z)
        (volume.prod volume))
    (hg : (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → g x = 0) ∧
      Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (g : Eucl d → ℝ) z)
        (volume.prod volume)) :
    (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → (f + g) x = 0) ∧
      Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ ((f + g : L2 d) : Eucl d → ℝ) z)
        (volume.prod volume) := by
  sorry

theorem formDomain_smul_mem (κ : ℝ) (G : Set (Eucl d)) (t : ℝ) {f : L2 d}
    (hf : (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → f x = 0) ∧
      Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f : Eucl d → ℝ) z)
        (volume.prod volume)) :
    (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → (t • f) x = 0) ∧
      Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ ((t • f : L2 d) : Eucl d → ℝ) z)
        (volume.prod volume) := by
  sorry

/-- The form domain `H^s_0(G)` of paper Section 2, with `κ = d + 2s`:
functions in `L²(ℝ^d)` vanishing a.e. off `G` whose Gagliardo integrand is
integrable on `ℝ^d × ℝ^d`. -/
def formDomain (κ : ℝ) (G : Set (Eucl d)) : Submodule ℝ (L2 d) where
  carrier := {f | (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → f x = 0) ∧
    Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f : Eucl d → ℝ) z)
      (volume.prod volume)}
  zero_mem' := formDomain_zero_mem κ G
  add_mem' := fun hf hg => formDomain_add_mem κ G hf hg
  smul_mem' := fun t _ hf => formDomain_smul_mem κ G t hf

theorem mem_formDomain_iff (κ : ℝ) (G : Set (Eucl d)) (f : L2 d) :
    f ∈ formDomain κ G ↔
      (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → f x = 0) ∧
        Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f : Eucl d → ℝ) z)
          (volume.prod volume) :=
  Iff.rfl

/-- The energy functional underlying the form, `(c/2) [u]²`. -/
noncomputable def formEnergy (c κ : ℝ) (f : L2 d) : ℝ :=
  c / 2 * gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ)

theorem formEnergy_smul (c κ : ℝ) (G : Set (Eucl d)) (t : ℝ) (f : formDomain κ G) :
    formEnergy c κ ((t • f : formDomain κ G) : L2 d) = t * t * formEnergy c κ (f : L2 d) := by
  sorry

theorem formEnergy_polar_add_left (c κ : ℝ) (G : Set (Eucl d)) (f f' g : formDomain κ G) :
    QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) (f + f') g =
      QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) f g +
        QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) f' g := by
  sorry

theorem formEnergy_polar_smul_left (c κ : ℝ) (G : Set (Eucl d)) (t : ℝ)
    (f g : formDomain κ G) :
    QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) (t • f) g =
      t • QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) f g := by
  sorry

/-- The zero-exterior quadratic form `Q_G` of equation `eq:form` on its form
domain. -/
noncomputable def formQ (c κ : ℝ) (G : Set (Eucl d)) : QuadraticMap ℝ (formDomain κ G) ℝ :=
  QuadraticMap.ofPolar (fun u : formDomain κ G => formEnergy c κ (u : L2 d))
    (formEnergy_smul c κ G) (formEnergy_polar_add_left c κ G)
    (formEnergy_polar_smul_left c κ G)

theorem formQ_apply (c κ : ℝ) (G : Set (Eucl d)) (f : formDomain κ G) :
    formQ c κ G f =
      c / 2 * gagliardoSeminormSq κ (volume : Measure (Eucl d)) ((f : L2 d) : Eucl d → ℝ) :=
  rfl

theorem formQ_nonneg (c κ : ℝ) (hc : 0 ≤ c) (G : Set (Eucl d)) (f : formDomain κ G) :
    0 ≤ formQ c κ G f := by
  sorry

/-- The bilinear form associated with `Q_G`:
`polar Q_G f g = c ∬ (f x - f y) (g x - g y) |x - y|^{-κ}`. -/
theorem formQ_polar (c κ : ℝ) (G : Set (Eucl d)) (f g : formDomain κ G) :
    QuadraticMap.polar (formQ c κ G) f g =
      c * ∫ z : Eucl d × Eucl d,
        (((f : L2 d) : Eucl d → ℝ) z.1 - ((f : L2 d) : Eucl d → ℝ) z.2) *
          (((g : L2 d) : Eucl d → ℝ) z.1 - ((g : L2 d) : Eucl d → ℝ) z.2) *
            gagliardoKernel κ z.1 z.2 ∂(volume.prod volume) := by
  sorry

/-- The eigenvalue `λ_{k+1}(G)` of the restricted fractional Laplacian `A_G`
(paper Section 2), counted from `k = 0` and repeated according to
multiplicity, as the Courant--Fischer level of the closed form `Q_G`. -/
noncomputable def eigenvalue (c κ : ℝ) (G : Set (Eucl d)) (k : ℕ) : ℝ :=
  MinMax.level (formQ c κ G) k

end Tunneling
