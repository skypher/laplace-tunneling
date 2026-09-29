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

private theorem ae_L2_add (f g : L2 d) :
    (f + g : L2 d) =ᵐ[volume] (fun x : Eucl d => f x + g x) := by
  exact MeasureTheory.Lp.coeFn_add f g

private theorem ae_L2_smul (t : ℝ) (f : L2 d) :
    (t • f : L2 d) =ᵐ[volume] (fun x : Eucl d => t * f x) := by
  exact MeasureTheory.Lp.coeFn_smul t f

private theorem ae_L2_sub (f g : L2 d) :
    (f - g : L2 d) =ᵐ[volume] (fun x : Eucl d => f x - g x) := by
  exact MeasureTheory.Lp.coeFn_sub f g

private theorem ae_gagliardoIntegrand_congr
    (κ : ℝ) {u v : Eucl d → ℝ} (h : u =ᵐ[volume] v) :
    (fun z : Eucl d × Eucl d => gagliardoIntegrand κ u z) =ᵐ[volume.prod volume]
      (fun z => gagliardoIntegrand κ v z) := by
  have hfst : (fun z : Eucl d × Eucl d => u z.1) =ᵐ[volume.prod volume]
      (fun z => v z.1) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae_eq_comp h
  have hsnd : (fun z : Eucl d × Eucl d => u z.2) =ᵐ[volume.prod volume]
      (fun z => v z.2) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae_eq_comp h
  filter_upwards [hfst, hsnd] with z hz₁ hz₂
  simp [gagliardoIntegrand, hz₁, hz₂]

theorem formDomain_zero_mem (κ : ℝ) (G : Set (Eucl d)) :
    (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → (0 : L2 d) x = 0) ∧
      Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ ((0 : L2 d) : Eucl d → ℝ) z)
        (volume.prod volume) := by
  constructor
  · filter_upwards [MeasureTheory.Lp.coeFn_zero ℝ 2 (volume : Measure (Eucl d))] with x hx
    intro _
    exact hx
  · have hzero : (0 : L2 d) =ᵐ[volume] (0 : Eucl d → ℝ) :=
      MeasureTheory.Lp.coeFn_zero ℝ 2 (volume : Measure (Eucl d))
    have hcongr := ae_gagliardoIntegrand_congr κ hzero
    have hbase : Integrable
        (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (0 : Eucl d → ℝ) z)
        (volume.prod volume) := by
      simp [gagliardoIntegrand]
    exact hbase.congr hcongr.symm

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
  constructor
  · filter_upwards [hf.1, hg.1, MeasureTheory.Lp.coeFn_add f g] with x hfx hgx hadd
    intro hx
    rw [hadd, Pi.add_apply, hfx hx, hgx hx]
    norm_num
  · let u : Eucl d → ℝ := (f : Eucl d → ℝ)
    let v : Eucl d → ℝ := (g : Eucl d → ℝ)
    have hK := gagliardoKernel_aestronglyMeasurable κ (volume : Measure (Eucl d))
    have hmeas := gagliardoIntegrand_aestronglyMeasurable κ
      (volume : Measure (Eucl d)) hK
      ((MeasureTheory.Lp.aestronglyMeasurable f).add
        (MeasureTheory.Lp.aestronglyMeasurable g))
    have hupper : Integrable
        (fun z : Eucl d × Eucl d =>
          2 * gagliardoIntegrand κ u z + 2 * gagliardoIntegrand κ v z)
        (volume.prod volume) :=
      (hf.2.const_mul 2).add (hg.2.const_mul 2)
    have hnonneg : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
        0 ≤ gagliardoIntegrand κ (u + v) z :=
      MeasureTheory.ae_of_all _ (fun z => gagliardoIntegrand_nonneg κ _ z)
    have hle : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
        gagliardoIntegrand κ (u + v) z ≤
          2 * gagliardoIntegrand κ u z + 2 * gagliardoIntegrand κ v z :=
      MeasureTheory.ae_of_all _ (fun z => gagliardoIntegrand_add_le κ u v z)
    have hsum : Integrable
        (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (u + v) z)
        (volume.prod volume) :=
      hupper.mono_nonneg hmeas hnonneg hle
    have hrep := ae_gagliardoIntegrand_congr κ (ae_L2_add f g)
    exact hsum.congr hrep.symm

theorem formDomain_smul_mem (κ : ℝ) (G : Set (Eucl d)) (t : ℝ) {f : L2 d}
    (hf : (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → f x = 0) ∧
      Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f : Eucl d → ℝ) z)
        (volume.prod volume)) :
    (∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G → (t • f) x = 0) ∧
      Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ ((t • f : L2 d) : Eucl d → ℝ) z)
        (volume.prod volume) := by
  constructor
  · filter_upwards [hf.1, MeasureTheory.Lp.coeFn_smul t f] with x hx hsmul
    intro hxG
    simp [hsmul, hx hxG]
  · have hsmul : (fun z : Eucl d × Eucl d =>
        gagliardoIntegrand κ ((t • f : L2 d) : Eucl d → ℝ) z) =ᵐ[volume.prod volume]
      (fun z => t ^ 2 * gagliardoIntegrand κ (f : Eucl d → ℝ) z) := by
      have hcongr := ae_gagliardoIntegrand_congr κ (ae_L2_smul t f)
      filter_upwards [hcongr] with z hz
      calc
        gagliardoIntegrand κ ((t • f : L2 d) : Eucl d → ℝ) z =
            gagliardoIntegrand κ (fun x : Eucl d => t * f x) z := hz
        _ = t ^ 2 * gagliardoIntegrand κ (f : Eucl d → ℝ) z :=
          gagliardoIntegrand_smul κ t (f : Eucl d → ℝ) z
    exact (hf.2.const_mul (t ^ 2)).congr hsmul.symm

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

private theorem formDomain_gagliardo_integrable (κ : ℝ) (G : Set (Eucl d))
    (f : formDomain κ G) :
    Integrable
      (fun z : Eucl d × Eucl d =>
        gagliardoIntegrand κ (((f : formDomain κ G) : L2 d) : Eucl d → ℝ) z)
      (volume.prod volume) := by
  exact ((mem_formDomain_iff κ G ((f : formDomain κ G) : L2 d)).mp f.property).2

private theorem formDomain_gagliardo_integrable_add (κ : ℝ) (G : Set (Eucl d))
    (f g : formDomain κ G) :
    Integrable
      (fun z : Eucl d × Eucl d =>
        gagliardoIntegrand κ
          ((((f : formDomain κ G) : L2 d) : Eucl d → ℝ) +
            (((g : formDomain κ G) : L2 d) : Eucl d → ℝ)) z)
      (volume.prod volume) := by
  have hsum := formDomain_gagliardo_integrable κ G (f + g)
  have hrep := ae_gagliardoIntegrand_congr κ
    (ae_L2_add (f : L2 d) (g : L2 d))
  exact hsum.congr hrep

private theorem formDomain_gagliardo_integrable_sub (κ : ℝ) (G : Set (Eucl d))
    (f g : formDomain κ G) :
    Integrable
      (fun z : Eucl d × Eucl d =>
        gagliardoIntegrand κ
          ((((f : formDomain κ G) : L2 d) : Eucl d → ℝ) -
            (((g : formDomain κ G) : L2 d) : Eucl d → ℝ)) z)
      (volume.prod volume) := by
  have hsub := formDomain_gagliardo_integrable κ G (f - g)
  have hrep := ae_gagliardoIntegrand_congr κ
    (ae_L2_sub (f : L2 d) (g : L2 d))
  exact hsub.congr hrep

theorem formEnergy_smul (c κ : ℝ) (G : Set (Eucl d)) (t : ℝ) (f : formDomain κ G) :
    formEnergy c κ ((t • f : formDomain κ G) : L2 d) = t * t * formEnergy c κ (f : L2 d) := by
  simp only [Submodule.coe_smul]
  unfold formEnergy
  rw [gagliardoSeminormSq_congr_ae κ (volume : Measure (Eucl d))
      (ae_L2_smul t (f : L2 d)),
    gagliardoSeminormSq_smul]
  ring

private noncomputable def formCrossIntegrand
    (κ : ℝ) (u v : Eucl d → ℝ) (z : Eucl d × Eucl d) : ℝ :=
  (u z.1 - u z.2) * (v z.1 - v z.2) * gagliardoKernel κ z.1 z.2

private theorem formCrossIntegrand_integrable (κ : ℝ) (G : Set (Eucl d))
    (f g : formDomain κ G) :
    Integrable
      (fun z : Eucl d × Eucl d =>
        formCrossIntegrand κ
          (((f : formDomain κ G) : L2 d) : Eucl d → ℝ)
          (((g : formDomain κ G) : L2 d) : Eucl d → ℝ) z)
      (volume.prod volume) := by
  let u : Eucl d → ℝ := (((f : formDomain κ G) : L2 d) : Eucl d → ℝ)
  let v : Eucl d → ℝ := (((g : formDomain κ G) : L2 d) : Eucl d → ℝ)
  have hplus : Integrable
      (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (u + v) z)
      (volume.prod volume) := by
    have hsum := formDomain_gagliardo_integrable_add κ G f g
    change Integrable
      (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (u + v) z)
      (volume.prod volume) at hsum
    exact hsum
  have hminus : Integrable
      (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (u - v) z)
      (volume.prod volume) := by
    have hsub := formDomain_gagliardo_integrable_sub κ G f g
    change Integrable
      (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (u - v) z)
      (volume.prod volume) at hsub
    exact hsub
  change Integrable
      (fun z : Eucl d × Eucl d => formCrossIntegrand κ u v z)
      (volume.prod volume)
  have hscaled : Integrable
      (fun z : Eucl d × Eucl d =>
        (1 / 4 : ℝ) * (gagliardoIntegrand κ (u + v) z -
          gagliardoIntegrand κ (u - v) z))
      (volume.prod volume) :=
    (hplus.sub hminus).const_mul (1 / 4)
  exact hscaled.congr (MeasureTheory.ae_of_all _ (fun z => by
    simp only [formCrossIntegrand, gagliardoIntegrand, Pi.add_apply, Pi.sub_apply]
    ring))

private theorem formEnergy_polar_cross (c κ : ℝ) (G : Set (Eucl d))
    (f g : formDomain κ G) :
    QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) f g =
      c * ∫ z : Eucl d × Eucl d,
        formCrossIntegrand κ
          (((f : formDomain κ G) : L2 d) : Eucl d → ℝ)
          (((g : formDomain κ G) : L2 d) : Eucl d → ℝ) z
          ∂(volume.prod volume) := by
  let u : Eucl d → ℝ := (((f : formDomain κ G) : L2 d) : Eucl d → ℝ)
  let v : Eucl d → ℝ := (((g : formDomain κ G) : L2 d) : Eucl d → ℝ)
  have hu : Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ u z)
      (volume.prod volume) := formDomain_gagliardo_integrable κ G f
  have hv : Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand κ v z)
      (volume.prod volume) := formDomain_gagliardo_integrable κ G g
  have hplus : Integrable
      (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (u + v) z)
      (volume.prod volume) := by
    have hsum := formDomain_gagliardo_integrable_add κ G f g
    change Integrable
      (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (u + v) z)
      (volume.prod volume) at hsum
    exact hsum
  have hcross : Integrable
      (fun z : Eucl d × Eucl d => formCrossIntegrand κ u v z)
      (volume.prod volume) := by
    change Integrable
      (fun z : Eucl d × Eucl d =>
        formCrossIntegrand κ
          (((f : formDomain κ G) : L2 d) : Eucl d → ℝ)
          (((g : formDomain κ G) : L2 d) : Eucl d → ℝ) z)
      (volume.prod volume)
    exact formCrossIntegrand_integrable κ G f g
  have hpoint : ∀ z : Eucl d × Eucl d,
      gagliardoIntegrand κ (u + v) z =
        (gagliardoIntegrand κ u z + gagliardoIntegrand κ v z) +
          2 * formCrossIntegrand κ u v z := by
    intro z
    simp only [gagliardoIntegrand, formCrossIntegrand, Pi.add_apply]
    ring
  have hint :
      ∫ z : Eucl d × Eucl d, gagliardoIntegrand κ (u + v) z ∂(volume.prod volume) =
        (∫ z, gagliardoIntegrand κ u z ∂(volume.prod volume)) +
          (∫ z, gagliardoIntegrand κ v z ∂(volume.prod volume)) +
            2 * ∫ z, formCrossIntegrand κ u v z ∂(volume.prod volume) := by
    calc
      ∫ z : Eucl d × Eucl d, gagliardoIntegrand κ (u + v) z ∂(volume.prod volume) =
          ∫ z : Eucl d × Eucl d,
            (gagliardoIntegrand κ u z + gagliardoIntegrand κ v z) +
              2 * formCrossIntegrand κ u v z ∂(volume.prod volume) :=
        MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_of_all _ hpoint)
      _ = (∫ z : Eucl d × Eucl d,
            gagliardoIntegrand κ u z + gagliardoIntegrand κ v z ∂(volume.prod volume)) +
          ∫ z : Eucl d × Eucl d, 2 * formCrossIntegrand κ u v z ∂(volume.prod volume) :=
        MeasureTheory.integral_add (hu.add hv) (hcross.const_mul 2)
      _ = _ := by
        rw [MeasureTheory.integral_add hu hv, MeasureTheory.integral_const_mul]
  change formEnergy c κ ((f + g : formDomain κ G) : L2 d) -
      formEnergy c κ (f : L2 d) - formEnergy c κ (g : L2 d) =
    c * ∫ z : Eucl d × Eucl d, formCrossIntegrand κ u v z ∂(volume.prod volume)
  simp only [formEnergy, Submodule.coe_add]
  rw [gagliardoSeminormSq_congr_ae κ (volume : Measure (Eucl d))
    (ae_L2_add (f : L2 d) (g : L2 d))]
  change c / 2 * (∫ z : Eucl d × Eucl d, gagliardoIntegrand κ (u + v) z
        ∂(volume.prod volume)) -
      c / 2 * (∫ z : Eucl d × Eucl d, gagliardoIntegrand κ u z
        ∂(volume.prod volume)) -
      c / 2 * (∫ z : Eucl d × Eucl d, gagliardoIntegrand κ v z
        ∂(volume.prod volume)) =
    c * ∫ z : Eucl d × Eucl d, formCrossIntegrand κ u v z ∂(volume.prod volume)
  rw [hint]
  ring

theorem formEnergy_polar_add_left (c κ : ℝ) (G : Set (Eucl d)) (f f' g : formDomain κ G) :
    QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) (f + f') g =
      QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) f g +
        QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) f' g := by
  rw [formEnergy_polar_cross c κ G (f + f') g,
    formEnergy_polar_cross c κ G f g, formEnergy_polar_cross c κ G f' g]
  have h1 : (fun z : Eucl d × Eucl d =>
        formCrossIntegrand κ
          ((((f + f' : formDomain κ G) : L2 d) : Eucl d → ℝ))
          (((g : formDomain κ G) : L2 d) : Eucl d → ℝ) z) =ᵐ[volume.prod volume]
      (fun z => formCrossIntegrand κ
          ((((f : formDomain κ G) : L2 d) : Eucl d → ℝ))
          (((g : formDomain κ G) : L2 d) : Eucl d → ℝ) z +
        formCrossIntegrand κ
          ((((f' : formDomain κ G) : L2 d) : Eucl d → ℝ))
          (((g : formDomain κ G) : L2 d) : Eucl d → ℝ) z) := by
    have hfst : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
        ((f + f' : formDomain κ G) : L2 d) z.1 =
          (f : L2 d) z.1 + (f' : L2 d) z.1 := by
      simpa only [Submodule.coe_add] using
        ae_comp_fst_of_ae (ae_L2_add (f : L2 d) (f' : L2 d))
    have hsnd : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
        ((f + f' : formDomain κ G) : L2 d) z.2 =
          (f : L2 d) z.2 + (f' : L2 d) z.2 := by
      have hcomp := (MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure (Eucl d))) (ν := volume)).ae_eq_comp
          (ae_L2_add (f : L2 d) (f' : L2 d))
      filter_upwards [hcomp] with z hz
      simpa only [Function.comp_apply, Submodule.coe_add] using hz
    filter_upwards [hfst, hsnd] with z hz₁ hz₂
    simp only [formCrossIntegrand]
    rw [hz₁, hz₂]
    ring
  have hcf := formCrossIntegrand_integrable κ G f g
  have hcf' := formCrossIntegrand_integrable κ G f' g
  rw [MeasureTheory.integral_congr_ae h1,
    MeasureTheory.integral_add hcf hcf']
  ring

theorem formEnergy_polar_smul_left (c κ : ℝ) (G : Set (Eucl d)) (t : ℝ)
    (f g : formDomain κ G) :
    QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) (t • f) g =
      t • QuadraticMap.polar (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) f g := by
  rw [formEnergy_polar_cross c κ G (t • f) g,
    formEnergy_polar_cross c κ G f g]
  have h1 : (fun z : Eucl d × Eucl d =>
        formCrossIntegrand κ
          ((((t • f : formDomain κ G) : L2 d) : Eucl d → ℝ))
          (((g : formDomain κ G) : L2 d) : Eucl d → ℝ) z) =ᵐ[volume.prod volume]
      (fun z => t * formCrossIntegrand κ
          ((((f : formDomain κ G) : L2 d) : Eucl d → ℝ))
          (((g : formDomain κ G) : L2 d) : Eucl d → ℝ) z) := by
    have hfst : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
        ((t • f : formDomain κ G) : L2 d) z.1 = t * (f : L2 d) z.1 := by
      simpa only [Submodule.coe_smul] using
        ae_comp_fst_of_ae (ae_L2_smul t (f : L2 d))
    have hsnd : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
        ((t • f : formDomain κ G) : L2 d) z.2 = t * (f : L2 d) z.2 := by
      have hcomp := (MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure (Eucl d))) (ν := volume)).ae_eq_comp
          (ae_L2_smul t (f : L2 d))
      filter_upwards [hcomp] with z hz
      simpa only [Function.comp_apply, Submodule.coe_smul] using hz
    filter_upwards [hfst, hsnd] with z hz₁ hz₂
    simp only [formCrossIntegrand]
    rw [hz₁, hz₂]
    ring
  rw [MeasureTheory.integral_congr_ae h1,
    MeasureTheory.integral_const_mul]
  simp [smul_eq_mul]
  ring

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
  rw [formQ_apply]
  apply mul_nonneg
  · exact div_nonneg hc (by norm_num)
  · exact gagliardoSeminormSq_nonneg κ (volume : Measure (Eucl d))
      ((f : L2 d) : Eucl d → ℝ)

/-- The bilinear form associated with `Q_G`:
`polar Q_G f g = c ∬ (f x - f y) (g x - g y) |x - y|^{-κ}`. -/
theorem formQ_polar (c κ : ℝ) (G : Set (Eucl d)) (f g : formDomain κ G) :
    QuadraticMap.polar (formQ c κ G) f g =
      c * ∫ z : Eucl d × Eucl d,
        (((f : L2 d) : Eucl d → ℝ) z.1 - ((f : L2 d) : Eucl d → ℝ) z.2) *
          (((g : L2 d) : Eucl d → ℝ) z.1 - ((g : L2 d) : Eucl d → ℝ) z.2) *
            gagliardoKernel κ z.1 z.2 ∂(volume.prod volume) := by
  change QuadraticMap.polar
      (fun u : formDomain κ G => formEnergy c κ (u : L2 d)) f g = _
  exact formEnergy_polar_cross c κ G f g

/-- The eigenvalue `λ_{k+1}(G)` of the restricted fractional Laplacian `A_G`
(paper Section 2), counted from `k = 0` and repeated according to
multiplicity, as the Courant--Fischer level of the closed form `Q_G`. -/
noncomputable def eigenvalue (c κ : ℝ) (G : Set (Eucl d)) (k : ℕ) : ℝ :=
  MinMax.level (formQ c κ G) k

end Tunneling

