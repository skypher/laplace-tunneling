import Tunneling.Statements
import Tunneling.Perturbation
import Tunneling.FractionalForm
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Conditional two-well interfaces (superseded)

This module predates the unconditional development in `Tunneling/Euclid`.
`FinalTheorem` is conditional on the abstract spectral input
`TwoWellSpectralInput`, and its `lambda` are branch Rayleigh energies rather
than eigenvalues of `A_{Ω_L}`.  `FinalTheoremL2` is conditional on
`L2TwoWellAux`, whose one-well form integrates over `X × X` with every point of
`X` in the ball of radius `R` (the regional form on the well), not over
`ℝ^d × ℝ^d` as in paper equation `eq:form`.  Neither is the paper's Theorem 3.3.

The paper's Theorem 3.3 is `Tunneling.twoWell_main`
(`Tunneling/Euclid/Main.lean`), proved for the restricted fractional Laplacian
without additional hypotheses.  This file is kept for its algebraic lemmas,
in particular `twoWellGapLimit_of_branchErrors`, which that proof uses.
-/

namespace Tunneling

open GroundStatePerturbation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A bounded symmetric cross pairing, represented in the conjugate-linear
first slot used by the Fréchet-Riesz sesquilinear form API. -/
structure SymmetricCrossPairing (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  form : H →L⋆[ℝ] H →L[ℝ] ℝ
  sym : ∀ x y : H, form x y = form y x

namespace SymmetricCrossPairing

/-- The zero symmetric pairing, used to extend valid-range cross data to all
separations without asserting any operator outside the theorem's range. -/
noncomputable def zero
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    SymmetricCrossPairing H where
  form := 0
  sym := by
    intro x y
    simp

/-- The bounded operator represented by a symmetric cross pairing. -/
noncomputable def operator (χ : SymmetricCrossPairing H) : H →L[ℝ] H :=
  InnerProductSpace.continuousLinearMapOfBilin χ.form

theorem operator_inner (χ : SymmetricCrossPairing H) (x y : H) :
    inner ℝ (χ.operator x) y = χ.form x y :=
  InnerProductSpace.continuousLinearMapOfBilin_apply χ.form x y

theorem operator_symm (χ : SymmetricCrossPairing H) (x y : H) :
    inner ℝ (χ.operator x) y = inner ℝ x (χ.operator y) := by
  rw [operator_inner, real_inner_comm, operator_inner]
  exact χ.sym x y

/-- A uniform bilinear estimate for a cross pairing gives the Schur-type
operator bound used for `B_L`. -/
theorem operator_norm_le (χ : SymmetricCrossPairing H) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y : H, |χ.form x y| ≤ C * ‖x‖ * ‖y‖) : ‖χ.operator‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC ?_
  intro x
  by_cases hx : ‖χ.operator x‖ = 0
  · rw [hx]
    nlinarith [mul_nonneg hC (norm_nonneg x)]
  · have hinner := h x (χ.operator x)
    have hsq : χ.form x (χ.operator x) = ‖χ.operator x‖ * ‖χ.operator x‖ := by
      rw [← operator_inner, real_inner_self_eq_norm_mul_norm]
    have habs : χ.form x (χ.operator x) ≤ C * ‖x‖ * ‖χ.operator x‖ := by
      exact (abs_le.mp hinner).2
    have ht : 0 < ‖χ.operator x‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    by_contra! hlt
    have hmul : C * ‖x‖ * ‖χ.operator x‖ < ‖χ.operator x‖ * ‖χ.operator x‖ :=
      mul_lt_mul_of_pos_right hlt ht
    have hle : ‖χ.operator x‖ * ‖χ.operator x‖ ≤ C * ‖x‖ * ‖χ.operator x‖ := by
      rw [← hsq]
      exact habs
    exact absurd hmul (not_lt_of_ge hle)

end SymmetricCrossPairing

/-- A bounded cross pairing on `L²` whose values are given by a chosen kernel.
The kernel is the translated separated kernel in Lemma 2.1. -/
structure L2CrossPairing (X : Type*) [MeasurableSpace X] [NormedAddCommGroup X]
    (K : X → X → ℝ) (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu] where
  form : (MeasureTheory.Lp ℝ 2 mu) →L⋆[ℝ]
    (MeasureTheory.Lp ℝ 2 mu) →L[ℝ] ℝ
  hsymm : ∀ x y : X, K x y = K y x
  hform : ∀ u v : MeasureTheory.Lp ℝ 2 mu,
    form u v = kernelCrossPairing K mu ⇑u ⇑v

namespace L2CrossPairing

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]
  {K : X → X → ℝ} {mu : MeasureTheory.Measure X} [MeasureTheory.SFinite mu]

/-- Construct the bounded `L²` kernel pairing directly from a uniformly
bounded measurable kernel.  The continuity bound is the Schur estimate from
`kernelCrossPairing_Lp_le`. -/
noncomputable def ofKernel
    [MeasureTheory.IsFiniteMeasure mu]
    (K : X → X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ x y, |K x y| ≤ C)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => K z.1 z.2) (mu.prod mu))
    (hsymm : ∀ x y, K x y = K y x) :
    L2CrossPairing X K mu where
  form :=
    LinearMap.mkContinuous₂
      (LinearMap.mk₂'ₛₗ _ _
        (fun u v => kernelCrossPairing K mu ⇑u ⇑v)
        (fun u₁ u₂ v =>
          kernelCrossPairing_add_left K C hK hmeas u₁ u₂ v)
        (fun c u v => by
          rw [kernelCrossPairing_smul_left K c u v]
          simp)
        (fun u v₁ v₂ =>
          kernelCrossPairing_add_right K C hK hmeas hsymm u v₁ v₂)
        (fun c u v => by
          rw [kernelCrossPairing_smul_right K hsymm c u v]
          simp))
      (C * mu.real Set.univ)
      (fun u v => by
        have h := kernelCrossPairing_Lp_le K C hC hK mu u v
        simpa [mul_assoc, mul_comm, mul_left_comm] using h)
  hsymm := hsymm
  hform := by
    intro u v
    rfl

/-- The symmetric cross pairing represented by a symmetric `L²` kernel. -/
noncomputable def toSymmetric (χ : L2CrossPairing X K mu) :
    SymmetricCrossPairing (MeasureTheory.Lp ℝ 2 mu) where
  form := χ.form
  sym := by
    intro u v
    rw [χ.hform u v, χ.hform v u]
    exact kernelCrossPairing_symm K χ.hsymm mu ⇑u ⇑v

theorem operator_inner_eq_kernelCrossPairing (χ : L2CrossPairing X K mu)
    (u v : MeasureTheory.Lp ℝ 2 mu) :
    inner ℝ ((L2CrossPairing.toSymmetric χ).operator u) v =
      kernelCrossPairing K mu ⇑u ⇑v := by
  rw [SymmetricCrossPairing.operator_inner]
  exact χ.hform u v

end L2CrossPairing

/-- Scalar specialization of the integrated Gagliardo cross-term identity in
Lemma 2.1.  The branch remainder algebra below consumes this exact
cancellation rather than a separate surrogate identity. -/
theorem scalar_crossTerm (a b : ℝ) :
    (a - b) ^ 2 - a ^ 2 - b ^ 2 = -2 * a * b := by
  have h := pairCrossExcessIntegral_eq (X := ℝ)
    (mu := MeasureTheory.Measure.dirac (0 : ℝ)) (kappa := 0)
    (u := fun _ => a) (v := fun _ => b)
  rw [MeasureTheory.Measure.dirac_prod_dirac,
    MeasureTheory.integral_dirac, MeasureTheory.integral_dirac] at h
  simp only [pairCrossExcess, crossIntegrand, gagliardoKernel,
    sub_self, Real.rpow_zero, one_mul] at h
  nlinarith [h]

/-- The unit sphere of a real Hilbert space. -/
def UnitVector (H : Type*) [NormedAddCommGroup H] : Type _ :=
  {x : H // ‖x‖ = 1}

/-- The lowest Rayleigh energy of `q + W` over normalized vectors. -/
noncomputable def branchEnergy (q : H → ℝ) (W : H →L[ℝ] H) : ℝ :=
  ⨅ ψ : UnitVector H, GroundStatePerturbation.branchRayleigh q W ψ.val

/-- Lemma 3.1 packaged as the two-sided estimate for a branch ground energy. -/
theorem branch_energy_bounds
    (φ : H) (q : H → ℝ) (mu gap : ℝ) (W : H →L[ℝ] H)
    (hφ : ‖φ‖ = 1)
    (hqφ : q φ = mu)
    (hqGroundAdd : ∀ (t : ℝ) (r : H), inner ℝ φ r = 0 →
      q (t • φ + r) = q (t • φ) + q r)
    (hqSmul : ∀ (t : ℝ) (x : H), q (t • x) = t ^ 2 * q x)
    (hgap : 0 < gap)
    (hq : ∀ ψ : H, ‖ψ‖ = 1 →
      mu + gap * ‖residual φ ψ‖ ^ 2 ≤ q ψ)
    (hW : ∀ x y : H, inner ℝ (W x) y = inner ℝ x (W y))
    (hb : ‖W‖ ≤ gap / 4) :
    mu + inner ℝ (W φ) φ - 2 * ‖W‖ ^ 2 / gap ≤ branchEnergy q W ∧
      branchEnergy q W ≤ mu + inner ℝ (W φ) φ := by
  letI : Nonempty (UnitVector H) := ⟨⟨φ, hφ⟩⟩
  have hpoint : ∀ ψ : UnitVector H,
      mu + inner ℝ (W φ) φ - 2 * ‖W‖ ^ 2 / gap ≤
        GroundStatePerturbation.branchRayleigh q W ψ.val := by
    intro ψ
    set a : ℝ := inner ℝ φ ψ.val
    set p : H := a • φ
    set r : H := residual φ ψ.val
    have hpdef : p = a • φ := rfl
    have hrdef : r = residual φ ψ.val := rfl
    have hdecomp : ψ.val = p + r := by
      simpa [p, r] using decomposition φ ψ.val
    have horφ : inner ℝ φ r = 0 := residual_orthogonal hφ
    have hor : inner ℝ p r = 0 := by
      rw [hpdef, real_inner_smul_left, residual_orthogonal hφ, mul_zero]
    have hnorm : ‖ψ.val‖ ^ 2 = ‖p‖ ^ 2 + ‖r‖ ^ 2 := by
      rw [hdecomp, pow_two, pow_two, pow_two]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p r hor
    have hnormψ : ‖ψ.val‖ ^ 2 = 1 := by rw [ψ.2]; ring
    have hnormp : ‖p‖ ^ 2 = a ^ 2 := by
      rw [hpdef, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hφ]
      ring
    have hqp : q p = mu * ‖p‖ ^ 2 := by
      calc
        q p = q (a • φ) := by rw [hpdef]
        _ = a ^ 2 * q φ := hqSmul a φ
        _ = a ^ 2 * mu := by rw [hqφ]
        _ = mu * ‖p‖ ^ 2 := by rw [hnormp]; ring
    have hqZero : q 0 = 0 := by
      have h := hqSmul (0 : ℝ) φ
      simpa using h
    have hqr : (mu + gap) * ‖r‖ ^ 2 ≤ q r := by
      by_cases hr : r = 0
      · simp [hr, hqZero]
      · have hne : r ≠ 0 := fun h => hr h
        have hnormr : 0 < ‖r‖ := norm_pos_iff.mpr hne
        set sr : H := (‖r‖)⁻¹ • r
        have hsrdef : sr = (‖r‖)⁻¹ • r := rfl
        have hunit : ‖sr‖ = 1 := by
          rw [hsrdef, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hnormr), inv_mul_cancel₀ hnormr.ne']
        have hres : residual φ sr = sr := by
          have hor' : inner ℝ φ sr = 0 := by
            rw [hsrdef, real_inner_smul_right, residual_orthogonal hφ, mul_zero]
          show GroundStatePerturbation.residual φ sr = sr
          unfold GroundStatePerturbation.residual
          rw [hor', zero_smul, sub_zero]
        have hunitgap := hq sr hunit
        rw [hres] at hunitgap
        have hscale : q r = ‖r‖ ^ 2 * q sr := by
          have hfactor : r = ‖r‖ • sr := by
            rw [hsrdef, smul_smul, mul_inv_cancel₀ hnormr.ne', one_smul]
          conv_lhs => rw [hfactor, hqSmul]
        rw [hscale]
        have hqle : (mu + gap) * 1 ≤ q sr := by
          rw [hunit] at hunitgap
          simpa using hunitgap
        nlinarith [sq_nonneg ‖r‖]
    have hnormW : ‖W‖ ≤ ‖W‖ := le_refl _
    have hcluster := GroundStatePerturbation.cluster_form_lower_bound
      q W mu gap ‖W‖ p r ψ.val hgap (norm_nonneg W) hb
      hW hnormW hor hdecomp (by
        rw [hdecomp, hpdef]
        exact hqGroundAdd a r horφ) hqp hqr
    have hwp : inner ℝ (W p) p = ‖p‖ ^ 2 * inner ℝ (W φ) φ := by
      have hinner : inner ℝ (W p) p = a ^ 2 * inner ℝ (W φ) φ := by
        conv_lhs => rw [hpdef]
        rw [map_smul, real_inner_smul_left, real_inner_smul_right]
        ring
      rw [← hnormp] at hinner
      exact hinner
    have hwnorm : |inner ℝ (W φ) φ| ≤ ‖W‖ := by
      have h1 : |inner ℝ (W φ) φ| ≤ ‖W φ‖ * ‖φ‖ := abs_real_inner_le_norm _ _
      have h2 : ‖W φ‖ ≤ ‖W‖ * ‖φ‖ := ContinuousLinearMap.le_opNorm W φ
      nlinarith [hφ, norm_nonneg (W φ), norm_nonneg φ]
    have hsplit : ‖p‖ ^ 2 + ‖r‖ ^ 2 = 1 := by
      linarith [hnorm, hnormψ]
    have htarget : mu + inner ℝ (W φ) φ - 2 * ‖W‖ ^ 2 / gap ≤
        mu * ‖ψ.val‖ ^ 2 + inner ℝ (W p) p -
          2 * ‖W‖ ^ 2 / gap * ‖p‖ ^ 2 +
          (gap / 2 - ‖W‖) * ‖r‖ ^ 2 := by
      rw [hnormψ, hwp]
      have hnonneg : 0 ≤ gap / 2 - 2 * ‖W‖ + 2 * ‖W‖ ^ 2 / gap := by
        have hkey : (gap - 2 * ‖W‖) ^ 2 =
            2 * gap * (gap / 2 - 2 * ‖W‖ + 2 * ‖W‖ ^ 2 / gap) := by
          field_simp [hgap.ne']
          ring
        have := sq_nonneg (gap - 2 * ‖W‖)
        nlinarith [hkey, hgap]
      have hcoef : 0 ≤ gap / 2 - ‖W‖ - inner ℝ (W φ) φ +
          2 * ‖W‖ ^ 2 / gap := by
        nlinarith [(abs_le.mp hwnorm).2, hnonneg]
      nlinarith [hsplit, hcoef]
    exact htarget.trans hcluster
  constructor
  · exact le_ciInf hpoint
  · have hbdd : BddBelow
        (Set.range fun ψ : UnitVector H =>
          GroundStatePerturbation.branchRayleigh q W ψ.val) := by
      refine ⟨mu + inner ℝ (W φ) φ - 2 * ‖W‖ ^ 2 / gap, ?_⟩
      intro x hx
      obtain ⟨ψ, rfl⟩ := hx
      exact hpoint ψ
    let ψ0 : UnitVector H := ⟨φ, hφ⟩
    have hqφ' : GroundStatePerturbation.branchRayleigh q W ψ0.val =
        mu + inner ℝ (W φ) φ := by
      simp [ψ0, hqφ]
    calc
      branchEnergy q W ≤
          GroundStatePerturbation.branchRayleigh q W ψ0.val :=
        ciInf_le hbdd ψ0
      _ = mu + inner ℝ (W φ) φ := hqφ'

/-- Unit vectors orthogonal to the normalized ground state.  The constrained
Rayleigh infimum over this set is the second branch slot used in the paper's
within-branch estimate. -/
def OrthogonalUnitVector (φ : H) : Type _ :=
  {ψ : UnitVector H // inner ℝ φ ψ.val = 0}

open Classical in
/-- The second constrained Rayleigh energy of a branch.  If the orthogonal
unit sphere is empty, the supplied `lower` value is used as a conservative
fallback so the lower-bound theorem remains valid in degenerate spaces. -/
noncomputable def branchSecondEnergy (lower : ℝ) (φ : H) (q : H → ℝ)
    (W : H →L[ℝ] H) : ℝ :=
  if h : Nonempty (OrthogonalUnitVector φ) then
    ⨅ ψ : OrthogonalUnitVector φ,
      q ψ.val.val + inner ℝ (W ψ.val.val) ψ.val.val
  else lower

/-- The within-branch second-energy estimate used for equation
`eq:two-well-third-level`: every unit vector orthogonal to `φ` has energy at
least `mu + gap - ‖W‖`. -/
theorem branchSecondEnergy_lower (lower mu gap : ℝ) (φ : H)
    (q : H → ℝ) (W : H →L[ℝ] H)
    (hφ : ‖φ‖ = 1) (hgap : 0 < gap)
    (hq : ∀ ψ : H, ‖ψ‖ = 1 →
      mu + gap * ‖residual φ ψ‖ ^ 2 ≤ q ψ)
    (hb : ‖W‖ ≤ gap / 4)
    (hf : mu + 3 * gap / 4 ≤ lower) :
    mu + 3 * gap / 4 ≤ branchSecondEnergy lower φ q W := by
  have hbound : mu + 3 * gap / 4 ≤ mu + gap - ‖W‖ := by nlinarith [hb, hgap]
  unfold branchSecondEnergy
  split_ifs with h
  · apply le_ciInf
    intro ψ
    have hψ : ‖ψ.val.val‖ = 1 := ψ.val.2
    have him : inner ℝ φ ψ.val.val = 0 := ψ.2
    have hres : residual φ ψ.val.val = ψ.val.val := by
      calc
        residual φ ψ.val.val =
            ψ.val.val - inner ℝ φ ψ.val.val • φ := rfl
        _ = ψ.val.val - (0 : ℝ) • φ := by rw [him]
        _ = ψ.val.val := by simp
    have hqψ : mu + gap ≤ q ψ.val.val := by
      have h := hq ψ.val.val hψ
      rw [hres] at h
      simpa [hψ, pow_two] using h
    have hinner : -‖W‖ ≤ inner ℝ (W ψ.val.val) ψ.val.val := by
      have habs := abs_real_inner_le_norm (W ψ.val.val) ψ.val.val
      have hop := ContinuousLinearMap.le_opNorm W ψ.val.val
      have hnorm : 0 ≤ ‖ψ.val.val‖ := norm_nonneg _
      have hcalc : |inner ℝ (W ψ.val.val) ψ.val.val| ≤ ‖W‖ := by
        calc
          |inner ℝ (W ψ.val.val) ψ.val.val| ≤
              ‖W ψ.val.val‖ * ‖ψ.val.val‖ := habs
          _ ≤ ‖W‖ * ‖ψ.val.val‖ * ‖ψ.val.val‖ :=
            mul_le_mul_of_nonneg_right hop hnorm
          _ = ‖W‖ := by rw [hψ]; ring
      exact (abs_le.mp hcalc).1
    nlinarith [hqψ, hinner]
  · exact hf

/-- The first two eigenvalue slots in equation `eq:branches`, with the higher
spectral data kept explicit after the constrained third slot. -/
noncomputable def twoWellLambda
    (lower : ℝ) (φ : H) (q : H → ℝ) (cross : ℝ → SymmetricCrossPairing H)
    (higher : ℝ → ℕ → ℝ) : ℝ → ℕ → ℝ :=
  fun L n =>
    match n with
    | 0 => branchEnergy q ((cross L).operator)
    | 1 => branchEnergy q (-(cross L).operator)
    | 2 => min
        (branchSecondEnergy lower φ q ((cross L).operator))
        (branchSecondEnergy lower φ q (-(cross L).operator))
    | k + 3 => higher L k

/-- The analytic input that remains to be constructed for the restricted
fractional Laplacian.  Every field is a statement from the paper's two-well
proof, and the fields are hypotheses rather than axioms. -/
structure TwoWellSpectralInput (A : TwoWellConstants)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] where
  q : H → ℝ
  cross : ℝ → SymmetricCrossPairing H
  φ : H
  higher : ℝ → ℕ → ℝ
  hφ : ‖φ‖ = 1
  hqφ : q φ = A.mu1
  hqGroundAdd : ∀ (t : ℝ) (r : H), inner ℝ φ r = 0 →
    q (t • φ + r) = q (t • φ) + q r
  hqHomogeneous : ∀ (t : ℝ) (x : H), q (t • x) = t ^ 2 * q x
  hgapq : ∀ ψ : H, ‖ψ‖ = 1 →
    A.mu1 + A.gap * ‖residual φ ψ‖ ^ 2 ≤ q ψ
  hBnorm : ∀ L : ℝ, A.L0 ≤ L → ‖(cross L).operator‖ ≤ A.beta L
  htApprox : ∀ L : ℝ, A.L0 ≤ L →
    |inner ℝ ((cross L).operator φ) φ +
      A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| ≤
      A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)
namespace TwoWellSpectralInput

variable {A : TwoWellConstants}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The branch perturbation operator associated with the supplied cross
pairing. -/
noncomputable def B (S : TwoWellSpectralInput A H) : ℝ → H →L[ℝ] H :=
  fun L => (S.cross L).operator

/-- The diagonal branch coefficient `t_L = <phi, B_L phi>`. -/
noncomputable def t (S : TwoWellSpectralInput A H) : ℝ → ℝ :=
  fun L => inner ℝ ((S.cross L).operator S.φ) S.φ

/-- The eigenvalue sequence whose first two entries are the branch ground
energies and whose third entry is the constrained within-branch second
energy. -/
noncomputable def lambda (S : TwoWellSpectralInput A H) : ℝ → ℕ → ℝ :=
  twoWellLambda (A.mu1 + 3 * A.gap / 4) S.φ S.q S.cross S.higher

/-- The third-level lower bound in equation `eq:two-well-third-level`, from
the constrained second-energy estimate for both branches. -/
theorem third_level_lower (S : TwoWellSpectralInput A H)
    (L : ℝ) (hL : A.L0 ≤ L) :
    A.mu1 + 3 * A.gap / 4 ≤
      twoWellLambda (A.mu1 + 3 * A.gap / 4) S.φ S.q S.cross S.higher L 2 := by
  have hgap : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  have hsmall : A.beta L ≤ A.gap / 4 := TwoWellConstants.beta_small A hL
  have hplus := branchSecondEnergy_lower
    (A.mu1 + 3 * A.gap / 4) A.mu1 A.gap S.φ S.q (S.B L)
    S.hφ hgap S.hgapq ((S.hBnorm L hL).trans hsmall)
    (le_refl _)
  have hbneg : ‖-(S.B L)‖ ≤ A.gap / 4 := by
    rw [norm_neg]
    exact (S.hBnorm L hL).trans hsmall
  have hminus := branchSecondEnergy_lower
    (A.mu1 + 3 * A.gap / 4) A.mu1 A.gap S.φ S.q (-(S.B L))
    S.hφ hgap S.hgapq hbneg (le_refl _)
  have h2 : twoWellLambda (A.mu1 + 3 * A.gap / 4) S.φ S.q S.cross S.higher L 2 =
      min (branchSecondEnergy (A.mu1 + 3 * A.gap / 4) S.φ S.q (S.B L))
        (branchSecondEnergy (A.mu1 + 3 * A.gap / 4) S.φ S.q (-(S.B L))) := by
    simp only [twoWellLambda, TwoWellSpectralInput.B]
  rw [h2]
  exact le_min hplus hminus

/-- The third-level separation in equation `eq:two-well-third-level`, derived
from the third-level lower bound and the negative-branch ground-energy upper
bound.  The latter follows from the branch perturbation estimate and
`TwoWellConstants.beta_small`. -/
theorem third_level_gap (S : TwoWellSpectralInput A H)
    (L : ℝ) (hL : A.L0 ≤ L) :
    A.gap / 2 ≤
      twoWellLambda (A.mu1 + 3 * A.gap / 4) S.φ S.q S.cross S.higher L 2 -
        twoWellLambda (A.mu1 + 3 * A.gap / 4) S.φ S.q S.cross S.higher L 1 := by
  have hgap : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  have hsmall : A.beta L ≤ A.gap / 4 := TwoWellConstants.beta_small A hL
  have hbneg : ‖-(S.B L)‖ ≤ A.gap / 4 := by
    rw [norm_neg]
    exact (S.hBnorm L hL).trans hsmall
  have hWneg : ∀ x y : H,
      inner ℝ ((-(S.B L)) x) y = inner ℝ x ((-(S.B L)) y) := by
    intro x y
    simp only [neg_apply, inner_neg_left, inner_neg_right,
      TwoWellSpectralInput.B, SymmetricCrossPairing.operator_symm]
  have hminus := branch_energy_bounds S.φ S.q A.mu1 A.gap (-(S.B L))
    S.hφ S.hqφ S.hqGroundAdd S.hqHomogeneous hgap S.hgapq
    hWneg hbneg
  have hinner : |inner ℝ ((S.B L) S.φ) S.φ| ≤ ‖S.B L‖ := by
    have h1 := abs_real_inner_le_norm ((S.B L) S.φ) S.φ
    have h2 := ContinuousLinearMap.le_opNorm (S.B L) S.φ
    have hφ : 0 ≤ ‖S.φ‖ := norm_nonneg S.φ
    have hmul : ‖(S.B L) S.φ‖ * ‖S.φ‖ ≤
        ‖S.B L‖ * ‖S.φ‖ * ‖S.φ‖ :=
      mul_le_mul_of_nonneg_right h2 hφ
    calc
      |inner ℝ ((S.B L) S.φ) S.φ| ≤ ‖(S.B L) S.φ‖ * ‖S.φ‖ := h1
      _ ≤ ‖S.B L‖ * ‖S.φ‖ * ‖S.φ‖ := hmul
      _ = ‖S.B L‖ := by rw [S.hφ]; ring
  have ht : |inner ℝ ((S.B L) S.φ) S.φ| ≤ A.gap / 4 :=
    hinner.trans ((S.hBnorm L hL).trans hsmall)
  have h1 : twoWellLambda (A.mu1 + 3 * A.gap / 4) S.φ S.q S.cross S.higher L 1 =
      branchEnergy S.q (-(S.B L)) := by
    simp only [twoWellLambda, TwoWellSpectralInput.B]
  have hupper : branchEnergy S.q (-(S.B L)) ≤ A.mu1 + A.gap / 4 := by
    have h := hminus.2
    have hneg : inner ℝ ((-(S.B L)) S.φ) S.φ =
        -inner ℝ ((S.B L) S.φ) S.φ := by
      rw [neg_apply, inner_neg_left]
    rw [hneg] at h
    nlinarith [h, (abs_le.mp ht).1, (abs_le.mp ht).2]
  have h2 := S.third_level_lower L hL
  rw [h1]
  nlinarith [h2, hupper, hgap]

end TwoWellSpectralInput

/-- The normalized limiting-gap estimate in equation `eq:gap-limit`.  The
branch energies are written with explicit remainders so that the limit proof
uses one exact real-arithmetic decomposition. -/
theorem twoWellGapLimit_of_branchErrors
    (A : TwoWellConstants)
    (lambda : ℝ → ℕ → ℝ) (t rPlus rMinus : ℝ → ℝ)
    (hbranchPlus : ∀ L : ℝ, lambda L 0 = A.mu1 + t L + rPlus L)
    (hbranchMinus : ∀ L : ℝ, lambda L 1 = A.mu1 - t L + rMinus L)
    (hremainders : ∀ L : ℝ, A.L0 ≤ L →
      |rPlus L| ≤ 2 * A.beta L ^ 2 / A.gap ∧
      |rMinus L| ≤ 2 * A.beta L ^ 2 / A.gap)
    (htApprox : ∀ L : ℝ, A.L0 ≤ L →
      |t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| ≤
        A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)) :
    A.gapLimit lambda := by
  have hkappa : 0 < A.kappa := A.kappa_pos
  have hgap : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  have hLpos : ∀ L : ℝ, A.L0 ≤ L → 0 < L := by
    intro L hL
    have hL0 : 0 < A.L0 := by
      have h : (0:ℝ) < 4 * A.R := by nlinarith [A.hR]
      exact lt_of_lt_of_le h (le_max_left _ _)
    exact lt_of_lt_of_le hL0 hL
  have hpowOne : ∀ L : ℝ, 0 < L → L ^ A.kappa * L ^ (-A.kappa) = 1 := by
    intro L hL
    rw [← Real.rpow_add hL, add_neg_cancel]
    exact Real.rpow_zero L
  have hgapError : ∀ L : ℝ, A.L0 ≤ L →
      |L ^ A.kappa * (lambda L 1 - lambda L 0) -
        2 * A.c * A.phiMass ^ 2| ≤
        4 * L ^ A.kappa * A.beta L ^ 2 / A.gap +
          2 * L ^ A.kappa *
            (A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)) := by
    intro L hL
    have hLpos' := hLpos L hL
    have hr := hremainders L hL
    have ht := htApprox L hL
    have hmain :
        L ^ A.kappa * (lambda L 1 - lambda L 0) -
          2 * A.c * A.phiMass ^ 2 =
          L ^ A.kappa * (rMinus L - rPlus L) -
            2 * L ^ A.kappa *
              (t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa)) := by
      rw [hbranchPlus L, hbranchMinus L]
      have hpow : L ^ A.kappa * A.c * A.phiMass ^ 2 * L ^ (-A.kappa) =
          A.c * A.phiMass ^ 2 := by
        calc
          L ^ A.kappa * A.c * A.phiMass ^ 2 * L ^ (-A.kappa) =
              A.c * A.phiMass ^ 2 * (L ^ A.kappa * L ^ (-A.kappa)) := by
            ring
          _ = A.c * A.phiMass ^ 2 * 1 := by
            rw [hpowOne L hLpos']
          _ = A.c * A.phiMass ^ 2 := by
            ring
      nlinarith [hpow]
    rw [hmain]
    have hsum : |L ^ A.kappa * (rMinus L - rPlus L) -
        2 * L ^ A.kappa * (t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤
        |L ^ A.kappa * (rMinus L - rPlus L)| +
          |2 * L ^ A.kappa * (t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| :=
      abs_sub _ _
    have hbranch : |L ^ A.kappa * (rMinus L - rPlus L)| ≤
        4 * L ^ A.kappa * A.beta L ^ 2 / A.gap := by
      have htri : |rMinus L - rPlus L| ≤ |rMinus L| + |rPlus L| :=
        abs_sub _ _
      have hsumRem : |rMinus L| + |rPlus L| ≤
          4 * A.beta L ^ 2 / A.gap := by
        refine le_trans (add_le_add hr.2 hr.1) (le_of_eq ?_)
        ring
      calc
        |L ^ A.kappa * (rMinus L - rPlus L)| =
            L ^ A.kappa * |rMinus L - rPlus L| := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hLpos') _)]
        _ ≤ L ^ A.kappa * (|rMinus L| + |rPlus L|) :=
          mul_le_mul_of_nonneg_left htri (Real.rpow_nonneg (le_of_lt hLpos') _)
        _ ≤ L ^ A.kappa * (4 * A.beta L ^ 2 / A.gap) :=
          mul_le_mul_of_nonneg_left hsumRem (Real.rpow_nonneg (le_of_lt hLpos') _)
        _ = 4 * L ^ A.kappa * A.beta L ^ 2 / A.gap := by ring
    have hkernel : |2 * L ^ A.kappa *
        (t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤
        2 * L ^ A.kappa *
          (A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)) := by
      have h2 : 0 ≤ 2 * L ^ A.kappa :=
        mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hLpos') _)
      rw [abs_mul, abs_of_nonneg h2]
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    exact le_trans hsum (add_le_add hbranch hkernel)
  have herrorTendsto :
      Filter.Tendsto
        (fun L : ℝ =>
          4 * L ^ A.kappa * A.beta L ^ 2 / A.gap +
            2 * L ^ A.kappa *
              (A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)))
        Filter.atTop (nhds 0) := by
    have hb : ∀ L : ℝ, 0 < L →
        L ^ A.kappa * A.beta L ^ 2 =
          (A.c * (2:ℝ) ^ A.kappa * A.volumeD) ^ 2 * L ^ (-A.kappa) := by
      intro L hL
      have hbeta : A.beta L =
          A.c * (2:ℝ) ^ A.kappa * A.volumeD * L ^ (-A.kappa) := by
        simp [TwoWellConstants.beta]
      have hpow : L ^ A.kappa * (L ^ (-A.kappa)) ^ 2 = L ^ (-A.kappa) := by
        rw [pow_two, ← mul_assoc, hpowOne L hL, one_mul]
      set C : ℝ := A.c * (2:ℝ) ^ A.kappa * A.volumeD
      calc
        L ^ A.kappa * A.beta L ^ 2
            = L ^ A.kappa * (C * L ^ (-A.kappa)) ^ 2 := by
          rw [hbeta]
        _ = C ^ 2 * (L ^ A.kappa * (L ^ (-A.kappa)) ^ 2) := by
          rw [mul_pow]
          ring
        _ = C ^ 2 * L ^ (-A.kappa) := by
          rw [hpow]
    have hbetaTendsto : Filter.Tendsto
        (fun L : ℝ => 4 * L ^ A.kappa * A.beta L ^ 2 / A.gap)
        Filter.atTop (nhds 0) := by
      refine Filter.Tendsto.congr'
        (f₁ := fun L =>
          4 * (A.c * (2:ℝ) ^ A.kappa * A.volumeD) ^ 2 * L ^ (-A.kappa) / A.gap)
        ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with L hL
        have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
        calc
          4 * (A.c * (2:ℝ) ^ A.kappa * A.volumeD) ^ 2 * L ^ (-A.kappa) / A.gap
              = 4 * (L ^ A.kappa * A.beta L ^ 2) / A.gap := by
            rw [hb L hLpos]
            apply congrArg (fun w => w / A.gap)
            exact mul_assoc 4 _ _
          _ = 4 * L ^ A.kappa * A.beta L ^ 2 / A.gap := by
            apply congrArg (fun w => w / A.gap)
            exact (mul_assoc 4 _ _).symm
      · have h := (tendsto_rpow_neg_atTop hkappa).const_mul
          (4 * (A.c * (2:ℝ) ^ A.kappa * A.volumeD) ^ 2 / A.gap)
        simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h
    have hkTendsto : Filter.Tendsto
        (fun L : ℝ => 2 * L ^ A.kappa *
          (A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)))
        Filter.atTop (nhds 0) := by
      refine Filter.Tendsto.congr'
        (f₁ := fun L =>
          2 * A.c * A.C * A.phiMass ^ 2 * L ^ (-2:ℝ)) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with L hL
        have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
        have hpow : L ^ A.kappa * L ^ (-A.kappa - 2) = L ^ (-2:ℝ) := by
          rw [← Real.rpow_add hLpos]
          congr 1
          ring
        calc
          2 * A.c * A.C * A.phiMass ^ 2 * L ^ (-2:ℝ)
              = 2 * (A.c * A.C * A.phiMass ^ 2) *
                (L ^ A.kappa * L ^ (-A.kappa - 2)) := by
            rw [← hpow]
            ring
          _ = 2 * L ^ A.kappa *
                (A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)) := by
            ring
      · have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 2)).const_mul
          (2 * A.c * A.C * A.phiMass ^ 2)
        simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h
    simpa using hbetaTendsto.add hkTendsto
  have hzero : Filter.Tendsto
      (fun L : ℝ => |L ^ A.kappa * (lambda L 1 - lambda L 0) -
        2 * A.c * A.phiMass ^ 2|) Filter.atTop (nhds 0) := by
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ herrorTendsto
    filter_upwards [Filter.eventually_ge_atTop A.L0] with L hL
    exact hgapError L hL
  have hconst : Filter.Tendsto
      (fun _ : ℝ => 2 * A.c * A.phiMass ^ 2) Filter.atTop
      (nhds (2 * A.c * A.phiMass ^ 2)) :=
    tendsto_const_nhds
  have hsum : Filter.Tendsto
      (fun L : ℝ =>
        (L ^ A.kappa * (lambda L 1 - lambda L 0) - 2 * A.c * A.phiMass ^ 2) +
          2 * A.c * A.phiMass ^ 2)
      Filter.atTop (nhds (2 * A.c * A.phiMass ^ 2)) := by
    have herror : Filter.Tendsto
        (fun L : ℝ => L ^ A.kappa * (lambda L 1 - lambda L 0) -
          2 * A.c * A.phiMass ^ 2) Filter.atTop (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero _).2 hzero
    simpa [zero_add] using herror.add hconst
  simpa [TwoWellConstants.gapLimit, sub_add_cancel] using hsum

/-- Equation `eq:gap-limit`, derived from the two branch stability estimates
and the diagonal approximation for `t_L`. -/
theorem FinalTheorem (A : TwoWellConstants)
    (S : TwoWellSpectralInput A H) : A.twoWellStatement S.lambda := by
  have hBsym : ∀ (L : ℝ) (x y : H), inner ℝ (S.B L x) y = inner ℝ x (S.B L y) := by
    intro L x y
    exact SymmetricCrossPairing.operator_symm _ x y
  have hgap : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  have hLpos : ∀ L : ℝ, A.L0 ≤ L → 0 < L := by
    intro L hL
    have hL0 : 0 < A.L0 := by
      have h : (0:ℝ) < 4 * A.R := by nlinarith [A.hR]
      exact lt_of_lt_of_le h (le_max_left _ _)
    exact lt_of_lt_of_le hL0 hL
  constructor
  · intro L hL
    have hL0 := hLpos L hL
    have hsmall : A.beta L ≤ A.gap / 4 := TwoWellConstants.beta_small A hL
    have hbneg : ‖-(S.B L)‖ ≤ A.gap / 4 := by
      rw [norm_neg]
      exact (S.hBnorm L hL).trans hsmall
    have hWneg : ∀ x y : H,
        inner ℝ (-(S.B L) x) y = inner ℝ x (-(S.B L) y) := by
      intro x y
      simp [hBsym L x y]
    have hplus := branch_energy_bounds S.φ S.q A.mu1 A.gap (S.B L)
      S.hφ S.hqφ S.hqGroundAdd S.hqHomogeneous hgap S.hgapq
      (hBsym L)
      ((S.hBnorm L hL).trans hsmall)
    have hminus := branch_energy_bounds S.φ S.q A.mu1 A.gap (-(S.B L))
      S.hφ S.hqφ S.hqGroundAdd S.hqHomogeneous hgap S.hgapq
      hWneg hbneg
    have hbnn : 0 ≤ A.beta L :=
      TwoWellConstants.beta_nonneg A (hLpos L hL).le
    have hstabPlus : |branchEnergy S.q (S.B L) - (A.mu1 + S.t L)| ≤
        2 * A.beta L ^ 2 / A.gap := by
      have hlo := hplus.1
      have hhi := hplus.2
      have hsq : ‖S.B L‖ ^ 2 ≤ A.beta L ^ 2 := by
        refine sq_le_sq.mpr ?_
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hbnn]
        exact S.hBnorm L hL
      have hle : 2 * ‖S.B L‖ ^ 2 / A.gap ≤ 2 * A.beta L ^ 2 / A.gap := by
        exact div_le_div_of_nonneg_right (by nlinarith [hsq]) hgap.le
      have habs : |branchEnergy S.q (S.B L) -
          (A.mu1 + inner ℝ (S.B L S.φ) S.φ)| ≤ 2 * ‖S.B L‖ ^ 2 / A.gap := by
        apply abs_le.mpr
        constructor <;> nlinarith [hlo, hhi]
      exact habs.trans hle
    have hstabMinus : |branchEnergy S.q (-(S.B L)) - (A.mu1 - S.t L)| ≤
        2 * A.beta L ^ 2 / A.gap := by
      have hlo : A.mu1 - inner ℝ ((S.B L) S.φ) S.φ -
          2 * ‖-(S.B L)‖ ^ 2 / A.gap ≤ branchEnergy S.q (-(S.B L)) := by
        simpa [neg_apply, inner_neg_left, sub_eq_add_neg] using hminus.1
      have hhi : branchEnergy S.q (-(S.B L)) ≤
          A.mu1 - inner ℝ ((S.B L) S.φ) S.φ := by
        simpa [neg_apply, inner_neg_left, sub_eq_add_neg] using hminus.2
      have hsq : ‖-(S.B L)‖ ^ 2 ≤ A.beta L ^ 2 := by
        rw [norm_neg]
        refine sq_le_sq.mpr ?_
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hbnn]
        exact S.hBnorm L hL
      have hle : 2 * ‖-(S.B L)‖ ^ 2 / A.gap ≤ 2 * A.beta L ^ 2 / A.gap := by
        exact div_le_div_of_nonneg_right (by nlinarith [hsq]) hgap.le
      have habs : |branchEnergy S.q (-(S.B L)) -
          (A.mu1 - inner ℝ (S.B L S.φ) S.φ)| ≤ 2 * ‖-(S.B L)‖ ^ 2 / A.gap := by
        apply abs_le.mpr
        constructor <;> nlinarith [hlo, hhi]
      exact habs.trans hle
    have hk : |S.t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| ≤
        A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) := by
      show |inner ℝ ((S.cross L).operator S.φ) S.φ +
        A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| ≤
        A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)
      exact S.htApprox L hL
    have hremPlus : |branchEnergy S.q (S.B L) -
        (A.mu1 - A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤ A.remainder L := by
      have htriangle : |branchEnergy S.q (S.B L) -
          (A.mu1 - A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤
          |branchEnergy S.q (S.B L) - (A.mu1 + S.t L)| +
            |S.t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| := by
        calc
          |branchEnergy S.q (S.B L) -
              (A.mu1 - A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| =
              |(branchEnergy S.q (S.B L) - (A.mu1 + S.t L)) +
                (S.t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| := by
            congr 1
            ring
          _ ≤ |branchEnergy S.q (S.B L) - (A.mu1 + S.t L)| +
              |S.t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| :=
            abs_add_le _ _
      refine htriangle.trans ?_
      have hsum := add_le_add hstabPlus hk
      simpa [TwoWellConstants.remainder, add_comm, add_left_comm,
        add_assoc] using hsum
    have hremMinus : |branchEnergy S.q (-(S.B L)) -
        (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤ A.remainder L := by
      have hshift : |-S.t L - A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| =
          |S.t L + A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| := by
        rw [← abs_neg]
        congr 1
        have hcross := scalar_crossTerm (S.t L) (A.c * A.phiMass ^ 2 * L ^ (-A.kappa))
        nlinarith [hcross]
      have htriangle : |branchEnergy S.q (-(S.B L)) -
          (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤
          |branchEnergy S.q (-(S.B L)) - (A.mu1 - S.t L)| +
            |-S.t L - A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| := by
        calc
          |branchEnergy S.q (-(S.B L)) -
              (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| =
              |(branchEnergy S.q (-(S.B L)) - (A.mu1 - S.t L)) +
                (-S.t L - A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| := by
            congr 1
            ring
          _ ≤ |branchEnergy S.q (-(S.B L)) - (A.mu1 - S.t L)| +
              |-S.t L - A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| :=
            abs_add_le _ _
      rw [hshift] at htriangle
      refine htriangle.trans ?_
      have hsum := add_le_add hstabMinus hk
      simpa [TwoWellConstants.remainder, add_comm, add_left_comm,
        add_assoc] using hsum
    refine ⟨?_, ?_, S.third_level_lower L hL, S.third_level_gap L hL⟩
    · show |branchEnergy S.q (S.B L) -
        (A.mu1 - A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤ A.remainder L
      simp only [TwoWellSpectralInput.lambda, twoWellLambda,
        TwoWellSpectralInput.B]
      exact hremPlus
    · show |branchEnergy S.q (-(S.B L)) -
        (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤ A.remainder L
      simp only [TwoWellSpectralInput.lambda, twoWellLambda,
        TwoWellSpectralInput.B]
      exact hremMinus
  · refine twoWellGapLimit_of_branchErrors A S.lambda S.t
      (fun L => branchEnergy S.q (S.B L) - (A.mu1 + S.t L))
      (fun L => branchEnergy S.q (-(S.B L)) - (A.mu1 - S.t L))
      ?_ ?_ ?_ ?_
    · intro L
      simp only [TwoWellSpectralInput.lambda, twoWellLambda,
        TwoWellSpectralInput.B]
      ring
    · intro L
      simp only [TwoWellSpectralInput.lambda, twoWellLambda,
        TwoWellSpectralInput.B]
      ring
    · intro L hL
      have hsmall : A.beta L ≤ A.gap / 4 := TwoWellConstants.beta_small A hL
      have hbneg : ‖-(S.B L)‖ ≤ A.gap / 4 := by
        rw [norm_neg]
        exact (S.hBnorm L hL).trans hsmall
      have hWneg : ∀ x y : H,
          inner ℝ (-(S.B L) x) y = inner ℝ x (-(S.B L) y) := by
        intro x y
        simp [hBsym L x y]
      have hplus := branch_energy_bounds S.φ S.q A.mu1 A.gap (S.B L)
        S.hφ S.hqφ S.hqGroundAdd S.hqHomogeneous hgap S.hgapq
        (hBsym L)
        ((S.hBnorm L hL).trans hsmall)
      have hminus := branch_energy_bounds S.φ S.q A.mu1 A.gap (-(S.B L))
        S.hφ S.hqφ S.hqGroundAdd S.hqHomogeneous hgap S.hgapq
        hWneg hbneg
      have hbnn : 0 ≤ A.beta L := TwoWellConstants.beta_nonneg A (hLpos L hL).le
      have hsqPlus : ‖S.B L‖ ^ 2 ≤ A.beta L ^ 2 := by
        refine sq_le_sq.mpr ?_
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hbnn]
        exact S.hBnorm L hL
      have hsqMinus : ‖-(S.B L)‖ ^ 2 ≤ A.beta L ^ 2 := by
        rw [norm_neg]
        exact hsqPlus
      have hstabPlus : |branchEnergy S.q (S.B L) - (A.mu1 + S.t L)| ≤
          2 * A.beta L ^ 2 / A.gap := by
        have habs : |branchEnergy S.q (S.B L) -
            (A.mu1 + inner ℝ (S.B L S.φ) S.φ)| ≤
            2 * ‖S.B L‖ ^ 2 / A.gap := by
          apply abs_le.mpr
          constructor <;> nlinarith [hplus.1, hplus.2]
        refine habs.trans ?_
        exact div_le_div_of_nonneg_right (by nlinarith [hsqPlus]) hgap.le
      have hstabMinus : |branchEnergy S.q (-(S.B L)) - (A.mu1 - S.t L)| ≤
          2 * A.beta L ^ 2 / A.gap := by
        have hlo : A.mu1 - inner ℝ ((S.B L) S.φ) S.φ -
            2 * ‖-(S.B L)‖ ^ 2 / A.gap ≤ branchEnergy S.q (-(S.B L)) := by
          simpa [neg_apply, inner_neg_left, sub_eq_add_neg] using hminus.1
        have hhi : branchEnergy S.q (-(S.B L)) ≤
            A.mu1 - inner ℝ ((S.B L) S.φ) S.φ := by
          simpa [neg_apply, inner_neg_left, sub_eq_add_neg] using hminus.2
        have habs : |branchEnergy S.q (-(S.B L)) -
            (A.mu1 - inner ℝ ((S.B L) S.φ) S.φ)| ≤
            2 * ‖-(S.B L)‖ ^ 2 / A.gap := by
          apply abs_le.mpr
          constructor <;> nlinarith [hlo, hhi]
        refine habs.trans ?_
        exact div_le_div_of_nonneg_right (by nlinarith [hsqMinus]) hgap.le
      exact ⟨hstabPlus, hstabMinus⟩
    · intro L hL
      exact S.htApprox L hL

/-- The coordinate linear form `ell(z)=direction dot z` in Lemma 3.2. -/
noncomputable def linearForm
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (direction : X) : X → ℝ :=
  fun z => inner ℝ direction z

noncomputable def twoWellTaylorRemainder
    (A : TwoWellConstants)
    {X : Type*} [NormedAddCommGroup X] [Module ℝ X]
    (direction : X) (linear : X → ℝ) (L : ℝ) (z : X × X) : ℝ :=
  translatedCrossKernel A.kappa ((L : ℝ) • direction) z.1 z.2 -
    L ^ (-A.kappa) -
    A.kappa * L ^ (-A.kappa - 1) * linear (z.1 + z.2)

theorem twoWellTaylorRemainder_eq
    (A : TwoWellConstants)
    {X : Type*} [NormedAddCommGroup X] [Module ℝ X]
    (direction : X) (linear : X → ℝ) (L : ℝ) (x y : X) :
    translatedCrossKernel A.kappa ((L : ℝ) • direction) x y =
      L ^ (-A.kappa) +
        A.kappa * L ^ (-A.kappa - 1) * linear (x + y) +
        twoWellTaylorRemainder A direction linear L (x, y) := by
  simp only [twoWellTaylorRemainder]
  ring

/-- The Taylor remainder factor is continuous on the compactly supported
coordinate domain used in Lemma 3.2.  The separation `L >= 4R` keeps the
translated denominator nonzero. -/
theorem twoWellTaylorRemainder_continuous
    (A : TwoWellConstants)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (direction : X) (L : ℝ)
    (hLpos : 0 < L) (hdirection : ‖direction‖ = 1)
    (hX : ∀ x : X, ‖x‖ ≤ A.R) (hL4 : 4 * A.R ≤ L) :
    Continuous
      (fun z : X × X => twoWellTaylorRemainder A direction
        (linearForm direction) L z) := by
  have hne : ∀ z : X × X,
      (L:ℝ) • direction - z.1 - z.2 ≠ 0 := by
    intro z
    have hsep := translatedCrossKernel_separation_of_mem_ball
      hdirection (hX z.1) (hX z.2) hL4
    have hpos : (0:ℝ) < L / 2 := by positivity
    intro hzero
    have hnorm : ‖(L:ℝ) • direction - z.1 - z.2‖ = 0 := by
      rw [hzero, norm_zero]
    linarith
  have hkernel : Continuous (fun z : X × X =>
      translatedCrossKernel A.kappa ((L:ℝ) • direction) z.1 z.2) := by
    refine continuous_iff_continuousAt.mpr ?_
    intro z
    have hz : (L:ℝ) • direction - z.1 - z.2 ≠ 0 := hne z
    have hcont : ContinuousAt (fun w : X × X =>
        ‖(L:ℝ) • direction - w.1 - w.2‖) z := by
      fun_prop
    refine hcont.rpow_const (p := -A.kappa) ?_
    exact Or.inl (norm_ne_zero_iff.mpr hz)
  have hlinear : Continuous (fun z : X × X =>
      linearForm direction (z.1 + z.2)) := by
    have h : Continuous (linearForm direction) := by
      unfold linearForm
      exact continuous_const.inner continuous_id
    exact h.comp (continuous_fst.add continuous_snd)
  have hcoeff : Continuous (fun z : X × X =>
      A.kappa * L ^ (-A.kappa - 1) *
        linearForm direction (z.1 + z.2)) :=
    continuous_const.mul hlinear
  exact hkernel.sub continuous_const |>.sub hcoeff

/-! The cross kernel in equation `eq:B`.  Its normalization and translation
are part of the theorem statement, rather than a free kernel field. -/
noncomputable def twoWellKernel
    (A : TwoWellConstants)
    {X : Type*} [NormedAddCommGroup X] [Module ℝ X]
    (direction : X) : ℝ → X → X → ℝ :=
  fun L x y =>
    -A.c * translatedCrossKernel A.kappa ((L : ℝ) • direction) x y

theorem twoWellKernel_symm
    (A : TwoWellConstants)
    {X : Type*} [NormedAddCommGroup X] [Module ℝ X]
    (direction : X) (L : ℝ) (x y : X) :
    twoWellKernel A direction L x y = twoWellKernel A direction L y x := by
  unfold twoWellKernel
  rw [translatedCrossKernel_swap]

/-- The product mass term is integrable because the ground state belongs to
`L²(mu)` and the measure is finite. -/
theorem l2ProductIntegrable
    {X : Type*} [MeasurableSpace X]
    {mu : MeasureTheory.Measure X} [MeasureTheory.SFinite mu]
    [MeasureTheory.IsFiniteMeasure mu]
    (φ : MeasureTheory.Lp ℝ 2 mu) :
    MeasureTheory.Integrable
      (fun z : X × X => ⇑φ z.1 * ⇑φ z.2) (mu.prod mu) := by
  have hφ : MeasureTheory.Integrable ⇑φ mu :=
    MeasureTheory.MemLp.integrable
      (q := 2) (by norm_num)
      (MeasureTheory.Lp.memLp φ)
  exact MeasureTheory.Integrable.mul_prod
    (μ := mu) (ν := mu) (f := ⇑φ) (g := ⇑φ) hφ hφ

/-- Multiplying an integrable product mass term by a bounded measurable factor
preserves integrability. -/
theorem bounded_factor_mul_integrable
    {X : Type*} [MeasurableSpace X] {mu : MeasureTheory.Measure X}
    (u v : X → ℝ) (C : ℝ)
    (hu : MeasureTheory.Integrable u mu)
    (hv : MeasureTheory.AEStronglyMeasurable v mu)
    (hb : ∀ x, |v x| ≤ C) :
    MeasureTheory.Integrable (fun x => u x * v x) mu := by
  have h : MeasureTheory.Integrable (fun x => v x * u x) mu := by
    refine MeasureTheory.Integrable.bdd_mul (g := u) (c := C) hu hv ?_
    exact Filter.Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs] using hb x)
  simpa [mul_comm] using h

/-- Measure-preserving central inversion makes negation measurable. -/
theorem measurableNeg_of_measurePreserving_neg
    {X : Type*} [MeasurableSpace X] [Neg X]
    {mu : MeasureTheory.Measure X}
    (hmu : MeasureTheory.MeasurePreserving (fun x : X => -x) mu mu) :
    MeasurableNeg X :=
  ⟨hmu.measurable⟩

/-- The first-moment cancellation in Lemma 3.2.  Central reflection
invariance of the measure and evenness of the ground state force the linear
Taylor integral to vanish. -/
theorem linear_integral_zero_of_even
    {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [SecondCountableTopology X] [OpensMeasurableSpace X]
    {mu : MeasureTheory.Measure X} [MeasureTheory.SFinite mu]
    (φ : MeasureTheory.Lp ℝ 2 mu) (direction : X)
    (heven : ∀ x : X, ⇑φ (-x) = ⇑φ x)
    (hmu : MeasureTheory.MeasurePreserving (fun x : X => -x) mu mu) :
    (∫ z : X × X, ⇑φ z.1 * ⇑φ z.2 *
      linearForm direction (z.1 + z.2) ∂(mu.prod mu)) = 0 := by
  haveI : MeasurableNeg X := measurableNeg_of_measurePreserving_neg hmu
  let e : X × X ≃ᵐ X × X :=
    (MeasurableEquiv.neg X).prodCongr (MeasurableEquiv.neg X)
  have heq : ⇑e = Prod.map (fun x : X => -x) (fun x : X => -x) := by
    funext z
    rcases z with ⟨x, y⟩
    simp [e, MeasurableEquiv.prodCongr, MeasurableEquiv.neg]
  have hprod : MeasureTheory.MeasurePreserving (⇑e) (mu.prod mu) (mu.prod mu) := by
    rw [heq]
    exact MeasureTheory.MeasurePreserving.prod hmu hmu
  set f : X × X → ℝ := fun z => ⇑φ z.1 * ⇑φ z.2 *
    linearForm direction (z.1 + z.2)
  have hchange : ∫ z, f (⇑e z) ∂(mu.prod mu) = ∫ z, f z ∂(mu.prod mu) :=
    hprod.integral_comp' f
  have hpoint : ∀ z : X × X, f (⇑e z) = - f z := by
    intro z
    rw [heq]
    rcases z with ⟨x, y⟩
    show f ((-x, -y)) = - f (x, y)
    simp only [f, linearForm, heven]
    have hxy : (-x) + (-y) = -(x + y) := by
      calc
        (-x) + (-y) = (-y) + (-x) := add_comm _ _
        _ = -(x + y) := (neg_add_rev x y).symm
    rw [hxy, inner_neg_right]
    ring
  have hneg : ∫ z, f (⇑e z) ∂(mu.prod mu) =
      - ∫ z, f z ∂(mu.prod mu) := by
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hpoint), MeasureTheory.integral_neg]
  have key : (∫ z, f z ∂(mu.prod mu)) = - ∫ z, f z ∂(mu.prod mu) :=
    hchange.symm.trans hneg
  linarith

/-- The canonical one-well Rayleigh form on `L²(mu)`, obtained by lifting the
zero-exterior Gagliardo form along the finite-energy `L²` projection. -/
noncomputable def oneWellForm
    (A : TwoWellConstants)
    (X : Type*) [MeasurableSpace X] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [SecondCountableTopology X] [OpensMeasurableSpace X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu] :
    QuadraticMap ℝ (MeasureTheory.Lp ℝ 2 mu) ℝ :=
  restrictedZeroExteriorFormLift A.c A.kappa mu Set.univ
    (gagliardoKernel_aestronglyMeasurable A.kappa mu)

theorem oneWellForm_nonneg
    (A : TwoWellConstants)
    (X : Type*) [MeasurableSpace X] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [SecondCountableTopology X] [OpensMeasurableSpace X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    (x : MeasureTheory.Lp ℝ 2 mu) :
    0 ≤ oneWellForm A X mu x := by
  exact restrictedZeroExteriorFormLift_nonneg A.c A.kappa A.hc.le mu Set.univ
    (gagliardoKernel_aestronglyMeasurable A.kappa mu) x

/-- The remaining one-well and spectral data in the two-well proof, with the
cross operator specialized to the Gagliardo `L²` kernel.  The one-well slot is
the Rayleigh energy of the associated closed form from equation `eq:form`;
the restricted fractional Laplacian itself is unbounded and is not represented
here by a bounded operator. -/
structure L2TwoWellAux (A : TwoWellConstants)
    (X : Type*) [MeasurableSpace X] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [SecondCountableTopology X] [OpensMeasurableSpace X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    [MeasureTheory.IsFiniteMeasure mu] where
  φRaw : X → ℝ
  higher : ℝ → ℕ → ℝ
  hφEnergy : finiteGagliardoEnergy A.kappa mu Set.univ φRaw
  hφNormLp : ‖finiteGagliardoEnergy.toLp A.kappa mu Set.univ φRaw hφEnergy‖ = 1
  hmassLp : ∫ x,
      ⇑(finiteGagliardoEnergy.toLp A.kappa mu Set.univ φRaw hφEnergy) x ∂mu = A.phiMass
  hφEnergySource :
    restrictedZeroExteriorForm A.c A.kappa mu Set.univ
      (gagliardoKernel_aestronglyMeasurable A.kappa mu)
      ⟨φRaw, hφEnergy⟩ = A.mu1
  honeWellPolar : ∀ (t : ℝ) (r : MeasureTheory.Lp ℝ 2 mu),
    inner ℝ
        (finiteGagliardoEnergy.toLp A.kappa mu Set.univ φRaw hφEnergy) r = 0 →
      QuadraticMap.polar (⇑(oneWellForm A X mu))
        (t • finiteGagliardoEnergy.toLp A.kappa mu Set.univ φRaw hφEnergy) r = 0
  honeWellSecond :
    orthogonalRayleighInf (⇑(oneWellForm A X mu))
      (finiteGagliardoEnergy.toLp A.kappa mu Set.univ φRaw hφEnergy) = A.mu2
  direction : X
  hdirection : ‖direction‖ = 1
  hX : ∀ x : X, ‖x‖ ≤ A.R
  hmeasure : mu.real Set.univ = A.volumeD
  heven : ∀ x : X,
    ⇑(finiteGagliardoEnergy.toLp A.kappa mu Set.univ φRaw hφEnergy) (-x) =
      ⇑(finiteGagliardoEnergy.toLp A.kappa mu Set.univ φRaw hφEnergy) x
  hmeasureNeg : MeasureTheory.MeasurePreserving (fun x : X => -x) mu mu
  hnonneg : ∀ x : X,
    0 ≤ ⇑(finiteGagliardoEnergy.toLp A.kappa mu Set.univ φRaw hφEnergy) x
namespace L2TwoWellAux

variable {A : TwoWellConstants}
  {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [SecondCountableTopology X] [OpensMeasurableSpace X]
  {mu : MeasureTheory.Measure X} [MeasureTheory.SFinite mu]
  [MeasureTheory.IsFiniteMeasure mu]

/-- The `L²` ground state is the representative of the finite-energy function
from equation `eq:mass`. -/
noncomputable def φ (aux : L2TwoWellAux A X mu) : MeasureTheory.Lp ℝ 2 mu :=
  finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy

/-- The `L²` ground state is the representative of the finite-energy function
from equation `eq:mass`. -/
theorem coeFn_φ_ae (aux : L2TwoWellAux A X mu) :
    ⇑aux.φ =ᵐ[mu] aux.φRaw := by
  rw [φ]
  exact (finiteGagliardoEnergy.coeFn_toLp
    A.kappa mu Set.univ aux.φRaw aux.hφEnergy).trans
      (by rw [zeroExtension_univ])

/-- Normalization in equation `eq:mass`, transported from the raw
finite-energy representative. -/
theorem hφ (aux : L2TwoWellAux A X mu) : ‖aux.φ‖ = 1 := by
  exact aux.hφNormLp

/-- The mass identity in equation `eq:mass`, transported from the raw
finite-energy representative. -/
theorem hmass (aux : L2TwoWellAux A X mu) :
    ∫ x, ⇑aux.φ x ∂mu = A.phiMass := by
  exact aux.hmassLp

/-- Compatibility of the canonical lifted form with its finite-energy source. -/
theorem hsourceForm (aux : L2TwoWellAux A X mu)
    (u : finiteGagliardoEnergySubmodule A.kappa mu Set.univ
      (gagliardoKernel_aestronglyMeasurable A.kappa mu)) :
    oneWellForm A X mu
        (finiteGagliardoEnergy.toLp A.kappa mu Set.univ u.1 u.2) =
      restrictedZeroExteriorForm A.c A.kappa mu Set.univ
        (gagliardoKernel_aestronglyMeasurable A.kappa mu) u := by
  exact restrictedZeroExteriorFormLift_apply_toLp A.c A.kappa mu Set.univ
    (gagliardoKernel_aestronglyMeasurable A.kappa mu) u

/-- The ground-state energy value is the supplied Rayleigh-form energy. -/
theorem hφEnergyFromForm (aux : L2TwoWellAux A X mu) :
    oneWellForm A X mu
        (finiteGagliardoEnergy.toLp A.kappa mu Set.univ
          aux.φRaw aux.hφEnergy) = A.mu1 := by
  exact (aux.hsourceForm ⟨aux.φRaw, aux.hφEnergy⟩).trans aux.hφEnergySource

/-- The ground-state energy value is read from the restricted zero-exterior
form in equation `eq:form`, rather than supplied as an independent equality
for the `L²` quadratic map. -/
theorem hφEnergyValue (aux : L2TwoWellAux A X mu) :
    oneWellForm A X mu
        (finiteGagliardoEnergy.toLp A.kappa mu Set.univ
          aux.φRaw aux.hφEnergy) = A.mu1 := by
  exact aux.hφEnergyFromForm

/-- The one-well Rayleigh energy represented by the associated closed form. -/
noncomputable def q (aux : L2TwoWellAux A X mu) :
    MeasureTheory.Lp ℝ 2 mu → ℝ :=
  ⇑(oneWellForm A X mu)

theorem hqφ (aux : L2TwoWellAux A X mu) :
    aux.q aux.φ = A.mu1 := by
  exact aux.hφEnergyValue

/-- The orthogonal spectral gap is the supplied Rayleigh-form estimate. -/
theorem hgapOrthFromForm (aux : L2TwoWellAux A X mu)
    (η : MeasureTheory.Lp ℝ 2 mu)
    (hη : inner ℝ
        (finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy) η = 0) :
    (A.mu1 + A.gap) * ‖η‖ ^ 2 ≤ oneWellForm A X mu η := by
  have hqsmul : ∀ (t : ℝ) (x : MeasureTheory.Lp ℝ 2 mu),
      oneWellForm A X mu (t • x) = t ^ 2 * oneWellForm A X mu x := by
    intro t x
    rw [(oneWellForm A X mu).map_smul, smul_eq_mul, pow_two]
  have hnonneg : ∀ x : MeasureTheory.Lp ℝ 2 mu, 0 ≤ oneWellForm A X mu x :=
    fun x => oneWellForm_nonneg A X mu x
  have hgapEq : A.gap = A.mu2 - A.mu1 := by
    simp [TwoWellConstants.gap]
  exact quadratic_gap_of_orthogonalRayleighInf
    (finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy)
    (⇑(oneWellForm A X mu)) A.mu1 A.mu2 A.gap
    hqsmul hnonneg aux.honeWellSecond hgapEq η hη

/-- The polar form vanishes on the ground-state line by the first-variation
identity in equation `eq:mass`. -/
theorem hgroundPolarFromSource (aux : L2TwoWellAux A X mu)
    (t : ℝ) (r : MeasureTheory.Lp ℝ 2 mu)
    (hr : inner ℝ
        (finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy) r = 0) :
    QuadraticMap.polar (⇑(oneWellForm A X mu))
      (t • finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy) r = 0 := by
  exact aux.honeWellPolar t r hr

theorem hgapOrth (aux : L2TwoWellAux A X mu)
    (η : MeasureTheory.Lp ℝ 2 mu)
    (hη : inner ℝ (finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy) η = 0) :
    (A.mu1 + A.gap) * ‖η‖ ^ 2 ≤ oneWellForm A X mu η := by
  exact aux.hgapOrthFromForm η hη

/-- The polar form vanishes on the ground-state line by the first variation of
the minimizing normalized ground state. -/
theorem hgroundPolar (aux : L2TwoWellAux A X mu)
    (t : ℝ) (r : MeasureTheory.Lp ℝ 2 mu)
    (hr : inner ℝ
        (finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy) r = 0) :
    QuadraticMap.polar (⇑(oneWellForm A X mu))
      (t • finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy) r = 0 := by
  exact aux.hgroundPolarFromSource t r hr

theorem hqEnergyHomogeneous (aux : L2TwoWellAux A X mu)
    (t : ℝ) (x : MeasureTheory.Lp ℝ 2 mu) :
    aux.q (t • x) = t ^ 2 * aux.q x := by
  show oneWellForm A X mu (t • x) = t ^ 2 * oneWellForm A X mu x
  rw [(oneWellForm A X mu).map_smul, smul_eq_mul, pow_two]

/-- Polar orthogonality on the ground-state line is exactly the source-level
cross-term cancellation in equation `eq:form`; it yields the ground-line
additivity law consumed by the spectral input. -/
theorem hqEnergyGroundAdd (aux : L2TwoWellAux A X mu)
    (t : ℝ) (r : MeasureTheory.Lp ℝ 2 mu)
    (hr : inner ℝ aux.φ r = 0) :
    aux.q (t • aux.φ + r) = aux.q (t • aux.φ) + aux.q r := by
  have hpolar := aux.hgroundPolar t r (by
    show inner ℝ (finiteGagliardoEnergy.toLp A.kappa mu Set.univ
      aux.φRaw aux.hφEnergy) r = 0
    exact hr)
  simp only [QuadraticMap.polar] at hpolar
  show oneWellForm A X mu
      (t • finiteGagliardoEnergy.toLp A.kappa mu Set.univ
        aux.φRaw aux.hφEnergy + r) =
    oneWellForm A X mu
      (t • finiteGagliardoEnergy.toLp A.kappa mu Set.univ
        aux.φRaw aux.hφEnergy) +
      oneWellForm A X mu r
  linarith [hpolar]

theorem hgapEnergy (aux : L2TwoWellAux A X mu) :
    ∀ ψ : MeasureTheory.Lp ℝ 2 mu, ‖ψ‖ = 1 →
      A.mu1 + A.gap *
        ‖residual (finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy) ψ‖ ^ 2 ≤
        oneWellForm A X mu ψ :=
  fun ψ hψ =>
    quadratic_gap_of_polar
      (finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy)
      (oneWellForm A X mu) A.mu1 A.gap
      aux.hφNormLp aux.hφEnergyValue aux.hgroundPolar aux.hgapOrth ψ hψ

/-- Global unit-sphere minimization follows from the orthogonal spectral gap
and the first-variation identity; it is no longer an independent input. -/
theorem hgroundMin (aux : L2TwoWellAux A X mu)
    (ψ : MeasureTheory.Lp ℝ 2 mu) (hψ : ‖ψ‖ = 1) :
    oneWellForm A X mu
        (finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy) ≤
      oneWellForm A X mu ψ := by
  have hgapEnergy := aux.hgapEnergy ψ hψ
  have hgapPos : 0 < A.gap := by
    simpa [TwoWellConstants.gap] using A.hgap
  have hres : 0 ≤ A.gap *
      ‖residual
        (finiteGagliardoEnergy.toLp A.kappa mu Set.univ aux.φRaw aux.hφEnergy) ψ‖ ^ 2 := by
    positivity
  linarith [aux.hφEnergyValue, hgapEnergy, hres]

theorem hgapq (aux : L2TwoWellAux A X mu) :
    ∀ ψ : MeasureTheory.Lp ℝ 2 mu, ‖ψ‖ = 1 →
      A.mu1 + A.gap * ‖residual aux.φ ψ‖ ^ 2 ≤ aux.q ψ := by
  exact aux.hgapEnergy

theorem twoWellKernel_bound (aux : L2TwoWellAux A X mu)
    {L : ℝ} (hL : A.L0 ≤ L) (x y : X) :
    |twoWellKernel A aux.direction L x y| ≤
      A.c * (2:ℝ) ^ A.kappa * L ^ (-A.kappa) := by
  have hL0 : 0 < A.L0 := by
    have h : (0:ℝ) < 4 * A.R := by nlinarith [A.hR]
    exact lt_of_lt_of_le h (le_max_left _ _)
  have hLpos : 0 < L := lt_of_lt_of_le hL0 hL
  have hkappa : 0 ≤ A.kappa := by
    rw [A.hkappa]
    have hd : (0:ℝ) ≤ (A.d : ℝ) := Nat.cast_nonneg _
    nlinarith [A.hs.1, hd]
  have hsep : (L:ℝ) / 2 ≤ ‖(L:ℝ) • aux.direction - x - y‖ := by
    have hL0bound : 4 * A.R ≤ A.L0 := le_max_left _ _
    have hL4 : 4 * A.R ≤ L := le_trans hL0bound hL
    exact translatedCrossKernel_separation_of_mem_ball
      aux.hdirection (aux.hX x) (aux.hX y) hL4
  show |-A.c *
    translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y| ≤
    A.c * 2 ^ A.kappa * L ^ (-A.kappa)
  have hbound := translatedCrossKernel_le_of_lowerBound A.kappa L
    ((L : ℝ) • aux.direction) x y hkappa hLpos hsep
  have hnonneg :
      0 ≤ translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y := by
    unfold translatedCrossKernel
    exact Real.rpow_nonneg (norm_nonneg _) _
  calc
    |-A.c * translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y| =
        A.c * translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y := by
      rw [neg_mul, abs_neg, abs_mul,
        abs_of_nonneg A.hc.le, abs_of_nonneg hnonneg]
    _ ≤ A.c * (2 ^ A.kappa * L ^ (-A.kappa)) :=
      mul_le_mul_of_nonneg_left hbound A.hc.le
    _ = A.c * 2 ^ A.kappa * L ^ (-A.kappa) := by ring

theorem twoWellKernel_aestronglyMeasurable (aux : L2TwoWellAux A X mu)
    {L : ℝ} (hL : A.L0 ≤ L) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => twoWellKernel A aux.direction L z.1 z.2)
      (mu.prod mu) := by
  have hL0 : 0 < A.L0 := by
    have h : (0:ℝ) < 4 * A.R := by nlinarith [A.hR]
    exact lt_of_lt_of_le h (le_max_left _ _)
  have hLpos : 0 < L := lt_of_lt_of_le hL0 hL
  have hsep : ∀ x y : X, (L:ℝ) / 2 ≤
      ‖(L:ℝ) • aux.direction - x - y‖ := by
    intro x y
    have hL0bound : 4 * A.R ≤ A.L0 := le_max_left _ _
    have hL4 : 4 * A.R ≤ L := le_trans hL0bound hL
    exact translatedCrossKernel_separation_of_mem_ball
      aux.hdirection (aux.hX x) (aux.hX y) hL4
  have hbase : Continuous (fun z : X × X =>
      (L:ℝ) • aux.direction - z.1 - z.2) := by
    exact continuous_const.sub continuous_fst |>.sub continuous_snd
  have hne : ∀ z : X × X,
      (‖(L:ℝ) • aux.direction - z.1 - z.2‖ : ℝ) ≠ 0 := by
    intro z
    have hpos : (0:ℝ) < L / 2 := by positivity
    have h := hsep z.1 z.2
    intro hzero
    rw [hzero] at h
    exact absurd h (not_le_of_gt hpos)
  have hnorm : Continuous (fun z : X × X =>
      ‖(L:ℝ) • aux.direction - z.1 - z.2‖) :=
    continuous_norm.comp hbase
  have hpow : Continuous (fun z : X × X =>
      (‖(L:ℝ) • aux.direction - z.1 - z.2‖ : ℝ) ^ (-A.kappa)) :=
    hnorm.rpow_const (fun z => Or.inl (hne z))
  have hcont : Continuous (fun z : X × X =>
      twoWellKernel A aux.direction L z.1 z.2) := by
    show Continuous (fun z : X × X =>
      -A.c * (‖(L:ℝ) • aux.direction - z.1 - z.2‖ : ℝ) ^ (-A.kappa))
    exact continuous_const.mul hpow
  exact hcont.aestronglyMeasurable

noncomputable def validCross (aux : L2TwoWellAux A X mu)
    {L : ℝ} (hL : A.L0 ≤ L) :
    L2CrossPairing X (twoWellKernel A aux.direction L) mu :=
  L2CrossPairing.ofKernel
    (twoWellKernel A aux.direction L)
    (A.c * (2:ℝ) ^ A.kappa * L ^ (-A.kappa))
    (by
      have hL0 : 0 < A.L0 := by
        have h : (0:ℝ) < 4 * A.R := by nlinarith [A.hR]
        exact lt_of_lt_of_le h (le_max_left _ _)
      have hLpos : 0 < L := lt_of_lt_of_le hL0 hL
      exact mul_nonneg
        (mul_nonneg A.hc.le (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg hLpos.le _))
    (twoWellKernel_bound aux hL)
    (twoWellKernel_aestronglyMeasurable aux hL)
    (twoWellKernel_symm A aux.direction L)

open Classical in
/-- The cross pairing on all separations.  On the theorem's valid range it is
the constructed `L²` kernel pairing; elsewhere it is the irrelevant zero
pairing. -/
noncomputable def cross (aux : L2TwoWellAux A X mu) (L : ℝ) :
    SymmetricCrossPairing (MeasureTheory.Lp ℝ 2 mu) :=
  if h : A.L0 ≤ L then
    L2CrossPairing.toSymmetric (validCross aux h)
  else
    SymmetricCrossPairing.zero (MeasureTheory.Lp ℝ 2 mu)

/-- The eigenvalue sequence of the L2 auxiliary data, with the first two
entries fixed by the two branch ground energies. -/
noncomputable def lambda (aux : L2TwoWellAux A X mu) : ℝ → ℕ → ℝ :=
  twoWellLambda (A.mu1 + 3 * A.gap / 4) aux.φ aux.q
    aux.cross aux.higher

/-- Build the abstract spectral input consumed by `FinalTheorem`, with all
cross-kernel fields supplied by the Gagliardo `L²` representation. -/
noncomputable def toSpectralInput (aux : L2TwoWellAux A X mu) :
    TwoWellSpectralInput A (MeasureTheory.Lp ℝ 2 mu) where
  q := aux.q
  cross := aux.cross
  φ := aux.φ
  higher := aux.higher
  hφ := aux.hφ
  hqφ := aux.hqφ
  hqGroundAdd := aux.hqEnergyGroundAdd
  hqHomogeneous := aux.hqEnergyHomogeneous
  hgapq := aux.hgapq
  hBnorm := fun L hL => by
    have hcross : aux.cross L =
        L2CrossPairing.toSymmetric (validCross aux hL) := by
      simp [L2TwoWellAux.cross, hL]
    rw [hcross]
    have hL0 : 0 < A.L0 := by
      have h : (0:ℝ) < 4 * A.R := by nlinarith [A.hR]
      exact lt_of_lt_of_le h (le_max_left _ _)
    have hLpos : 0 < L := lt_of_lt_of_le hL0 hL
    have hkappa : 0 ≤ A.kappa := by
      rw [A.hkappa]
      have hd : (0:ℝ) ≤ (A.d : ℝ) := Nat.cast_nonneg _
      nlinarith [A.hs.1, hd]
    have hsep : ∀ x y : X, L / 2 ≤ ‖(L : ℝ) • aux.direction - x - y‖ := by
      intro x y
      have hL0bound : 4 * A.R ≤ A.L0 := le_max_left _ _
      have hL4 : 4 * A.R ≤ L := le_trans hL0bound hL
      exact translatedCrossKernel_separation_of_mem_ball
        aux.hdirection (aux.hX x) (aux.hX y) hL4
    have hkernel : ∀ x y,
        |twoWellKernel A aux.direction L x y| ≤
          A.c * 2 ^ A.kappa * L ^ (-A.kappa) := by
      intro x y
      show |-A.c *
        translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y| ≤
        A.c * 2 ^ A.kappa * L ^ (-A.kappa)
      have hbound := translatedCrossKernel_le_of_lowerBound A.kappa L
        ((L : ℝ) • aux.direction) x y hkappa hLpos (hsep x y)
      have hnonneg :
          0 ≤ translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y := by
        unfold translatedCrossKernel
        exact Real.rpow_nonneg (norm_nonneg _) _
      calc
        |-A.c * translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y| =
            A.c * translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y := by
          rw [neg_mul, abs_neg, abs_mul,
            abs_of_nonneg A.hc.le, abs_of_nonneg hnonneg]
        _ ≤ A.c * (2 ^ A.kappa * L ^ (-A.kappa)) :=
          mul_le_mul_of_nonneg_left hbound A.hc.le
        _ = A.c * 2 ^ A.kappa * L ^ (-A.kappa) := by ring
    have hform : ∀ u v : MeasureTheory.Lp ℝ 2 mu,
        |kernelCrossPairing (twoWellKernel A aux.direction L) mu ⇑u ⇑v| ≤
          A.beta L * ‖u‖ * ‖v‖ := by
      intro u v
      have h := kernelCrossPairing_Lp_le
        (twoWellKernel A aux.direction L)
        (A.c * 2 ^ A.kappa * L ^ (-A.kappa))
        (by
          by_contra hneg
          have hlt : A.c * 2 ^ A.kappa * L ^ (-A.kappa) < 0 := lt_of_not_ge hneg
          have hprod : (A.c * 2 ^ A.kappa * L ^ (-A.kappa)) * A.volumeD < 0 :=
            mul_neg_of_neg_of_pos hlt A.hvolumeD
          have hbeta : A.beta L =
              (A.c * 2 ^ A.kappa * L ^ (-A.kappa)) * A.volumeD := by
            simp [TwoWellConstants.beta]
            ring
          linarith [TwoWellConstants.beta_nonneg A hLpos.le, hbeta])
            hkernel mu u v
      rw [aux.hmeasure] at h
      simpa [TwoWellConstants.beta, mul_assoc, mul_comm, mul_left_comm] using h
    exact SymmetricCrossPairing.operator_norm_le
      (L2CrossPairing.toSymmetric (validCross aux hL))
      (TwoWellConstants.beta_nonneg A hLpos.le)
      (fun u v => by
        change |(validCross aux hL).form u v| ≤ A.beta L * ‖u‖ * ‖v‖
        rw [(validCross aux hL).hform u v]
        exact hform u v)
  htApprox := fun L hL => by
    have hcross : aux.cross L =
        L2CrossPairing.toSymmetric (validCross aux hL) := by
      simp [L2TwoWellAux.cross, hL]
    rw [hcross]
    show |inner ℝ ((L2CrossPairing.toSymmetric (validCross aux hL)).operator aux.φ) aux.φ +
      A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| ≤
      A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)
    rw [L2CrossPairing.operator_inner_eq_kernelCrossPairing
      (validCross aux hL) aux.φ aux.φ]
    have hK :
        kernelCrossPairing (twoWellKernel A aux.direction L) mu ⇑aux.φ ⇑aux.φ =
          -A.c * kernelCrossPairing
            (translatedCrossKernel A.kappa ((L : ℝ) • aux.direction))
            mu ⇑aux.φ ⇑aux.φ := by
      show kernelCrossPairing
        (fun x y => -A.c *
          translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y)
        mu ⇑aux.φ ⇑aux.φ =
          -A.c * kernelCrossPairing
            (translatedCrossKernel A.kappa ((L : ℝ) • aux.direction))
            mu ⇑aux.φ ⇑aux.φ
      exact kernelCrossPairing_const_mul_kernel (-A.c)
        (translatedCrossKernel A.kappa ((L : ℝ) • aux.direction))
        mu ⇑aux.φ ⇑aux.φ
    have hLpos : 0 < L := lt_of_lt_of_le
      (show (0:ℝ) < A.L0 from by
        have h : (0:ℝ) < 4 * A.R := by nlinarith [A.hR]
        exact lt_of_lt_of_le h (le_max_left _ _)) hL
    have hlineDeriv : ∀ x y : X,
        derivWithin
          (translatedCrossLine A.kappa ((L : ℝ) • aux.direction) x y)
          (Set.Icc (0:ℝ) 1) 0 =
          A.kappa * L ^ (-A.kappa - 1) *
            linearForm aux.direction (x + y) := by
      intro x y
      have hcenter : (L:ℝ) • aux.direction ≠ 0 := by
        intro hzero
        have hnorm : ‖(L:ℝ) • aux.direction‖ = 0 := by
          rw [hzero, norm_zero]
        rw [norm_smul, Real.norm_eq_abs, aux.hdirection, mul_one,
          abs_of_pos hLpos] at hnorm
        exact hLpos.ne hnorm.symm
      have hderiv := translatedCrossLine_hasDerivAt_zero A.kappa
        ((L:ℝ) • aux.direction) x y hcenter
      have hunique : UniqueDiffWithinAt ℝ (Set.Icc (0:ℝ) 1) 0 :=
        (uniqueDiffOn_Icc (show (0:ℝ) < 1 by norm_num)).uniqueDiffWithinAt
          (by simp)
      refine (hderiv.hasDerivWithinAt.derivWithin hunique).trans ?_
      rw [norm_smul, Real.norm_eq_abs, aux.hdirection, mul_one,
        abs_of_pos hLpos, real_inner_smul_left]
      have hpow : L ^ (-A.kappa - 2) * L = L ^ (-A.kappa - 1) := by
        rw [← Real.rpow_add_one (ne_of_gt hLpos) (-A.kappa - 2)]
        congr 1
        ring
      calc
        A.kappa * L ^ (-A.kappa - 2) *
            (L * inner ℝ aux.direction (x + y))
            = A.kappa * (L ^ (-A.kappa - 2) * L) *
              inner ℝ aux.direction (x + y) := by ring
        _ = A.kappa * L ^ (-A.kappa - 1) *
              inner ℝ aux.direction (x + y) := by
          rw [hpow]
        _ = A.kappa * L ^ (-A.kappa - 1) *
              linearForm aux.direction (x + y) := rfl
    have hkappa : 0 ≤ A.kappa := by
      rw [A.hkappa]
      have hd : (0:ℝ) ≤ (A.d : ℝ) := Nat.cast_nonneg _
      nlinarith [A.hs.1, hd]
    have hL4 : 4 * A.R ≤ L :=
      le_trans (le_max_left _ _) hL
    have hlineNonzero : ∀ (x y : X), ∀ t ∈ Set.Icc (0:ℝ) 1,
        (L:ℝ) • aux.direction - (t:ℝ) • (x + y) ≠ 0 := by
      intro x y t ht
      have hxt : ‖(t:ℝ) • x‖ ≤ A.R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc
          (t:ℝ) * ‖x‖ ≤ 1 * A.R :=
            mul_le_mul ht.2 (aux.hX x) (norm_nonneg x) zero_le_one
          _ = A.R := by ring
      have hyt : ‖(t:ℝ) • y‖ ≤ A.R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc
          (t:ℝ) * ‖y‖ ≤ 1 * A.R :=
            mul_le_mul ht.2 (aux.hX y) (norm_nonneg y) zero_le_one
          _ = A.R := by ring
      have hsep : (L:ℝ) / 2 ≤
          ‖(L:ℝ) • aux.direction - (t:ℝ) • x - (t:ℝ) • y‖ :=
        translatedCrossKernel_separation_of_mem_ball
          aux.hdirection hxt hyt hL4
      have hlower : (L:ℝ) / 2 ≤
          ‖(L:ℝ) • aux.direction - (t:ℝ) • (x + y)‖ := by
        simpa [smul_add, sub_sub] using hsep
      intro hzero
      have hL2pos : (0:ℝ) < L / 2 := by positivity
      have hnorm : ‖(L:ℝ) • aux.direction - (t:ℝ) • (x + y)‖ = 0 := by
        rw [hzero, norm_zero]
      linarith
    have hlineContDiff : ∀ (x y : X),
        ContDiffOn ℝ 2
          (translatedCrossLine A.kappa ((L : ℝ) • aux.direction) x y)
          (Set.Icc (0:ℝ) 1) := by
      intro x y
      exact translatedCrossLine_contDiffOn A.kappa
        ((L:ℝ) • aux.direction) x y (hlineNonzero x y)
    have hlineSecond : ∀ (x y : X), ∀ t ∈ Set.Ioo (0:ℝ) 1,
        |iteratedDerivWithin 2
          (translatedCrossLine A.kappa ((L : ℝ) • aux.direction) x y)
          (Set.Icc (0:ℝ) 1) t| ≤
          2 * A.C * L ^ (-A.kappa - 2) := by
      intro x y t ht
      have hxt : ‖(t:ℝ) • x‖ ≤ A.R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
        calc
          (t:ℝ) * ‖x‖ ≤ 1 * A.R :=
            mul_le_mul ht.2.le (aux.hX x) (norm_nonneg x) zero_le_one
          _ = A.R := by ring
      have hyt : ‖(t:ℝ) • y‖ ≤ A.R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
        calc
          (t:ℝ) * ‖y‖ ≤ 1 * A.R :=
            mul_le_mul ht.2.le (aux.hX y) (norm_nonneg y) zero_le_one
          _ = A.R := by ring
      have hsep : (L:ℝ) / 2 ≤
          ‖(L:ℝ) • aux.direction - (t:ℝ) • x - (t:ℝ) • y‖ :=
        translatedCrossKernel_separation_of_mem_ball
          aux.hdirection hxt hyt hL4
      have hlower : (L:ℝ) / 2 ≤
          ‖(L:ℝ) • aux.direction - (t:ℝ) • (x + y)‖ := by
        simpa [smul_add, sub_sub] using hsep
      have hne : (L:ℝ) • aux.direction - (t:ℝ) • (x + y) ≠ 0 := by
        intro hzero
        have hL2pos : (0:ℝ) < L / 2 := by positivity
        have hnorm : ‖(L:ℝ) • aux.direction - (t:ℝ) • (x + y)‖ = 0 := by
          rw [hzero, norm_zero]
        linarith
      have hz : ‖x + y‖ ≤ 2 * A.R := by
        calc
          ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
          _ ≤ A.R + A.R := add_le_add (aux.hX x) (aux.hX y)
          _ = 2 * A.R := by ring
      have hz2 : ‖x + y‖ ^ 2 ≤ (2 * A.R) ^ 2 := by
        refine sq_le_sq.mpr ?_
        rw [abs_of_nonneg (norm_nonneg _),
          abs_of_nonneg (mul_nonneg (by norm_num) A.hR.le)]
        exact hz
      have hL2pos : (0:ℝ) < L / 2 := by positivity
      have hexp : -A.kappa - 2 ≤ 0 := by
        have : (0:ℝ) ≤ A.kappa + 2 := by positivity
        linarith
      have hpowLe :
          ‖(L:ℝ) • aux.direction - (t:ℝ) • (x + y)‖ ^ (-A.kappa - 2) ≤
            (L / 2) ^ (-A.kappa - 2) :=
        Real.rpow_le_rpow_of_nonpos hL2pos hlower hexp
      have hpowHalf : (L / 2) ^ (-A.kappa - 2) =
          (2:ℝ) ^ (A.kappa + 2) * L ^ (-A.kappa - 2) := by
        calc
          (L / 2) ^ (-A.kappa - 2) = ((L / 2)⁻¹) ^ (A.kappa + 2) := by
            rw [show (-A.kappa - 2 : ℝ) = -(A.kappa + 2) by ring,
              Real.rpow_neg_eq_inv_rpow]
          _ = (2 / L) ^ (A.kappa + 2) := by rw [inv_div]
          _ = (2:ℝ) ^ (A.kappa + 2) / L ^ (A.kappa + 2) :=
            Real.div_rpow (by norm_num) (le_of_lt hLpos) _
          _ = (2:ℝ) ^ (A.kappa + 2) * L ^ (-A.kappa - 2) := by
            rw [div_eq_mul_inv,
              show (-A.kappa - 2 : ℝ) = -(A.kappa + 2) by ring,
              Real.rpow_neg (le_of_lt hLpos)]
      have hprod :
          A.kappa * (A.kappa + 1) *
              ‖(L:ℝ) • aux.direction - (t:ℝ) • (x + y)‖ ^ (-A.kappa - 2) *
              ‖x + y‖ ^ 2 ≤
            A.kappa * (A.kappa + 1) *
              (L / 2) ^ (-A.kappa - 2) * (2 * A.R) ^ 2 := by
        calc
          A.kappa * (A.kappa + 1) *
              ‖(L:ℝ) • aux.direction - (t:ℝ) • (x + y)‖ ^ (-A.kappa - 2) *
              ‖x + y‖ ^ 2 ≤
            A.kappa * (A.kappa + 1) *
              (L / 2) ^ (-A.kappa - 2) * ‖x + y‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left hpowLe
                (by positivity)
            · exact sq_nonneg _
          _ ≤ A.kappa * (A.kappa + 1) *
              (L / 2) ^ (-A.kappa - 2) * (2 * A.R) ^ 2 :=
            mul_le_mul_of_nonneg_left hz2 (by positivity)
      have hpowStep : (2:ℝ) ^ (A.kappa + 3) =
          (2:ℝ) ^ (A.kappa + 2) * 2 := by
        rw [show (A.kappa + 3 : ℝ) = (A.kappa + 2) + 1 by ring,
          Real.rpow_add_one (by norm_num)]
      have hconst :
          A.kappa * (A.kappa + 1) *
              (L / 2) ^ (-A.kappa - 2) * (2 * A.R) ^ 2 =
            2 * A.C * L ^ (-A.kappa - 2) := by
        show A.kappa * (A.kappa + 1) *
            (L / 2) ^ (-A.kappa - 2) * (2 * A.R) ^ 2 =
          2 * ((2:ℝ) ^ (A.kappa + 3) * A.kappa *
            (A.kappa + 1) * A.R ^ 2) * L ^ (-A.kappa - 2)
        rw [hpowHalf, hpowStep]
        ring
      have hcontAt := (hlineContDiff x y).contDiffAt
        (Icc_mem_nhds ht.1 ht.2)
      have hiter : iteratedDerivWithin 2
          (translatedCrossLine A.kappa ((L : ℝ) • aux.direction) x y)
          (Set.Icc (0:ℝ) 1) t =
          deriv (deriv
            (translatedCrossLine A.kappa ((L : ℝ) • aux.direction) x y)) t := by
        rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (show (0:ℝ) < 1 by norm_num))
          hcontAt (Set.mem_Icc_of_Ioo ht),
          iteratedDeriv_succ, iteratedDeriv_one]
      rw [hiter]
      refine (translatedCrossLine_second_deriv_abs_le A.kappa hkappa
        ((L:ℝ) • aux.direction) x y t hne).trans ?_
      exact hprod.trans hconst.le
    have hTaylorBound : ∀ x y : X,
        |twoWellTaylorRemainder A aux.direction
          (linearForm aux.direction) L (x, y)| ≤
          A.C * L ^ (-A.kappa - 2) := by
      intro x y
      set g : ℝ → ℝ :=
        translatedCrossLine A.kappa ((L : ℝ) • aux.direction) x y
      have hg0 : g 0 = L ^ (-A.kappa) := by
        show translatedCrossLine A.kappa ((L : ℝ) • aux.direction) x y 0 =
          L ^ (-A.kappa)
        rw [translatedCrossLine_zero, norm_smul, Real.norm_eq_abs,
          aux.hdirection, mul_one, abs_of_nonneg (le_of_lt hLpos)]
      have hg1 : g 1 =
          translatedCrossKernel A.kappa ((L : ℝ) • aux.direction) x y :=
        translatedCrossLine_one A.kappa ((L : ℝ) • aux.direction) x y
      have hC : 0 ≤ 2 * A.C * L ^ (-A.kappa - 2) := by
        have h : 0 ≤ A.C * L ^ (-A.kappa - 2) :=
          mul_nonneg A.hC.le (Real.rpow_nonneg (le_of_lt hLpos) _)
        nlinarith
      have hsc := scalar_taylor_remainder_bound g 0 1
        (2 * A.C * L ^ (-A.kappa - 2))
        (by norm_num) (by norm_num) hC
        (hlineContDiff x y)
        (hlineSecond x y)
      rw [hg0, hg1, hlineDeriv x y] at hsc
      simp only [sub_zero, one_mul, one_pow, mul_one] at hsc
      have hcalc : (2 * A.C * L ^ (-A.kappa - 2)) / 2 =
          A.C * L ^ (-A.kappa - 2) := by
        field_simp
      rw [hcalc] at hsc
      simpa [twoWellTaylorRemainder] using hsc
    have hlinearCont : Continuous (linearForm aux.direction) := by
      unfold linearForm
      exact continuous_const.inner continuous_id
    have hlinCont : Continuous (fun z : X × X =>
        linearForm aux.direction (z.1 + z.2)) :=
      hlinearCont.comp (continuous_fst.add continuous_snd)
    have hlinMeas : MeasureTheory.AEStronglyMeasurable
        (fun z : X × X => linearForm aux.direction (z.1 + z.2))
        (mu.prod mu) :=
      hlinCont.aestronglyMeasurable
    have hlinBound : ∀ z : X × X,
        |linearForm aux.direction (z.1 + z.2)| ≤ 2 * A.R := by
      intro z
      rcases z with ⟨x, y⟩
      have hxy : ‖x + y‖ ≤ 2 * A.R := by
        calc
          ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
          _ ≤ A.R + A.R := add_le_add (aux.hX x) (aux.hX y)
          _ = 2 * A.R := by ring
      calc
        |linearForm aux.direction (x + y)| =
            |inner ℝ aux.direction (x + y)| := rfl
        _ ≤ ‖aux.direction‖ * ‖x + y‖ :=
          abs_real_inner_le_norm aux.direction (x + y)
        _ = ‖x + y‖ := by rw [aux.hdirection]; ring
        _ ≤ 2 * A.R := hxy
    have hlinInt := bounded_factor_mul_integrable
      (u := fun z : X × X => ⇑aux.φ z.1 * ⇑aux.φ z.2)
      (v := fun z : X × X => linearForm aux.direction (z.1 + z.2))
      (C := 2 * A.R)
      (l2ProductIntegrable aux.φ) hlinMeas hlinBound
    have hRMeas : MeasureTheory.AEStronglyMeasurable
        (fun z : X × X => twoWellTaylorRemainder A aux.direction
          (linearForm aux.direction) L z) (mu.prod mu) :=
      (twoWellTaylorRemainder_continuous A aux.direction L hLpos
        aux.hdirection aux.hX hL4).aestronglyMeasurable
    have hRInt := bounded_factor_mul_integrable
      (u := fun z : X × X => ⇑aux.φ z.1 * ⇑aux.φ z.2)
      (v := fun z : X × X => twoWellTaylorRemainder A aux.direction
        (linearForm aux.direction) L z)
      (C := A.C * L ^ (-A.kappa - 2))
      (l2ProductIntegrable aux.φ) hRMeas
      (fun z => hTaylorBound z.1 z.2)
    have hI := interactionMass_taylor_remainder mu ⇑aux.φ
      (translatedCrossKernel A.kappa ((L : ℝ) • aux.direction))
      (linearForm aux.direction)
        (fun z => twoWellTaylorRemainder A aux.direction
          (linearForm aux.direction) L z)
      A.phiMass (L ^ (-A.kappa))
      (A.kappa * L ^ (-A.kappa - 1))
      (A.C * L ^ (-A.kappa - 2))
      (l2ProductIntegrable aux.φ) hlinInt hRInt aux.hmass
        (linear_integral_zero_of_even aux.φ aux.direction aux.heven aux.hmeasureNeg)
      aux.hnonneg
      (mul_nonneg A.hC.le (Real.rpow_nonneg (le_of_lt hLpos) _))
      (fun x y =>
        twoWellTaylorRemainder_eq A aux.direction
          (linearForm aux.direction) L x y)
      (fun x y => hTaylorBound x y)
    rw [hK]
    have habs :
        |-A.c * kernelCrossPairing
            (translatedCrossKernel A.kappa ((L : ℝ) • aux.direction))
            mu ⇑aux.φ ⇑aux.φ +
          A.c * A.phiMass ^ 2 * L ^ (-A.kappa)| =
          A.c * |kernelCrossPairing
            (translatedCrossKernel A.kappa ((L : ℝ) • aux.direction))
            mu ⇑aux.φ ⇑aux.φ -
            A.phiMass ^ 2 * L ^ (-A.kappa)| := by
      set I : ℝ := kernelCrossPairing
        (translatedCrossKernel A.kappa ((L : ℝ) • aux.direction))
        mu ⇑aux.φ ⇑aux.φ
      have h :
          -A.c * I + A.c * A.phiMass ^ 2 * L ^ (-A.kappa) =
            A.c * (A.phiMass ^ 2 * L ^ (-A.kappa) - I) := by
        ring
      rw [h, abs_mul, abs_of_nonneg A.hc.le, abs_sub_comm]
    rw [habs]
    have hIApprox :
        |kernelCrossPairing
            (translatedCrossKernel A.kappa ((L : ℝ) • aux.direction))
            mu ⇑aux.φ ⇑aux.φ -
          A.phiMass ^ 2 * L ^ (-A.kappa)| ≤
          A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) := by
      simpa [kernelCrossPairing, pow_two, mul_assoc, mul_comm,
        mul_left_comm] using hI
    have hmul := mul_le_mul_of_nonneg_left hIApprox A.hc.le
    simpa only [mul_assoc] using hmul

end L2TwoWellAux

/-- The two-well conclusion for the concrete Gagliardo cross kernel. -/
theorem FinalTheoremL2 (A : TwoWellConstants)
    (X : Type*) [MeasurableSpace X] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [SecondCountableTopology X] [OpensMeasurableSpace X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    [MeasureTheory.IsFiniteMeasure mu]
    (aux : L2TwoWellAux A X mu) :
    A.twoWellStatement aux.lambda := by
  exact FinalTheorem A (L2TwoWellAux.toSpectralInput aux)

end Tunneling
