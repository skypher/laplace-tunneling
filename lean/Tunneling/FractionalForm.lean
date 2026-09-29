import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection

/-!
# The zero-exterior Gagliardo form

This file records the concrete integrand used by the restricted fractional
Laplacian.  The integral is deliberately formed against an arbitrary measure
on the underlying measurable normed group so that the source extraction can be
compiled before the Euclidean-volume and operator constructions are added.
-/

namespace Tunneling

variable {X : Type*} [NormedAddCommGroup X]

/-- The singular kernel `|x-y|^(-κ)` in the Gagliardo seminorm. -/
noncomputable def gagliardoKernel (kappa : ℝ) (x y : X) : ℝ :=
  ‖x - y‖ ^ (-kappa)

/-- The singular Gagliardo kernel is measurable on the product space.  This
is the source-level measurability input used by the zero-exterior form. -/
theorem measurable_gagliardoKernel
    [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    (kappa : ℝ) :
    Measurable (fun z : X × X => gagliardoKernel kappa z.1 z.2) := by
  have hnorm : Measurable (fun z : X × X => ‖z.1 - z.2‖) :=
    (continuous_norm.comp continuous_sub).measurable
  show Measurable (fun z : X × X => ‖z.1 - z.2‖ ^ (-kappa))
  exact hnorm.pow_const (-kappa)

/-- Product-measure measurability of the singular Gagliardo kernel. -/
theorem gagliardoKernel_aestronglyMeasurable
    [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    (kappa : ℝ) (mu : MeasureTheory.Measure X) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu) :=
  (measurable_gagliardoKernel kappa).aestronglyMeasurable

/-- The pointwise Gagliardo integrand for a real-valued function. -/
noncomputable def gagliardoIntegrand (kappa : ℝ) (u : X → ℝ) (z : X × X) : ℝ :=
  (u z.1 - u z.2) ^ 2 * gagliardoKernel kappa z.1 z.2

theorem gagliardoIntegrand_nonneg (kappa : ℝ) (u : X → ℝ) (z : X × X) :
    0 ≤ gagliardoIntegrand kappa u z := by
  apply mul_nonneg
  · exact sq_nonneg _
  · exact Real.rpow_nonneg (norm_nonneg _) _

theorem gagliardoIntegrand_swap (kappa : ℝ) (u : X → ℝ) (x y : X) :
    gagliardoIntegrand kappa u (x, y) = gagliardoIntegrand kappa u (y, x) := by
  simp only [gagliardoIntegrand, gagliardoKernel]
  rw [norm_sub_rev]
  ring

theorem gagliardoIntegrand_zero_of_eq (kappa : ℝ) (u : X → ℝ) (x y : X)
    (h : u x = u y) : gagliardoIntegrand kappa u (x, y) = 0 := by
  simp [gagliardoIntegrand, gagliardoKernel, h]

/-- The real cross-term cancellation used in the exact block reduction. -/
theorem crossTerm_identity {Y : Type*} (u v : Y → ℝ) (x y : Y) :
    (u x - v y) ^ 2 - u x ^ 2 - v y ^ 2 = -2 * u x * v y := by
  ring

/-- The cross correction between two zero-exterior components.  This is the
integrand in the exact block reduction of Lemma 2.1. -/
noncomputable def pairCrossExcess (kappa : ℝ) (u v : X → ℝ) (z : X × X) : ℝ :=
  ((u z.1 - v z.2) ^ 2 - u z.1 ^ 2 - v z.2 ^ 2) *
    gagliardoKernel kappa z.1 z.2

/-- The signed interaction integrand produced by the cross correction. -/
noncomputable def crossIntegrand (kappa : ℝ) (u v : X → ℝ) (z : X × X) : ℝ :=
  u z.1 * v z.2 * gagliardoKernel kappa z.1 z.2

theorem pairCrossExcess_eq (kappa : ℝ) (u v : X → ℝ) (z : X × X) :
    pairCrossExcess kappa u v z = -2 * crossIntegrand kappa u v z := by
  rcases z with ⟨x, y⟩
  simp only [pairCrossExcess, crossIntegrand]
  rw [crossTerm_identity u v x y]
  ring

theorem crossIntegrand_swap (kappa : ℝ) (u v : X → ℝ) (x y : X) :
    crossIntegrand kappa u v (x, y) = crossIntegrand kappa v u (y, x) := by
  simp only [crossIntegrand, gagliardoKernel]
  rw [norm_sub_rev]
  ring

/-- The signed interaction pairing from the Gagliardo cross kernel. -/
noncomputable def crossPairing
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    (u v : X → ℝ) : ℝ :=
  ∫ z : X × X, crossIntegrand kappa u v z ∂(mu.prod mu)

theorem crossPairing_symm
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu]
    (u v : X → ℝ) : crossPairing kappa mu u v = crossPairing kappa mu v u := by
  simp only [crossPairing]
  calc
    (∫ z : X × X, crossIntegrand kappa u v z ∂(mu.prod mu)) =
        ∫ z : X × X, crossIntegrand kappa u v z.swap ∂(mu.prod mu) := by
      rw [MeasureTheory.integral_prod_swap]
    _ = ∫ z : X × X, crossIntegrand kappa v u z ∂(mu.prod mu) := by
      apply MeasureTheory.integral_congr_ae
      exact MeasureTheory.ae_of_all _
        (fun z => crossIntegrand_swap kappa u v z.2 z.1)

/-- Integral form of the exact cross-term cancellation. -/
theorem pairCrossExcessIntegral_eq
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    (u v : X → ℝ) :
    ∫ z : X × X, pairCrossExcess kappa u v z ∂(mu.prod mu) =
      -2 * ∫ z : X × X, crossIntegrand kappa u v z ∂(mu.prod mu) := by
  have h : (fun z : X × X => pairCrossExcess kappa u v z) =
      fun z => -2 * crossIntegrand kappa u v z := by
    funext z
    exact pairCrossExcess_eq kappa u v z
  rw [h, MeasureTheory.integral_const_mul]

theorem interactionMass_taylor_remainder
    [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu]
    (u : X → ℝ) (T : X → X → ℝ) (ell : X → ℝ) (R : X × X → ℝ)
    (m a b r : ℝ)
    (hprodInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2) (mu.prod mu))
    (hlinInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2 * ell (z.1 + z.2)) (mu.prod mu))
    (hRInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2 * R z) (mu.prod mu))
    (hmass : ∫ x, u x ∂mu = m)
    (hlinear : ∫ z : X × X, u z.1 * u z.2 * ell (z.1 + z.2) ∂(mu.prod mu) = 0)
    (hnonneg : ∀ x, 0 ≤ u x)
    (hr : 0 ≤ r)
    (hdecomp : ∀ x y, T x y = a + b * ell (x + y) + R (x, y))
    (hRbound : ∀ x y, |R (x, y)| ≤ r) :
    |∫ z : X × X, u z.1 * u z.2 * T z.1 z.2 ∂(mu.prod mu) - m * m * a| ≤
      r * m * m := by
  have hm : 0 ≤ m := by
    have h : (0:ℝ) ≤ ∫ x, u x ∂mu :=
      MeasureTheory.integral_nonneg (fun x => hnonneg x)
    linarith
  have hprodEq : ∫ z : X × X, u z.1 * u z.2 ∂(mu.prod mu) = m * m := by
    rw [MeasureTheory.integral_prod_mul u u, hmass]
  have hRbound' : ∀ z : X × X,
      |u z.1 * u z.2 * R z| ≤ r * (u z.1 * u z.2) := by
    intro z
    rcases z with ⟨x, y⟩
    have hprod : 0 ≤ u x * u y := mul_nonneg (hnonneg x) (hnonneg y)
    calc
      |u x * u y * R (x, y)| = |u x * u y| * |R (x, y)| := by rw [abs_mul]
      _ = (u x * u y) * |R (x, y)| := by rw [abs_of_nonneg hprod]
      _ ≤ (u x * u y) * r := mul_le_mul_of_nonneg_left (hRbound x y) hprod
      _ = r * (u x * u y) := by ring
  have hremAbs :
      |∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)| ≤
        ∫ z : X × X, |u z.1 * u z.2 * R z| ∂(mu.prod mu) :=
    MeasureTheory.abs_integral_le_integral_abs
  have hremMono :
      ∫ z : X × X, |u z.1 * u z.2 * R z| ∂(mu.prod mu) ≤
        ∫ z : X × X, r * (u z.1 * u z.2) ∂(mu.prod mu) :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_of_all _ fun _ => abs_nonneg _)
      (hprodInt.const_mul r)
      (MeasureTheory.ae_of_all _ fun z => hRbound' z)
  have hremConst :
      ∫ z : X × X, r * (u z.1 * u z.2) ∂(mu.prod mu) = r * m * m := by
    rw [MeasureTheory.integral_const_mul, hprodEq]
    ring
  have hrem : |∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)| ≤ r * m * m := by
    calc
      |∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)| ≤
          ∫ z : X × X, |u z.1 * u z.2 * R z| ∂(mu.prod mu) := hremAbs
      _ ≤ ∫ z : X × X, r * (u z.1 * u z.2) ∂(mu.prod mu) := hremMono
      _ = r * m * m := hremConst
  have hpointEq : ∀ z : X × X,
      u z.1 * u z.2 * T z.1 z.2 =
        a * (u z.1 * u z.2) +
          (b * (u z.1 * u z.2 * ell (z.1 + z.2)) +
            u z.1 * u z.2 * R z) := by
    intro z
    rcases z with ⟨x, y⟩
    rw [hdecomp x y]
    ring
  have hsumInt : MeasureTheory.Integrable
      (fun z : X × X =>
        b * (u z.1 * u z.2 * ell (z.1 + z.2)) +
          u z.1 * u z.2 * R z) (mu.prod mu) :=
    (hlinInt.const_mul b).add hRInt
  have hexpand :
      ∫ z : X × X, u z.1 * u z.2 * T z.1 z.2 ∂(mu.prod mu) =
        a * m * m +
          ∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu) := by
    calc
      ∫ z : X × X, u z.1 * u z.2 * T z.1 z.2 ∂(mu.prod mu) =
          ∫ z : X × X,
            (a * (u z.1 * u z.2) +
              (b * (u z.1 * u z.2 * ell (z.1 + z.2)) +
                u z.1 * u z.2 * R z)) ∂(mu.prod mu) :=
        MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_of_all _ hpointEq)
      _ = ∫ z : X × X, a * (u z.1 * u z.2) ∂(mu.prod mu) +
          ∫ z : X × X,
            (b * (u z.1 * u z.2 * ell (z.1 + z.2)) +
              u z.1 * u z.2 * R z) ∂(mu.prod mu) :=
        MeasureTheory.integral_add (hprodInt.const_mul a) hsumInt
      _ = ∫ z : X × X, a * (u z.1 * u z.2) ∂(mu.prod mu) +
          (∫ z : X × X, b * (u z.1 * u z.2 * ell (z.1 + z.2)) ∂(mu.prod mu) +
            ∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)) := by
        rw [MeasureTheory.integral_add (hlinInt.const_mul b) hRInt]
      _ = a * m * m +
          ∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu) := by
        rw [MeasureTheory.integral_const_mul, hprodEq,
          MeasureTheory.integral_const_mul, hlinear]
        ring
  rw [hexpand]
  have hkey : a * m * m +
      (∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)) - m * m * a =
      ∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu) := by
    ring
  rw [hkey]
  exact hrem

/-! The same mass-Taylor estimate with a general linear form on the product
space.  This is the form needed for the finite-well kernel, where the linear
term is `inner a (x-y)` rather than a function of `x+y`. -/
theorem interactionMass_taylor_remainder_prod
    [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu]
    (u : X → ℝ) (T : X → X → ℝ) (ell : X × X → ℝ) (R : X × X → ℝ)
    (m a b r : ℝ)
    (hprodInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2) (mu.prod mu))
    (hlinInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2 * ell z) (mu.prod mu))
    (hRInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2 * R z) (mu.prod mu))
    (hmass : ∫ x, u x ∂mu = m)
    (hlinear : ∫ z : X × X, u z.1 * u z.2 * ell z ∂(mu.prod mu) = 0)
    (hnonneg : ∀ x, 0 ≤ u x)
    (hr : 0 ≤ r)
    (hdecomp : ∀ x y, T x y = a + b * ell (x, y) + R (x, y))
    (hRbound : ∀ x y, |R (x, y)| ≤ r) :
    |∫ z : X × X, u z.1 * u z.2 * T z.1 z.2 ∂(mu.prod mu) - m * m * a| ≤
      r * m * m := by
  have hm : 0 ≤ m := by
    have h : (0:ℝ) ≤ ∫ x, u x ∂mu :=
      MeasureTheory.integral_nonneg (fun x => hnonneg x)
    linarith
  have hprodEq : ∫ z : X × X, u z.1 * u z.2 ∂(mu.prod mu) = m * m := by
    rw [MeasureTheory.integral_prod_mul u u, hmass]
  have hRbound' : ∀ z : X × X,
      |u z.1 * u z.2 * R z| ≤ r * (u z.1 * u z.2) := by
    intro z
    rcases z with ⟨x, y⟩
    have hprod : 0 ≤ u x * u y := mul_nonneg (hnonneg x) (hnonneg y)
    calc
      |u x * u y * R (x, y)| = |u x * u y| * |R (x, y)| := by rw [abs_mul]
      _ = (u x * u y) * |R (x, y)| := by rw [abs_of_nonneg hprod]
      _ ≤ (u x * u y) * r := mul_le_mul_of_nonneg_left (hRbound x y) hprod
      _ = r * (u x * u y) := by ring
  have hremAbs :
      |∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)| ≤
        ∫ z : X × X, |u z.1 * u z.2 * R z| ∂(mu.prod mu) :=
    MeasureTheory.abs_integral_le_integral_abs
  have hremMono :
      ∫ z : X × X, |u z.1 * u z.2 * R z| ∂(mu.prod mu) ≤
        ∫ z : X × X, r * (u z.1 * u z.2) ∂(mu.prod mu) :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_of_all _ fun _ => abs_nonneg _)
      (hprodInt.const_mul r)
      (MeasureTheory.ae_of_all _ fun z => hRbound' z)
  have hremConst :
      ∫ z : X × X, r * (u z.1 * u z.2) ∂(mu.prod mu) = r * m * m := by
    rw [MeasureTheory.integral_const_mul, hprodEq]
    ring
  have hrem : |∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)| ≤ r * m * m := by
    calc
      |∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)| ≤
          ∫ z : X × X, |u z.1 * u z.2 * R z| ∂(mu.prod mu) := hremAbs
      _ ≤ ∫ z : X × X, r * (u z.1 * u z.2) ∂(mu.prod mu) := hremMono
      _ = r * m * m := hremConst
  have hpointEq : ∀ z : X × X,
      u z.1 * u z.2 * T z.1 z.2 =
        a * (u z.1 * u z.2) +
          (b * (u z.1 * u z.2 * ell z) + u z.1 * u z.2 * R z) := by
    intro z
    rcases z with ⟨x, y⟩
    rw [hdecomp x y]
    ring
  have hsumInt : MeasureTheory.Integrable
      (fun z : X × X =>
        b * (u z.1 * u z.2 * ell z) + u z.1 * u z.2 * R z) (mu.prod mu) :=
    (hlinInt.const_mul b).add hRInt
  have hexpand :
      ∫ z : X × X, u z.1 * u z.2 * T z.1 z.2 ∂(mu.prod mu) =
        a * m * m + ∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu) := by
    calc
      ∫ z : X × X, u z.1 * u z.2 * T z.1 z.2 ∂(mu.prod mu) =
          ∫ z : X × X,
            (a * (u z.1 * u z.2) +
              (b * (u z.1 * u z.2 * ell z) + u z.1 * u z.2 * R z))
              ∂(mu.prod mu) :=
        MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_of_all _ hpointEq)
      _ = ∫ z : X × X, a * (u z.1 * u z.2) ∂(mu.prod mu) +
          ∫ z : X × X,
            (b * (u z.1 * u z.2 * ell z) + u z.1 * u z.2 * R z)
              ∂(mu.prod mu) :=
        MeasureTheory.integral_add (hprodInt.const_mul a) hsumInt
      _ = ∫ z : X × X, a * (u z.1 * u z.2) ∂(mu.prod mu) +
          (∫ z : X × X, b * (u z.1 * u z.2 * ell z) ∂(mu.prod mu) +
            ∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)) := by
        rw [MeasureTheory.integral_add (hlinInt.const_mul b) hRInt]
      _ = a * m * m +
          ∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu) := by
        rw [MeasureTheory.integral_const_mul, hprodEq,
          MeasureTheory.integral_const_mul, hlinear]
        ring
  rw [hexpand]
  have hkey : a * m * m +
      (∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu)) - m * m * a =
      ∫ z : X × X, u z.1 * u z.2 * R z ∂(mu.prod mu) := by ring
  rw [hkey]
  exact hrem

/-! Algebraic cancellation of the finite-well linear term. -/
theorem linear_sub_integral_zero
    [MeasurableSpace X] [InnerProductSpace ℝ X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    (a : X) (u : X → ℝ) :
    ∫ z : X × X, u z.1 * u z.2 * inner ℝ a (z.1 - z.2) ∂(mu.prod mu) = 0 := by
  set f : X × X → ℝ :=
    fun z => u z.1 * u z.2 * inner ℝ a (z.1 - z.2)
  have hpoint : ∀ z : X × X, f z.swap = -f z := by
    intro z
    rcases z with ⟨x, y⟩
    have h : x - y = -(y - x) := by abel
    simp only [f, Prod.swap]
    rw [h, inner_neg_right]
    ring
  have hswap : ∫ z : X × X, f z ∂(mu.prod mu) =
      ∫ z : X × X, f z.swap ∂(mu.prod mu) :=
    (MeasureTheory.integral_prod_swap f).symm
  have hneg : ∫ z : X × X, f z.swap ∂(mu.prod mu) =
      -∫ z : X × X, f z ∂(mu.prod mu) := by
    rw [MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_of_all _ hpoint), MeasureTheory.integral_neg]
  linarith [hswap, hneg]

theorem scalar_taylor_remainder_bound
    (g : ℝ → ℝ) (a b C : ℝ)
    (hab : a ≤ b) (hne : a ≠ b) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ 2 g (Set.Icc a b))
    (hsecond : ∀ t ∈ Set.Ioo a b,
      |iteratedDerivWithin 2 g (Set.Icc a b) t| ≤ C) :
    |g b - g a - (b - a) * derivWithin g (Set.Icc a b) a| ≤
      C * (b - a) ^ 2 / 2 := by
  have hlt : a < b := lt_of_le_of_ne hab hne
  have hIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hIoo : Set.uIoo a b = Set.Ioo a b := Set.uIoo_of_le hab
  have hpoly : taylorWithinEval g 1 (Set.uIcc a b) a b =
      g a + (b - a) * derivWithin g (Set.uIcc a b) a := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_one]
    simp [Nat.factorial, pow_one, smul_eq_mul]
  have hf1 : ContDiffOn ℝ 1 g (Set.uIcc a b) := by
    rw [hIcc]
    exact hf.of_le (m := 1) (by norm_num)
  have hd : DifferentiableOn ℝ
      (iteratedDerivWithin 1 g (Set.uIcc a b)) (Set.uIoo a b) := by
    rw [hIcc, hIoo]
    exact (hf.differentiableOn_iteratedDerivWithin (by norm_num)
      (uniqueDiffOn_Icc hlt)).mono Set.Ioo_subset_Icc_self
  obtain ⟨t, ht, hlag⟩ := taylor_mean_remainder_lagrange hne hf1 hd
  rw [hpoly] at hlag
  rw [hIcc] at hlag
  have hbound : |iteratedDerivWithin 2 g (Set.Icc a b) t| ≤ C := by
    apply hsecond t
    rw [hIoo] at ht
    exact ht
  have hs : 0 ≤ (b - a) ^ 2 := sq_nonneg _
  have hden : ((1 + 1 : ℕ).factorial : ℝ) = 2 := by
    norm_num [Nat.factorial]
  have habs :
      |iteratedDerivWithin 2 g (Set.Icc a b) t * (b - a) ^ 2 /
          ((1 + 1 : ℕ).factorial : ℝ)| ≤
        C * (b - a) ^ 2 / 2 := by
    have hnorm :
        |iteratedDerivWithin 2 g (Set.Icc a b) t * (b - a) ^ 2 /
            ((1 + 1 : ℕ).factorial : ℝ)| =
          |iteratedDerivWithin 2 g (Set.Icc a b) t| * (b - a) ^ 2 /
            ((1 + 1 : ℕ).factorial : ℝ) := by
      rw [abs_div, abs_mul, abs_of_nonneg hs,
        abs_of_nonneg
          (show (0:ℝ) ≤ ((1 + 1 : ℕ).factorial : ℝ) by norm_num)]
    rw [hnorm, hden]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbound hs) (by norm_num)
  have hkey :
      g b - g a - (b - a) * derivWithin g (Set.Icc a b) a =
        g b - (g a + (b - a) * derivWithin g (Set.Icc a b) a) := by
    ring
  rw [hkey, hlag]
  exact habs

/-- A general real kernel pairing on a product measure.  The separated kernel
in Lemma 2.1 is obtained by specializing `K` to `translatedCrossKernel`. -/
noncomputable def kernelCrossPairing
    [MeasurableSpace X] (K : X → X → ℝ) (mu : MeasureTheory.Measure X)
    (u v : X → ℝ) : ℝ :=
  ∫ z : X × X, u z.1 * v z.2 * K z.1 z.2 ∂(mu.prod mu)

theorem kernelCrossPairing_congr
    [MeasurableSpace X] {K₁ K₂ : X → X → ℝ}
    (mu : MeasureTheory.Measure X) (h : ∀ x y, K₁ x y = K₂ x y)
    (u v : X → ℝ) :
    kernelCrossPairing K₁ mu u v = kernelCrossPairing K₂ mu u v := by
  simp only [kernelCrossPairing]
  apply MeasureTheory.integral_congr_ae
  exact MeasureTheory.ae_of_all _ (fun z => by
    rcases z with ⟨x, y⟩
    show u x * v y * K₁ x y = u x * v y * K₂ x y
    rw [h x y])

theorem kernelCrossPairing_const_mul_kernel
    [MeasurableSpace X] (a : ℝ) (K : X → X → ℝ)
    (mu : MeasureTheory.Measure X) (u v : X → ℝ) :
    kernelCrossPairing (fun x y => a * K x y) mu u v =
      a * kernelCrossPairing K mu u v := by
  simp only [kernelCrossPairing]
  have h : (fun z : X × X => u z.1 * v z.2 * (a * K z.1 z.2)) =
      (fun z : X × X => a * (u z.1 * v z.2 * K z.1 z.2)) := by
    funext z
    rcases z with ⟨x, y⟩
    ring
  rw [h, MeasureTheory.integral_const_mul]

theorem kernelCrossPairing_symm
    [MeasurableSpace X] (K : X → X → ℝ) (hKsymm : ∀ x y, K x y = K y x)
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    (u v : X → ℝ) :
    kernelCrossPairing K mu u v = kernelCrossPairing K mu v u := by
  simp only [kernelCrossPairing]
  calc
    (∫ z : X × X, u z.1 * v z.2 * K z.1 z.2 ∂(mu.prod mu)) =
        ∫ z : X × X, u z.1 * v z.2 * K z.1 z.2 ∂(mu.prod mu) := rfl
    _ = ∫ z : X × X, v z.2 * u z.1 * K z.2 z.1 ∂(mu.prod mu) := by
      apply MeasureTheory.integral_congr_ae
      exact MeasureTheory.ae_of_all _ (fun z => by
        rcases z with ⟨x, y⟩
        show u x * v y * K x y = v y * u x * K y x
        rw [hKsymm x y]
        ring)
    _ = ∫ z : X × X, v z.1 * u z.2 * K z.1 z.2 ∂(mu.prod mu) := by
      symm
      exact MeasureTheory.integral_prod_swap
        (fun z : X × X => v z.2 * u z.1 * K z.2 z.1)
    _ = kernelCrossPairing K mu v u := rfl

/-- Lift an almost-everywhere equality on `mu` to its first coordinate on a
product measure.  This is used to transport `Lp` representative equalities
through the kernel pairing. -/
theorem ae_comp_fst_of_ae
    {Y : Type*} [MeasurableSpace Y] {mu : MeasureTheory.Measure Y}
    [MeasureTheory.SFinite mu] {p : Y → Prop} (h : ∀ᵐ x ∂mu, p x) :
    ∀ᵐ z : Y × Y ∂(mu.prod mu), p z.1 := by
  by_cases hzero : mu Set.univ = 0
  · have hprod : (mu.prod mu) Set.univ = 0 := by
      rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod,
        hzero, mul_zero]
    refine MeasureTheory.ae_iff.2 ?_
    have hsubset : {z : Y × Y | ¬p z.1} ⊆ Set.univ := by
      intro z _
      exact Set.mem_univ z
    exact MeasureTheory.measure_mono_null hsubset hprod
  · have hsmul : ∀ᵐ x ∂((mu Set.univ) • mu), p x :=
      (MeasureTheory.Measure.ae_ennreal_smul_measure_iff hzero).2 h
    refine MeasureTheory.ae_of_ae_map measurable_fst.aemeasurable ?_
    rw [MeasureTheory.Measure.map_fst_prod]
    exact hsmul

/-- A uniformly bounded measurable kernel defines an integrable pairing of
`L²` representatives on a finite measure space. -/
theorem kernelCrossPairing_integrable
    [MeasurableSpace X] {mu : MeasureTheory.Measure X}
    [MeasureTheory.SFinite mu] [MeasureTheory.IsFiniteMeasure mu]
    (K : X → X → ℝ) (C : ℝ)
    (hK : ∀ x y, |K x y| ≤ C)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => K z.1 z.2) (mu.prod mu))
    (u v : MeasureTheory.Lp ℝ 2 mu) :
    MeasureTheory.Integrable
      (fun z : X × X => ⇑u z.1 * ⇑v z.2 * K z.1 z.2) (mu.prod mu) := by
  have hu : MeasureTheory.Integrable ⇑u mu :=
    MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
      (MeasureTheory.Lp.memLp u)
  have hv : MeasureTheory.Integrable ⇑v mu :=
    MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
      (MeasureTheory.Lp.memLp v)
  have hprod : MeasureTheory.Integrable
      (fun z : X × X => ⇑u z.1 * ⇑v z.2) (mu.prod mu) :=
    hu.mul_prod hv
  have hbound : ∀ᵐ z : X × X ∂(mu.prod mu), ‖K z.1 z.2‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro z
    simpa [Real.norm_eq_abs] using hK z.1 z.2
  have h := hprod.bdd_mul hmeas hbound
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem kernelCrossPairing_add_left
    [MeasurableSpace X] {mu : MeasureTheory.Measure X}
    [MeasureTheory.SFinite mu] [MeasureTheory.IsFiniteMeasure mu]
    (K : X → X → ℝ) (C : ℝ)
    (hK : ∀ x y, |K x y| ≤ C)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => K z.1 z.2) (mu.prod mu))
    (u₁ u₂ v : MeasureTheory.Lp ℝ 2 mu) :
    kernelCrossPairing K mu ⇑(u₁ + u₂) ⇑v =
      kernelCrossPairing K mu ⇑u₁ ⇑v +
        kernelCrossPairing K mu ⇑u₂ ⇑v := by
  have huv : ∀ᵐ z : X × X ∂(mu.prod mu),
      ⇑(u₁ + u₂) z.1 = ⇑u₁ z.1 + ⇑u₂ z.1 := by
    refine ae_comp_fst_of_ae
      (p := fun x => ⇑(u₁ + u₂) x = ⇑u₁ x + ⇑u₂ x) ?_
    filter_upwards [MeasureTheory.Lp.coeFn_add u₁ u₂] with x hx
    exact hx
  have h1 := kernelCrossPairing_integrable K C hK hmeas u₁ v
  have h2 := kernelCrossPairing_integrable K C hK hmeas u₂ v
  simp only [kernelCrossPairing]
  calc
    ∫ z, ⇑(u₁ + u₂) z.1 * ⇑v z.2 * K z.1 z.2 ∂(mu.prod mu) =
        ∫ z, (⇑u₁ z.1 + ⇑u₂ z.1) * ⇑v z.2 * K z.1 z.2 ∂(mu.prod mu) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [huv] with z hz
      rw [hz]
    _ = ∫ z, ⇑u₁ z.1 * ⇑v z.2 * K z.1 z.2 +
          ⇑u₂ z.1 * ⇑v z.2 * K z.1 z.2 ∂(mu.prod mu) := by
      apply MeasureTheory.integral_congr_ae
      exact MeasureTheory.ae_of_all _ (fun z => by ring)
    _ = _ := MeasureTheory.integral_add h1 h2

theorem kernelCrossPairing_add_right
    [MeasurableSpace X] {mu : MeasureTheory.Measure X}
    [MeasureTheory.SFinite mu] [MeasureTheory.IsFiniteMeasure mu]
    (K : X → X → ℝ) (C : ℝ)
    (hK : ∀ x y, |K x y| ≤ C)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => K z.1 z.2) (mu.prod mu))
    (hsymm : ∀ x y, K x y = K y x)
    (u v₁ v₂ : MeasureTheory.Lp ℝ 2 mu) :
    kernelCrossPairing K mu ⇑u ⇑(v₁ + v₂) =
      kernelCrossPairing K mu ⇑u ⇑v₁ +
        kernelCrossPairing K mu ⇑u ⇑v₂ := by
  rw [kernelCrossPairing_symm K hsymm mu ⇑u ⇑(v₁ + v₂),
    kernelCrossPairing_add_left K C hK hmeas v₁ v₂ u,
    kernelCrossPairing_symm K hsymm mu ⇑v₁ ⇑u,
    kernelCrossPairing_symm K hsymm mu ⇑v₂ ⇑u]

theorem kernelCrossPairing_smul_left
    [MeasurableSpace X] {mu : MeasureTheory.Measure X}
    [MeasureTheory.SFinite mu]
    (K : X → X → ℝ) (c : ℝ) (u v : MeasureTheory.Lp ℝ 2 mu) :
    kernelCrossPairing K mu ⇑(c • u) ⇑v =
      c * kernelCrossPairing K mu ⇑u ⇑v := by
  have huv : ∀ᵐ z : X × X ∂(mu.prod mu),
      ⇑(c • u) z.1 = c * ⇑u z.1 := by
    refine ae_comp_fst_of_ae
      (p := fun x => ⇑(c • u) x = c * ⇑u x) ?_
    filter_upwards [MeasureTheory.Lp.coeFn_smul c u] with x hx
    exact hx
  simp only [kernelCrossPairing]
  calc
    ∫ z, ⇑(c • u) z.1 * ⇑v z.2 * K z.1 z.2 ∂(mu.prod mu) =
        ∫ z, c * (⇑u z.1 * ⇑v z.2 * K z.1 z.2) ∂(mu.prod mu) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [huv] with z hz
      rw [hz]
      ring
    _ = c * ∫ z, ⇑u z.1 * ⇑v z.2 * K z.1 z.2 ∂(mu.prod mu) :=
      MeasureTheory.integral_const_mul c _

theorem kernelCrossPairing_smul_right
    [MeasurableSpace X] {mu : MeasureTheory.Measure X}
    [MeasureTheory.SFinite mu]
    (K : X → X → ℝ) (hsymm : ∀ x y, K x y = K y x)
    (c : ℝ) (u v : MeasureTheory.Lp ℝ 2 mu) :
    kernelCrossPairing K mu ⇑u ⇑(c • v) =
      c * kernelCrossPairing K mu ⇑u ⇑v := by
  rw [kernelCrossPairing_symm K hsymm mu ⇑u ⇑(c • v),
    kernelCrossPairing_smul_left K c v u,
    kernelCrossPairing_symm K hsymm mu ⇑v ⇑u]

/-- The translated cross kernel `|center-x-y|^(-kappa)` from equation `eq:B`. -/
noncomputable def translatedCrossKernel (kappa : ℝ) (center : X) (x y : X) : ℝ :=
  ‖center - x - y‖ ^ (-kappa)

noncomputable def translatedCrossLine
    [Module ℝ X] (kappa : ℝ) (center x y : X) : ℝ → ℝ :=
  fun t => translatedCrossKernel kappa center ((t : ℝ) • x) ((t : ℝ) • y)

theorem translatedCrossLine_zero
    [Module ℝ X] (kappa : ℝ) (center x y : X) :
    translatedCrossLine kappa center x y 0 = ‖center‖ ^ (-kappa) := by
  simp [translatedCrossLine, translatedCrossKernel, zero_smul]

theorem translatedCrossLine_one
    [Module ℝ X] (kappa : ℝ) (center x y : X) :
    translatedCrossLine kappa center x y 1 =
      translatedCrossKernel kappa center x y := by
  simp [translatedCrossLine, one_smul]

theorem norm_rpow_eq_norm_sq_rpow
    [InnerProductSpace ℝ X] (x : X) (p : ℝ) :
    ‖x‖ ^ p = (‖x‖ ^ 2) ^ (p / 2) := by
  rw [← Real.rpow_natCast (‖x‖) 2, ← Real.rpow_mul (norm_nonneg x)]
  congr 1
  ring

theorem norm_sq_rpow_eq_norm_rpow
    [InnerProductSpace ℝ X] (x : X) (p : ℝ) :
    (‖x‖ ^ 2) ^ (p / 2 - 1) = ‖x‖ ^ (p - 2) := by
  rw [← Real.rpow_natCast (‖x‖) 2, ← Real.rpow_mul (norm_nonneg x)]
  congr 1
  ring

theorem norm_sub_smul_hasDerivAt
    [InnerProductSpace ℝ X] (c z : X) (p t : ℝ)
    (hw : c - (t:ℝ) • z ≠ 0) :
    HasDerivAt (fun s : ℝ => ‖c - (s:ℝ) • z‖ ^ p)
      (-p * ‖c - (t:ℝ) • z‖ ^ (p - 2) *
        inner ℝ (c - (t:ℝ) • z) z) t := by
  set w : ℝ → X := fun s => c - (s:ℝ) • z
  have hsmul : HasDerivAt (fun s : ℝ => (s:ℝ) • z) z t := by
    simpa using (hasDerivAt_id' t).smul_const z
  have hw' : HasDerivAt w (-(z)) t := hsmul.const_sub c
  have hq : HasDerivAt (fun s : ℝ => ‖w s‖ ^ 2)
      (-2 * inner ℝ (w t) z) t := by
    simpa [w, two_mul, inner_neg_right, real_inner_comm,
      mul_comm, mul_left_comm, mul_assoc] using hw'.norm_sq
  have hqpos : ‖w t‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hpow := HasDerivAt.rpow_const hq (p := p / 2) (Or.inl hqpos)
  refine (hpow.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by
      show ‖c - (s:ℝ) • z‖ ^ p =
        (‖c - (s:ℝ) • z‖ ^ 2) ^ (p / 2)
      exact norm_rpow_eq_norm_sq_rpow _ _)).congr_deriv ?_
  rw [show (‖w t‖ ^ 2) ^ (p / 2 - 1) = ‖w t‖ ^ (p - 2) from
      norm_sq_rpow_eq_norm_rpow _ _]
  simp [w, two_mul, mul_comm, mul_left_comm, mul_assoc]

theorem norm_sub_smul_second_deriv
    [InnerProductSpace ℝ X] (c z : X) (p t : ℝ)
    (hw : c - (t:ℝ) • z ≠ 0) :
    deriv (deriv (fun s : ℝ => ‖c - (s:ℝ) • z‖ ^ p)) t =
      p * (p - 2) * ‖c - (t:ℝ) • z‖ ^ (p - 4) *
        (inner ℝ (c - (t:ℝ) • z) z) ^ 2 +
      p * ‖c - (t:ℝ) • z‖ ^ (p - 2) * ‖z‖ ^ 2 := by
  set w : ℝ → X := fun s => c - (s:ℝ) • z
  have hsmul : HasDerivAt (fun s : ℝ => (s:ℝ) • z) z t := by
    simpa using (hasDerivAt_id' t).smul_const z
  have hw' : HasDerivAt w (-(z)) t := hsmul.const_sub c
  have ha : HasDerivAt (fun s : ℝ => inner ℝ (w s) z) (-(‖z‖ ^ 2)) t := by
    simpa [w, inner_zero_right, inner_neg_right, real_inner_comm,
      real_inner_self_eq_norm_sq] using
      HasDerivAt.inner (𝕜 := ℝ) hw' (hasDerivAt_const t z)
  have hpow : ((p - 2) - 2 : ℝ) = p - 4 := by ring
  have hrad : HasDerivAt (fun s : ℝ => ‖c - (s:ℝ) • z‖ ^ (p - 2))
      (-(p - 2) * ‖c - (t:ℝ) • z‖ ^ (p - 4) *
        inner ℝ (c - (t:ℝ) • z) z) t := by
    simpa only [hpow] using norm_sub_smul_hasDerivAt c z (p - 2) t hw
  have hprod := hrad.mul ha
  have hsecondExpr :
      HasDerivAt
        (fun s : ℝ => -p *
          (‖c - (s:ℝ) • z‖ ^ (p - 2) *
            inner ℝ (c - (s:ℝ) • z) z))
        (-p *
          (-(p - 2) * ‖c - (t:ℝ) • z‖ ^ (p - 4) *
              inner ℝ (c - (t:ℝ) • z) z * inner ℝ (c - (t:ℝ) • z) z +
            ‖c - (t:ℝ) • z‖ ^ (p - 2) * -(‖z‖ ^ 2))) t := by
    refine (hprod.const_mul (-p)).congr_of_eventuallyEq ?_
    filter_upwards with s
    show -p * (‖c - (s:ℝ) • z‖ ^ (p - 2) *
        inner ℝ (c - (s:ℝ) • z) z) =
      -p * ((fun s : ℝ => ‖c - (s:ℝ) • z‖ ^ (p - 2)) *
        fun s : ℝ => inner ℝ (w s) z) s
    simp [Pi.mul_apply, w]
  have hne : ∀ᶠ s in nhds t, c - (s:ℝ) • z ≠ 0 :=
    hw'.continuousAt.eventually_ne (by simpa [w] using hw)
  have hfirstEq :
      deriv (fun s : ℝ => ‖c - (s:ℝ) • z‖ ^ p) =ᶠ[nhds t]
        (fun s : ℝ => -p *
          (‖c - (s:ℝ) • z‖ ^ (p - 2) * inner ℝ (c - (s:ℝ) • z) z)) := by
    filter_upwards [hne] with s hs
    have h := (norm_sub_smul_hasDerivAt c z p s hs).deriv
    simpa [mul_assoc] using h
  have hderiv2 :
      deriv (deriv (fun s : ℝ => ‖c - (s:ℝ) • z‖ ^ p)) t =
        deriv (fun s : ℝ => -p *
          (‖c - (s:ℝ) • z‖ ^ (p - 2) * inner ℝ (c - (s:ℝ) • z) z)) t :=
    Filter.EventuallyEq.deriv_eq hfirstEq
  rw [hderiv2, hsecondExpr.deriv]
  simp [w, mul_add, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg,
    sub_sub]
  ring

theorem translatedCrossLine_eq_norm_sub_smul
    [InnerProductSpace ℝ X] (kappa : ℝ) (center x y : X) :
    translatedCrossLine kappa center x y =
      fun t : ℝ => ‖center - (t:ℝ) • (x + y)‖ ^ (-kappa) := by
  funext t
  simp [translatedCrossLine, translatedCrossKernel, smul_add, sub_sub]

theorem translatedCrossLine_contDiffOn
    [InnerProductSpace ℝ X] (kappa : ℝ) (center x y : X)
    (h : ∀ t ∈ Set.Icc (0:ℝ) 1, center - (t:ℝ) • (x + y) ≠ 0) :
    ContDiffOn ℝ 2 (translatedCrossLine kappa center x y) (Set.Icc (0:ℝ) 1) := by
  rw [translatedCrossLine_eq_norm_sub_smul]
  have haff : ContDiffOn ℝ 2
      (fun t : ℝ => center - (t:ℝ) • (x + y)) (Set.Icc (0:ℝ) 1) := by
    fun_prop
  refine (haff.norm (𝕜 := ℝ) (fun t ht => h t ht)).rpow_const_of_ne (fun t ht => ?_)
  exact norm_ne_zero_iff.mpr (h t ht)

theorem translatedCrossLine_second_deriv
    [InnerProductSpace ℝ X] (kappa : ℝ) (center x y : X) (t : ℝ)
    (h : center - (t:ℝ) • (x + y) ≠ 0) :
    deriv (deriv (translatedCrossLine kappa center x y)) t =
      kappa * (kappa + 2) *
        ‖center - (t:ℝ) • (x + y)‖ ^ (-kappa - 4) *
        (inner ℝ (center - (t:ℝ) • (x + y)) (x + y)) ^ 2 -
      kappa *
        ‖center - (t:ℝ) • (x + y)‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by
  rw [translatedCrossLine_eq_norm_sub_smul]
  rw [norm_sub_smul_second_deriv center (x + y) (-kappa) t h]
  ring

theorem translatedCrossLine_second_deriv_abs_le
    [InnerProductSpace ℝ X] (kappa : ℝ) (hk : 0 ≤ kappa)
    (center x y : X) (t : ℝ)
    (h : center - (t:ℝ) • (x + y) ≠ 0) :
    |deriv (deriv (translatedCrossLine kappa center x y)) t| ≤
      kappa * (kappa + 1) *
        ‖center - (t:ℝ) • (x + y)‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by
  set w : X := center - (t:ℝ) • (x + y)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr h
  have hcs : |inner ℝ w (x + y)| ≤ ‖w‖ * ‖x + y‖ :=
    abs_real_inner_le_norm w (x + y)
  have ha2 : (inner ℝ w (x + y)) ^ 2 ≤ ‖w‖ ^ 2 * ‖x + y‖ ^ 2 := by
    have habs : |inner ℝ w (x + y)| ≤ |‖w‖ * ‖x + y‖| := by
      rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hcs
    have hsq := sq_le_sq.mpr habs
    nlinarith [hsq, norm_nonneg w, norm_nonneg (x + y)]
  have hpow : ‖w‖ ^ (-kappa - 4) * ‖w‖ ^ 2 = ‖w‖ ^ (-kappa - 2) := by
    conv_lhs => rw [← Real.rpow_natCast ‖w‖ 2]
    rw [← Real.rpow_add hwpos]
    congr 1
    ring
  have hfirstNonneg :
      0 ≤ kappa * (kappa + 2) * ‖w‖ ^ (-kappa - 4) *
        (inner ℝ w (x + y)) ^ 2 := by
    positivity
  have hM : 0 ≤ kappa * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by
    positivity
  have hfirstLe :
      kappa * (kappa + 2) * ‖w‖ ^ (-kappa - 4) *
          (inner ℝ w (x + y)) ^ 2 -
        kappa * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 ≤
      kappa * (kappa + 1) * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by
    have hmul :
        kappa * (kappa + 2) * ‖w‖ ^ (-kappa - 4) *
            (inner ℝ w (x + y)) ^ 2 ≤
          kappa * (kappa + 2) * ‖w‖ ^ (-kappa - 4) *
            (‖w‖ ^ 2 * ‖x + y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left ha2
        (by positivity)
    calc
      kappa * (kappa + 2) * ‖w‖ ^ (-kappa - 4) *
          (inner ℝ w (x + y)) ^ 2 -
        kappa * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 ≤
        kappa * (kappa + 2) * ‖w‖ ^ (-kappa - 4) *
            (‖w‖ ^ 2 * ‖x + y‖ ^ 2) -
          kappa * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by
          linarith [hmul]
      _ = kappa * (kappa + 2) *
            (‖w‖ ^ (-kappa - 4) * ‖w‖ ^ 2) * ‖x + y‖ ^ 2 -
          kappa * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by
          ring
      _ = kappa * (kappa + 1) * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by
          rw [hpow]
          ring
  have hlower :
      -(kappa * (kappa + 1) * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2) ≤
        kappa * (kappa + 2) * ‖w‖ ^ (-kappa - 4) *
          (inner ℝ w (x + y)) ^ 2 -
          kappa * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by
    have hcoef : kappa ≤ kappa * (kappa + 1) := by nlinarith [sq_nonneg kappa]
    have hMle :
        kappa * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 ≤
          kappa * (kappa + 1) * ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by
      have hnn : 0 ≤ ‖w‖ ^ (-kappa - 2) * ‖x + y‖ ^ 2 := by positivity
      nlinarith [hcoef, hnn, mul_nonneg (by positivity : (0:ℝ) ≤ kappa) hnn]
    linarith [hfirstNonneg, hM, hMle]
  rw [translatedCrossLine_second_deriv kappa center x y t h]
  exact abs_le.mpr ⟨hlower, hfirstLe⟩

theorem translatedCrossLine_hasDerivAt_zero
    [InnerProductSpace ℝ X] (kappa : ℝ) (center x y : X)
    (h : center ≠ 0) :
    HasDerivAt (translatedCrossLine kappa center x y)
      (kappa * ‖center‖ ^ (-kappa - 2) *
        inner ℝ center (x + y)) 0 := by
  have hline : translatedCrossLine kappa center x y =
      fun t : ℝ => ‖center - (t:ℝ) • (x + y)‖ ^ (-kappa) := by
    funext t
    simp [translatedCrossLine, translatedCrossKernel, smul_add, sub_sub]
  rw [hline]
  have h0 : center - (0:ℝ) • (x + y) ≠ 0 := by
    rwa [zero_smul, sub_zero]
  simpa [zero_smul, sub_zero, neg_neg] using
    norm_sub_smul_hasDerivAt center (x + y) (-kappa) 0 h0

theorem translatedCrossKernel_swap (kappa : ℝ) (center : X) (x y : X) :
    translatedCrossKernel kappa center x y = translatedCrossKernel kappa center y x := by
  have h : center - x - y = center - y - x := by abel
  simp [translatedCrossKernel, h]

theorem translatedCrossKernel_le_of_lowerBound
    (kappa L : ℝ) (center x y : X) (hk : 0 ≤ kappa) (hL : 0 < L)
    (hsep : L / 2 ≤ ‖center - x - y‖) :
    translatedCrossKernel kappa center x y ≤ 2 ^ kappa * L ^ (-kappa) := by
  have hL2 : 0 < L / 2 := by positivity
  have hk' : -kappa ≤ 0 := neg_nonpos.mpr hk
  have hpow : (L / 2) ^ (-kappa) = 2 ^ kappa * L ^ (-kappa) := by
    calc
      (L / 2) ^ (-kappa) = ((L / 2)⁻¹) ^ kappa :=
        Real.rpow_neg_eq_inv_rpow _ _
      _ = (2 / L) ^ kappa := by rw [inv_div]
      _ = 2 ^ kappa / L ^ kappa :=
        Real.div_rpow (by norm_num) (le_of_lt hL) kappa
      _ = 2 ^ kappa * L ^ (-kappa) := by
        rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hL)]
  calc
    translatedCrossKernel kappa center x y =
        ‖center - x - y‖ ^ (-kappa) := rfl
    _ ≤ (L / 2) ^ (-kappa) :=
      Real.rpow_le_rpow_of_nonpos hL2 hsep hk'
    _ = 2 ^ kappa * L ^ (-kappa) := hpow

/-- The geometric separation estimate behind Lemma 3.2: two points in a ball
of radius `R` are separated from `L e` by at least `L/2` once `L >= 4R`. -/
theorem translatedCrossKernel_separation_of_mem_ball
    [NormedSpace ℝ X] {R L : ℝ} {e x y : X}
    (he : ‖e‖ = 1) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R)
    (hL : 4 * R ≤ L) :
    L / 2 ≤ ‖(L : ℝ) • e - x - y‖ := by
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  have hL0 : 0 ≤ L := by nlinarith
  have hxy : ‖x + y‖ ≤ 2 * R := by
    calc
      ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
      _ ≤ R + R := add_le_add hx hy
      _ = 2 * R := by ring
  have hnorm : ‖(L : ℝ) • e‖ = L := by
    rw [norm_smul, he, Real.norm_eq_abs, mul_one, abs_of_nonneg hL0]
  have hrev : L - 2 * R ≤ ‖(L : ℝ) • e - x - y‖ := by
    have hkey : (L : ℝ) • e - x - y = (L : ℝ) • e - (x + y) := by abel
    rw [hkey]
    have h := norm_sub_norm_le ((L : ℝ) • e) (x + y)
    rw [hnorm] at h
    nlinarith
  calc
    L / 2 ≤ L - 2 * R := by nlinarith
    _ ≤ ‖(L : ℝ) • e - x - y‖ := hrev

theorem kernelCrossPairing_le_of_abs_integrable
    [MeasurableSpace X] (K : X → X → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hK : ∀ x y, |K x y| ≤ C)
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    (u v : X → ℝ)
    (hu : MeasureTheory.Integrable (fun x => |u x|) mu)
    (hv : MeasureTheory.Integrable (fun x => |v x|) mu) :
    |kernelCrossPairing K mu u v| ≤
      C * (∫ x, |u x| ∂mu) * (∫ y, |v y| ∂mu) := by
  have hprod : MeasureTheory.Integrable
      (fun z : X × X => |u z.1| * |v z.2|) (mu.prod mu) :=
    hu.mul_prod hv
  have hprodC : MeasureTheory.Integrable
      (fun z : X × X => C * (|u z.1| * |v z.2|)) (mu.prod mu) :=
    hprod.const_mul C
  have hpoint : ∀ z : X × X,
      |u z.1 * v z.2 * K z.1 z.2| ≤ C * (|u z.1| * |v z.2|) := by
    intro z
    rcases z with ⟨x, y⟩
    have hxy := hK x y
    calc
      |u x * v y * K x y| = |u x| * |v y| * |K x y| := by simp only [abs_mul]
      _ = |K x y| * (|u x| * |v y|) := by ring
      _ ≤ C * (|u x| * |v y|) :=
        mul_le_mul_of_nonneg_right hxy
          (mul_nonneg (abs_nonneg (u x)) (abs_nonneg (v y)))
  have hmono : ∫ z, |u z.1 * v z.2 * K z.1 z.2| ∂(mu.prod mu) ≤
      ∫ z, C * (|u z.1| * |v z.2|) ∂(mu.prod mu) :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_of_all _ fun _ => abs_nonneg _) hprodC
      (MeasureTheory.ae_of_all _ hpoint)
  have habs : |∫ z, u z.1 * v z.2 * K z.1 z.2 ∂(mu.prod mu)| ≤
      ∫ z, |u z.1 * v z.2 * K z.1 z.2| ∂(mu.prod mu) :=
    MeasureTheory.abs_integral_le_integral_abs
  have hprodEq : ∫ z, |u z.1| * |v z.2| ∂(mu.prod mu) =
      (∫ x, |u x| ∂mu) * ∫ y, |v y| ∂mu :=
    MeasureTheory.integral_prod_mul (fun x => |u x|) (fun y => |v y|)
  have hconst : ∫ z, C * (|u z.1| * |v z.2|) ∂(mu.prod mu) =
      C * ∫ z, |u z.1| * |v z.2| ∂(mu.prod mu) :=
    MeasureTheory.integral_const_mul C _
  have key : |∫ z, u z.1 * v z.2 * K z.1 z.2 ∂(mu.prod mu)| ≤
      C * (∫ x, |u x| ∂mu) * (∫ y, |v y| ∂mu) := by
    calc
      |∫ z, u z.1 * v z.2 * K z.1 z.2 ∂(mu.prod mu)| ≤
          ∫ z, |u z.1 * v z.2 * K z.1 z.2| ∂(mu.prod mu) := habs
      _ ≤ ∫ z, C * (|u z.1| * |v z.2|) ∂(mu.prod mu) := hmono
      _ = C * (∫ x, |u x| ∂mu) * (∫ y, |v y| ∂mu) := by
        rw [hconst, hprodEq]
        ring
  simpa [kernelCrossPairing] using key

theorem integral_abs_le_measure_rpow_lpNorm
    [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] [MeasureTheory.IsFiniteMeasure mu]
    (u : X → ℝ) (hu : MeasureTheory.MemLp u 2 mu) :
    ∫ x, |u x| ∂mu ≤ mu.real Set.univ ^ (1 / 2 : ℝ) *
      MeasureTheory.lpNorm u 2 mu := by
  have hpq : Real.HolderConjugate (2 : ℝ) 2 :=
    by rw [Real.holderConjugate_iff]; norm_num
  have huabs : MeasureTheory.MemLp (abs u) 2 mu :=
    MeasureTheory.MemLp.abs hu
  have hone : MeasureTheory.MemLp (fun _ : X => (1 : ℝ)) 2 mu :=
    by simpa [ENNReal.ofReal_ofNat] using MeasureTheory.memLp_const 1
  have huabs' : MeasureTheory.MemLp (abs u) (ENNReal.ofReal 2) mu :=
    by simpa [ENNReal.ofReal_ofNat] using huabs
  have hone' : MeasureTheory.MemLp (fun _ : X => (1 : ℝ)) (ENNReal.ofReal 2) mu :=
    by simpa [ENNReal.ofReal_ofNat] using hone
  have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := abs u) (g := fun _ => (1 : ℝ)) hpq
    (MeasureTheory.ae_of_all _ fun x => abs_nonneg (u x))
    (MeasureTheory.ae_of_all _ fun _ => zero_le_one) huabs' hone'
  simp only [Pi.abs_apply, mul_one] at h
  have hmeasure : ∫ x, (1 : ℝ) ∂mu = mu.real Set.univ := by
    simp
  calc
    ∫ x, |u x| ∂mu = ∫ x, |u x| * (1 : ℝ) ∂mu := by simp
    _ ≤ (∫ x, |u x| ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
        (∫ x, (1 : ℝ) ∂mu) ^ (1 / 2 : ℝ) :=
      by simpa only [mul_one, Real.one_rpow] using h
    _ = (∫ x, |u x| ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
        mu.real Set.univ ^ (1 / 2 : ℝ) := by rw [hmeasure]
    _ = mu.real Set.univ ^ (1 / 2 : ℝ) *
        MeasureTheory.lpNorm u 2 mu := by
      rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp)
        (MeasureTheory.MemLp.aestronglyMeasurable hu)]
      simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat]
      norm_num
      ring_nf

theorem kernelCrossPairing_Lp_le
    [MeasurableSpace X] (K : X → X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ x y, |K x y| ≤ C)
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    [MeasureTheory.IsFiniteMeasure mu]
    (u v : MeasureTheory.Lp ℝ 2 mu) :
    |kernelCrossPairing K mu ⇑u ⇑v| ≤
      C * mu.real Set.univ * ‖u‖ * ‖v‖ := by
  have hu : MeasureTheory.MemLp ⇑u 2 mu := MeasureTheory.Lp.memLp u
  have hv : MeasureTheory.MemLp ⇑v 2 mu := MeasureTheory.Lp.memLp v
  have hL1u : ∫ x, |u x| ∂mu ≤
      mu.real Set.univ ^ (1 / 2 : ℝ) * MeasureTheory.lpNorm ⇑u 2 mu :=
    integral_abs_le_measure_rpow_lpNorm mu ⇑u hu
  have hL1v : ∫ x, |v x| ∂mu ≤
      mu.real Set.univ ^ (1 / 2 : ℝ) * MeasureTheory.lpNorm ⇑v 2 mu :=
    integral_abs_le_measure_rpow_lpNorm mu ⇑v hv
  have hnormu : MeasureTheory.lpNorm ⇑u 2 mu = ‖u‖ := by
    rw [MeasureTheory.Lp.norm_def,
      MeasureTheory.toReal_eLpNorm (MeasureTheory.Lp.aestronglyMeasurable u)]
  have hnormv : MeasureTheory.lpNorm ⇑v 2 mu = ‖v‖ := by
    rw [MeasureTheory.Lp.norm_def,
      MeasureTheory.toReal_eLpNorm (MeasureTheory.Lp.aestronglyMeasurable v)]
  have hu1 : MeasureTheory.MemLp ⇑u 1 mu :=
    hu.mono_exponent (by norm_num)
  have hv1 : MeasureTheory.MemLp ⇑v 1 mu :=
    hv.mono_exponent (by norm_num)
  have huabsInt : MeasureTheory.Integrable (fun x => |⇑u x|) mu :=
    (MeasureTheory.memLp_one_iff_integrable.1 hu1).abs
  have hvabsInt : MeasureTheory.Integrable (fun x => |⇑v x|) mu :=
    (MeasureTheory.memLp_one_iff_integrable.1 hv1).abs
  have hbound := kernelCrossPairing_le_of_abs_integrable K C
    hC hK mu ⇑u ⇑v huabsInt hvabsInt
  rw [hnormu] at hL1u
  rw [hnormv] at hL1v
  have hn : 0 ≤ mu.real Set.univ := MeasureTheory.measureReal_nonneg
  have hprod : (∫ x, |u x| ∂mu) * (∫ x, |v x| ∂mu) ≤
      (mu.real Set.univ ^ (1 / 2 : ℝ) * ‖u‖) *
        (mu.real Set.univ ^ (1 / 2 : ℝ) * ‖v‖) := by
    apply mul_le_mul hL1u hL1v
    · exact MeasureTheory.integral_nonneg fun _ => abs_nonneg _
    · positivity
  calc
    |kernelCrossPairing K mu ⇑u ⇑v| ≤
        C * ((∫ x, |u x| ∂mu) * (∫ x, |v x| ∂mu)) := by
      simpa [mul_assoc] using hbound
    _ ≤ C * ((mu.real Set.univ ^ (1 / 2 : ℝ) * ‖u‖) *
        (mu.real Set.univ ^ (1 / 2 : ℝ) * ‖v‖)) := by
      exact mul_le_mul_of_nonneg_left hprod hC
    _ = C * mu.real Set.univ * ‖u‖ * ‖v‖ := by
      simp only [← Real.sqrt_eq_rpow]
      have hsqrt : √(mu.real Set.univ) * √(mu.real Set.univ) =
          mu.real Set.univ := Real.mul_self_sqrt hn
      calc
        C * (√(mu.real Set.univ) * ‖u‖ *
            (√(mu.real Set.univ) * ‖v‖)) =
            C * ((√(mu.real Set.univ) * √(mu.real Set.univ)) *
              (‖u‖ * ‖v‖)) := by ring
        _ = C * (mu.real Set.univ * (‖u‖ * ‖v‖)) := by rw [hsqrt]
        _ = C * mu.real Set.univ * ‖u‖ * ‖v‖ := by ring

/-- The squared global Gagliardo seminorm.  The measure is explicit so that
the definition is available before specializing to Euclidean volume. -/
noncomputable def gagliardoSeminormSq
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X) (u : X → ℝ) : ℝ :=
  ∫ z : X × X, gagliardoIntegrand kappa u z ∂(mu.prod mu)

theorem gagliardoSeminormSq_nonneg
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X) (u : X → ℝ) :
    0 ≤ gagliardoSeminormSq kappa mu u :=
  MeasureTheory.integral_nonneg (gagliardoIntegrand_nonneg kappa u)

theorem gagliardoSeminormSq_zero
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X) :
    gagliardoSeminormSq kappa mu (0 : X → ℝ) = 0 := by
  show ∫ z : X × X, gagliardoIntegrand kappa (0 : X → ℝ) z ∂(mu.prod mu) = 0
  simp [gagliardoIntegrand]

theorem gagliardoIntegrand_smul
    (kappa t : ℝ) (u : X → ℝ) (z : X × X) :
    gagliardoIntegrand kappa (fun x => t * u x) z =
      t ^ 2 * gagliardoIntegrand kappa u z := by
  simp only [gagliardoIntegrand, sub_mul, mul_pow]
  ring

theorem gagliardoIntegrand_add_add_sub
    (kappa : ℝ) (u v : X → ℝ) (z : X × X) :
    gagliardoIntegrand kappa (u + v) z + gagliardoIntegrand kappa (u - v) z =
      2 * gagliardoIntegrand kappa u z + 2 * gagliardoIntegrand kappa v z := by
  simp only [gagliardoIntegrand, Pi.add_apply, Pi.sub_apply]
  ring

theorem gagliardoSeminormSq_smul
    [MeasurableSpace X] (kappa t : ℝ) (mu : MeasureTheory.Measure X)
    (u : X → ℝ) :
    gagliardoSeminormSq kappa mu (fun x => t * u x) =
      t ^ 2 * gagliardoSeminormSq kappa mu u := by
  have hpoint : ∀ z : X × X,
      gagliardoIntegrand kappa (fun x => t * u x) z =
        t ^ 2 * gagliardoIntegrand kappa u z :=
    gagliardoIntegrand_smul kappa t u
  calc
    gagliardoSeminormSq kappa mu (fun x => t * u x) =
        ∫ z, gagliardoIntegrand kappa (fun x => t * u x) z ∂(mu.prod mu) := rfl
    _ = ∫ z, t ^ 2 * gagliardoIntegrand kappa u z ∂(mu.prod mu) :=
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpoint)
    _ = t ^ 2 * gagliardoSeminormSq kappa mu u :=
      MeasureTheory.integral_const_mul _ _

theorem gagliardoSeminormSq_add_add_sub_of_integrable
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    (u v : X → ℝ)
    (hu : MeasureTheory.Integrable (fun z : X × X => gagliardoIntegrand kappa u z)
      (mu.prod mu))
    (hv : MeasureTheory.Integrable (fun z : X × X => gagliardoIntegrand kappa v z)
      (mu.prod mu))
    (huv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa (u + v) z) (mu.prod mu))
    (hsv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa (u - v) z) (mu.prod mu)) :
    gagliardoSeminormSq kappa mu (u + v) + gagliardoSeminormSq kappa mu (u - v) =
      2 * gagliardoSeminormSq kappa mu u + 2 * gagliardoSeminormSq kappa mu v := by
  have hpoint : ∀ z : X × X,
      gagliardoIntegrand kappa (u + v) z + gagliardoIntegrand kappa (u - v) z =
        2 * gagliardoIntegrand kappa u z + 2 * gagliardoIntegrand kappa v z :=
    gagliardoIntegrand_add_add_sub kappa u v
  have hadd := MeasureTheory.integral_add huv hsv
  have hright := MeasureTheory.integral_add (hu.const_mul 2) (hv.const_mul 2)
  calc
    gagliardoSeminormSq kappa mu (u + v) + gagliardoSeminormSq kappa mu (u - v) =
        ∫ z, gagliardoIntegrand kappa (u + v) z +
          gagliardoIntegrand kappa (u - v) z ∂(mu.prod mu) := hadd.symm
    _ = ∫ z, 2 * gagliardoIntegrand kappa u z +
        2 * gagliardoIntegrand kappa v z ∂(mu.prod mu) :=
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpoint)
    _ = 2 * gagliardoSeminormSq kappa mu u +
        2 * gagliardoSeminormSq kappa mu v := by
      rw [hright, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rfl

theorem gagliardoSeminormSq_congr_ae
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] {u v : X → ℝ} (h : u =ᵐ[mu] v) :
    gagliardoSeminormSq kappa mu u = gagliardoSeminormSq kappa mu v := by
  apply MeasureTheory.integral_congr_ae
  have hfst : (fun z : X × X => u z.1) =ᵐ[mu.prod mu] (fun z : X × X => v z.1) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := mu) (ν := mu)).ae_eq_comp h
  have hsnd : (fun z : X × X => u z.2) =ᵐ[mu.prod mu] (fun z : X × X => v z.2) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := mu) (ν := mu)).ae_eq_comp h
  filter_upwards [hfst, hsnd] with z hz1 hz2
  show gagliardoIntegrand kappa u z = gagliardoIntegrand kappa v z
  simp only [gagliardoIntegrand, hz1, hz2]

/-- Functions with zero exterior values on the complement of `G`. -/
def zeroExterior (G : Set X) (u : X → ℝ) : Prop :=
  ∀ x ∉ G, u x = 0

open Classical in
/-- The representative of `u` used by the zero-exterior problem: it is `u` on
`G` and vanishes on the ambient complement. -/
noncomputable def zeroExtension (G : Set X) (u : X → ℝ) : X → ℝ :=
  fun x => if x ∈ G then u x else 0

theorem zeroExtension_eq_of_zeroExterior
    {G : Set X} {u : X → ℝ} (h : zeroExterior G u) :
    zeroExtension G u = u := by
  funext x
  by_cases hx : x ∈ G
  · simp [zeroExtension, hx]
  · simp [zeroExtension, hx, h x hx]

theorem zeroExtension_congr_ae
    [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    (G : Set X) {u v : X → ℝ} (h : u =ᵐ[mu] v) :
    zeroExtension G u =ᵐ[mu] zeroExtension G v := by
  filter_upwards [h] with x hx
  by_cases hxG : x ∈ G
  · simp [zeroExtension, hxG, hx]
  · simp [zeroExtension, hxG]

theorem zeroExtension_smul
    (G : Set X) (t : ℝ) (u : X → ℝ) :
    zeroExtension G (t • u) = fun x => t * zeroExtension G u x := by
  funext x
  by_cases hxG : x ∈ G
  · simp [zeroExtension, hxG, Pi.smul_apply, smul_eq_mul]
  · simp [zeroExtension, hxG]

theorem zeroExtension_add
    (G : Set X) (u v : X → ℝ) :
    zeroExtension G (u + v) = zeroExtension G u + zeroExtension G v := by
  funext x
  by_cases hxG : x ∈ G
  · simp [zeroExtension, hxG, Pi.add_apply]
  · simp [zeroExtension, hxG, Pi.add_apply]

theorem zeroExtension_sub
    (G : Set X) (u v : X → ℝ) :
    zeroExtension G (u - v) = zeroExtension G u - zeroExtension G v := by
  funext x
  by_cases hxG : x ∈ G
  · simp [zeroExtension, hxG, Pi.sub_apply]
  · simp [zeroExtension, hxG, Pi.sub_apply]

theorem zeroExtension_zero (G : Set X) :
    zeroExtension G (0 : X → ℝ) = 0 := by
  funext x
  by_cases hxG : x ∈ G
  · simp [zeroExtension, hxG]
  · simp [zeroExtension, hxG]

theorem zeroExtension_univ (u : X → ℝ) :
    zeroExtension Set.univ u = u := by
  funext x
  simp [zeroExtension]

theorem gagliardoIntegrand_aestronglyMeasurable
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] {u : X → ℝ}
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu))
    (hu : MeasureTheory.AEStronglyMeasurable u mu) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoIntegrand kappa u z)
      (mu.prod mu) := by
  have hfst : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => u z.1) (mu.prod mu) :=
    hu.comp_fst
  have hsnd : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => u z.2) (mu.prod mu) :=
    hu.comp_snd
  have hdiff : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => u z.1 - u z.2)
      (mu.prod mu) :=
    hfst.sub hsnd
  exact (hdiff.pow 2).mul hK

theorem gagliardoIntegrand_add_le
    (kappa : ℝ) (u v : X → ℝ) (z : X × X) :
    gagliardoIntegrand kappa (u + v) z ≤
      2 * gagliardoIntegrand kappa u z + 2 * gagliardoIntegrand kappa v z := by
  simp only [gagliardoIntegrand, Pi.add_apply]
  have hk : 0 ≤ gagliardoKernel kappa z.1 z.2 := by
    unfold gagliardoKernel
    exact Real.rpow_nonneg (norm_nonneg _) _
  nlinarith [sq_nonneg
    ((u z.1 - u z.2) - (v z.1 - v z.2))]

def finiteGagliardoEnergy
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) (u : X → ℝ) : Prop :=
  MeasureTheory.MemLp (zeroExtension G u) 2 mu ∧
    MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa (zeroExtension G u) z)
      (mu.prod mu)

namespace finiteGagliardoEnergy

/-- The `L²` representative of a finite-energy zero-exterior function. -/
noncomputable def toLp
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) (u : X → ℝ)
    (hu : finiteGagliardoEnergy kappa mu G u) :
    MeasureTheory.Lp ℝ 2 mu :=
  MeasureTheory.MemLp.toLp (zeroExtension G u) hu.1

theorem coeFn_toLp
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) (u : X → ℝ)
    (hu : finiteGagliardoEnergy kappa mu G u) :
    ⇑(toLp kappa mu G u hu) =ᵐ[mu] zeroExtension G u :=
  MeasureTheory.MemLp.coeFn_toLp hu.1

theorem norm_toLp
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) (u : X → ℝ)
    (hu : finiteGagliardoEnergy kappa mu G u) :
    ‖toLp kappa mu G u hu‖ =
      ENNReal.toReal (MeasureTheory.eLpNorm (zeroExtension G u) 2 mu) :=
  MeasureTheory.Lp.norm_toLp (zeroExtension G u) hu.1

theorem integral_toLp
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) (u : X → ℝ)
    (hu : finiteGagliardoEnergy kappa mu G u) :
    (∫ x, ⇑(toLp kappa mu G u hu) x ∂mu) =
      ∫ x, zeroExtension G u x ∂mu :=
  MeasureTheory.integral_congr_ae (coeFn_toLp kappa mu G u hu)

theorem integral_toLp_univ
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (u : X → ℝ)
    (hu : finiteGagliardoEnergy kappa mu Set.univ u) {m : ℝ}
    (hm : ∫ x, u x ∂mu = m) :
    (∫ x, ⇑(toLp kappa mu Set.univ u hu) x ∂mu) = m := by
  rw [integral_toLp, zeroExtension_univ]
  exact hm

end finiteGagliardoEnergy

theorem finiteGagliardoEnergy_zero
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) :
    finiteGagliardoEnergy kappa mu G (0 : X → ℝ) := by
  refine ⟨?_, ?_⟩
  · rw [zeroExtension_zero]
    exact MeasureTheory.MemLp.zero
  · rw [zeroExtension_zero]
    simpa [gagliardoIntegrand] using MeasureTheory.integrable_zero (mu.prod mu)

theorem finiteGagliardoEnergy_smul
    [MeasurableSpace X] (kappa t : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) {u : X → ℝ}
    (hu : finiteGagliardoEnergy kappa mu G u) :
    finiteGagliardoEnergy kappa mu G (t • u) := by
  refine ⟨?_, ?_⟩
  · rw [zeroExtension_smul]
    exact hu.1.const_smul t
  · rw [zeroExtension_smul]
    exact (hu.2.const_mul (t ^ 2)).congr
      (MeasureTheory.ae_of_all _ fun z =>
        (gagliardoIntegrand_smul kappa t (zeroExtension G u) z).symm)

theorem finiteGagliardoEnergy_add
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) {u v : X → ℝ}
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu))
    (hu : finiteGagliardoEnergy kappa mu G u)
    (hv : finiteGagliardoEnergy kappa mu G v) :
    finiteGagliardoEnergy kappa mu G (u + v) := by
  refine ⟨?_, ?_⟩
  · rw [zeroExtension_add]
    exact hu.1.add hv.1
  · rw [zeroExtension_add]
    have hf : MeasureTheory.AEStronglyMeasurable
        (fun z : X × X =>
          gagliardoIntegrand kappa (zeroExtension G u + zeroExtension G v) z)
        (mu.prod mu) :=
      gagliardoIntegrand_aestronglyMeasurable kappa mu hK
        (hu.1.aestronglyMeasurable.add hv.1.aestronglyMeasurable)
    have hg : MeasureTheory.Integrable
        (fun z : X × X =>
          2 * gagliardoIntegrand kappa (zeroExtension G u) z +
            2 * gagliardoIntegrand kappa (zeroExtension G v) z)
        (mu.prod mu) :=
      (hu.2.const_mul 2).add (hv.2.const_mul 2)
    have hnonneg : ∀ z : X × X,
        0 ≤ gagliardoIntegrand kappa (zeroExtension G u + zeroExtension G v) z :=
      fun z => gagliardoIntegrand_nonneg kappa _ z
    have hle : ∀ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G u + zeroExtension G v) z ≤
          2 * gagliardoIntegrand kappa (zeroExtension G u) z +
            2 * gagliardoIntegrand kappa (zeroExtension G v) z := by
      intro z
      exact gagliardoIntegrand_add_le kappa
        (zeroExtension G u) (zeroExtension G v) z
    exact hg.mono_nonneg hf
      (MeasureTheory.ae_of_all _ hnonneg)
      (MeasureTheory.ae_of_all _ hle)

theorem finiteGagliardoEnergy_neg
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) {u : X → ℝ}
    (hu : finiteGagliardoEnergy kappa mu G u) :
    finiteGagliardoEnergy kappa mu G (-u) := by
  have h := finiteGagliardoEnergy_smul kappa (-1) mu G hu
  rwa [neg_one_smul] at h

theorem finiteGagliardoEnergy_sub
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) {u v : X → ℝ}
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu))
    (hu : finiteGagliardoEnergy kappa mu G u)
    (hv : finiteGagliardoEnergy kappa mu G v) :
    finiteGagliardoEnergy kappa mu G (u - v) := by
  have hneg := finiteGagliardoEnergy_neg kappa mu G hv
  have h := finiteGagliardoEnergy_add kappa mu G hK hu hneg
  rwa [← sub_eq_add_neg] at h

def finiteGagliardoEnergySubmodule
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu)) :
    Submodule ℝ (X → ℝ) where
  carrier := {u | finiteGagliardoEnergy kappa mu G u}
  zero_mem' := finiteGagliardoEnergy_zero kappa mu G
  add_mem' := fun hu hv => finiteGagliardoEnergy_add kappa mu G hK hu hv
  smul_mem' := fun t u hu => finiteGagliardoEnergy_smul kappa t mu G hu

theorem finiteGagliardoEnergy_toLp_add
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu))
    {u v : X → ℝ} (hu : finiteGagliardoEnergy kappa mu G u)
    (hv : finiteGagliardoEnergy kappa mu G v) :
    finiteGagliardoEnergy.toLp kappa mu G (u + v)
        (finiteGagliardoEnergy_add kappa mu G hK hu hv) =
      finiteGagliardoEnergy.toLp kappa mu G u hu +
        finiteGagliardoEnergy.toLp kappa mu G v hv := by
  have hadd : zeroExtension G (u + v) =ᵐ[mu]
      zeroExtension G u + zeroExtension G v :=
    MeasureTheory.ae_of_all _ (fun x => by
      by_cases hx : x ∈ G <;> simp [zeroExtension, Pi.add_apply, hx])
  have h1 : MeasureTheory.MemLp (zeroExtension G (u + v)) 2 mu :=
    (finiteGagliardoEnergy_add kappa mu G hK hu hv).1
  have h2 : MeasureTheory.MemLp
      (zeroExtension G u + zeroExtension G v) 2 mu := hu.1.add hv.1
  have hcongr : MeasureTheory.MemLp.toLp
      (zeroExtension G (u + v)) h1 =
      MeasureTheory.MemLp.toLp
        (zeroExtension G u + zeroExtension G v) h2 :=
    MeasureTheory.MemLp.toLp_congr h1 h2 hadd
  refine hcongr.trans ?_
  exact MeasureTheory.MemLp.toLp_add hu.1 hv.1

theorem finiteGagliardoEnergy_toLp_smul
    [MeasurableSpace X] (kappa t : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    {u : X → ℝ} (hu : finiteGagliardoEnergy kappa mu G u) :
    finiteGagliardoEnergy.toLp kappa mu G (t • u)
        (finiteGagliardoEnergy_smul kappa t mu G hu) =
      t • finiteGagliardoEnergy.toLp kappa mu G u hu := by
  have hsmul : zeroExtension G (t • u) =ᵐ[mu]
      t • zeroExtension G u :=
    MeasureTheory.ae_of_all _ (fun x => by
      by_cases hx : x ∈ G <;> simp [zeroExtension, Pi.smul_apply, smul_eq_mul, hx])
  have h1 : MeasureTheory.MemLp (zeroExtension G (t • u)) 2 mu :=
    (finiteGagliardoEnergy_smul kappa t mu G hu).1
  have h2 : MeasureTheory.MemLp (t • zeroExtension G u) 2 mu :=
    hu.1.const_smul t
  have hcongr : MeasureTheory.MemLp.toLp
      (zeroExtension G (t • u)) h1 =
      MeasureTheory.MemLp.toLp (t • zeroExtension G u) h2 :=
    MeasureTheory.MemLp.toLp_congr h1 h2 hsmul
  refine hcongr.trans ?_
  exact MeasureTheory.MemLp.toLp_const_smul t hu.1

noncomputable def finiteGagliardoEnergy_toLpLinear
    [MeasurableSpace X] (kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu)) :
    finiteGagliardoEnergySubmodule kappa mu G hK →ₗ[ℝ] MeasureTheory.Lp ℝ 2 mu where
  toFun u := finiteGagliardoEnergy.toLp kappa mu G u.1 u.2
  map_add' u v := by
    exact finiteGagliardoEnergy_toLp_add kappa mu G hK u.2 v.2
  map_smul' t u := by
    exact finiteGagliardoEnergy_toLp_smul kappa t mu G u.2

/-- The zero-exterior quadratic form from equation `eq:form`. -/
noncomputable def zeroExteriorForm
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    (G : Set X) (u : X → ℝ) : ℝ :=
  (c / 2) * gagliardoSeminormSq kappa mu (zeroExtension G u)

theorem zeroExteriorForm_eq_of_zeroExterior
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    (G : Set X) {u : X → ℝ} (h : zeroExterior G u) :
    zeroExteriorForm c kappa mu G u =
      (c / 2) * gagliardoSeminormSq kappa mu u := by
  rw [zeroExteriorForm, zeroExtension_eq_of_zeroExterior h]

theorem zeroExteriorForm_congr_ae
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) {u v : X → ℝ} (h : u =ᵐ[mu] v) :
    zeroExteriorForm c kappa mu G u = zeroExteriorForm c kappa mu G v := by
  rw [zeroExteriorForm, zeroExteriorForm,
    gagliardoSeminormSq_congr_ae kappa mu (zeroExtension_congr_ae mu G h)]

theorem zeroExteriorForm_congr_zeroExtension_ae
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) {u v : X → ℝ}
    (h : zeroExtension G u =ᵐ[mu] zeroExtension G v) :
    zeroExteriorForm c kappa mu G u = zeroExteriorForm c kappa mu G v := by
  rw [zeroExteriorForm, zeroExteriorForm,
    gagliardoSeminormSq_congr_ae kappa mu h]

theorem zeroExteriorForm_zero
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    (G : Set X) :
    zeroExteriorForm c kappa mu G (0 : X → ℝ) = 0 := by
  rw [zeroExteriorForm, zeroExtension_zero, gagliardoSeminormSq_zero]
  ring

theorem zeroExteriorForm_add_congr_left_zero
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X) {u v : X → ℝ}
    (h : zeroExtension G u =ᵐ[mu] 0) :
    zeroExteriorForm c kappa mu G (u + v) =
      zeroExteriorForm c kappa mu G v := by
  apply zeroExteriorForm_congr_zeroExtension_ae
  rw [zeroExtension_add]
  filter_upwards [h] with x hx
  simp [hx]

theorem zeroExteriorForm_smul
    [MeasurableSpace X] (c kappa t : ℝ) (mu : MeasureTheory.Measure X)
    (G : Set X) (u : X → ℝ) :
    zeroExteriorForm c kappa mu G (t • u) =
      t ^ 2 * zeroExteriorForm c kappa mu G u := by
  rw [zeroExteriorForm, zeroExteriorForm, zeroExtension_smul,
    gagliardoSeminormSq_smul]
  ring

theorem zeroExteriorForm_add_add_sub_of_integrable
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    (G : Set X) (u v : X → ℝ)
    (hu : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa (zeroExtension G u) z) (mu.prod mu))
    (hv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa (zeroExtension G v) z) (mu.prod mu))
    (huv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G u + zeroExtension G v) z) (mu.prod mu))
    (hsv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G u - zeroExtension G v) z) (mu.prod mu)) :
    zeroExteriorForm c kappa mu G (u + v) +
        zeroExteriorForm c kappa mu G (u - v) =
      2 * zeroExteriorForm c kappa mu G u +
        2 * zeroExteriorForm c kappa mu G v := by
  have hq := gagliardoSeminormSq_add_add_sub_of_integrable kappa mu
    (zeroExtension G u) (zeroExtension G v) hu hv huv hsv
  rw [zeroExteriorForm, zeroExteriorForm, zeroExteriorForm, zeroExteriorForm,
    zeroExtension_add, zeroExtension_sub]
  calc
    c / 2 * gagliardoSeminormSq kappa mu (zeroExtension G u + zeroExtension G v) +
        c / 2 * gagliardoSeminormSq kappa mu (zeroExtension G u - zeroExtension G v) =
        c / 2 * (gagliardoSeminormSq kappa mu (zeroExtension G u + zeroExtension G v) +
          gagliardoSeminormSq kappa mu (zeroExtension G u - zeroExtension G v)) := by ring
    _ = c / 2 *
        (2 * gagliardoSeminormSq kappa mu (zeroExtension G u) +
          2 * gagliardoSeminormSq kappa mu (zeroExtension G v)) := by rw [hq]
    _ = 2 * (c / 2 * gagliardoSeminormSq kappa mu (zeroExtension G u)) +
        2 * (c / 2 * gagliardoSeminormSq kappa mu (zeroExtension G v)) := by ring

theorem zeroExteriorForm_nonneg
    [MeasurableSpace X] {c kappa : ℝ} (hc : 0 ≤ c)
    (mu : MeasureTheory.Measure X) (G : Set X) (u : X → ℝ) :
    0 ≤ zeroExteriorForm c kappa mu G u := by
  show (0:ℝ) ≤ (c / 2) *
    gagliardoSeminormSq kappa mu (zeroExtension G u)
  apply mul_nonneg
  · exact div_nonneg hc (by norm_num)
  · exact gagliardoSeminormSq_nonneg kappa mu (zeroExtension G u)

theorem gagliardoIntegrand_sub_sub_smul_left
    (kappa a : ℝ) (u v : X → ℝ) (z : X × X) :
    gagliardoIntegrand kappa (a • u + v) z -
        gagliardoIntegrand kappa (a • u - v) z =
      a * (gagliardoIntegrand kappa (u + v) z -
        gagliardoIntegrand kappa (u - v) z) := by
  rcases z with ⟨x, y⟩
  simp only [gagliardoIntegrand, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

theorem gagliardoIntegrand_sub_sub_add_left
    (kappa : ℝ) (u v w : X → ℝ) (z : X × X) :
    gagliardoIntegrand kappa (u + v + w) z -
        gagliardoIntegrand kappa (u + v - w) z =
      (gagliardoIntegrand kappa (u + w) z -
        gagliardoIntegrand kappa (u - w) z) +
        (gagliardoIntegrand kappa (v + w) z -
          gagliardoIntegrand kappa (v - w) z) := by
  rcases z with ⟨x, y⟩
  simp only [gagliardoIntegrand, Pi.add_apply, Pi.sub_apply]
  ring

theorem zeroExteriorForm_sub_sub_smul_left_of_integrable
    [MeasurableSpace X] (c kappa a : ℝ) (mu : MeasureTheory.Measure X)
    (G : Set X) (u v : X → ℝ)
    (huv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (a • u + v)) z) (mu.prod mu))
    (hsv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (a • u - v)) z) (mu.prod mu))
    (hpuv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (u + v)) z) (mu.prod mu))
    (hpsv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (u - v)) z) (mu.prod mu)) :
    zeroExteriorForm c kappa mu G (a • u + v) -
        zeroExteriorForm c kappa mu G (a • u - v) =
      a * (zeroExteriorForm c kappa mu G (u + v) -
        zeroExteriorForm c kappa mu G (u - v)) := by
  have hpoint : ∀ z : X × X,
      gagliardoIntegrand kappa (zeroExtension G (a • u + v)) z -
          gagliardoIntegrand kappa (zeroExtension G (a • u - v)) z =
      a * (gagliardoIntegrand kappa (zeroExtension G (u + v)) z -
          gagliardoIntegrand kappa (zeroExtension G (u - v)) z) := by
    intro z
    have hu : zeroExtension G (a • u) = fun x => a * zeroExtension G u x :=
      zeroExtension_smul G a u
    have huv' : zeroExtension G (a • u + v) =
        (fun x => a * zeroExtension G u x) + zeroExtension G v := by
      rw [zeroExtension_add, hu]
    have hsv' : zeroExtension G (a • u - v) =
        (fun x => a * zeroExtension G u x) - zeroExtension G v := by
      rw [zeroExtension_sub, hu]
    have hplus : zeroExtension G (u + v) = zeroExtension G u + zeroExtension G v :=
      zeroExtension_add G u v
    have hminus : zeroExtension G (u - v) = zeroExtension G u - zeroExtension G v :=
      zeroExtension_sub G u v
    rw [huv', hsv', hplus, hminus]
    exact gagliardoIntegrand_sub_sub_smul_left kappa a
      (zeroExtension G u) (zeroExtension G v) z
  have hleft : ∫ z : X × X,
      gagliardoIntegrand kappa (zeroExtension G (a • u + v)) z -
        gagliardoIntegrand kappa (zeroExtension G (a • u - v)) z ∂(mu.prod mu) =
        ∫ z : X × X,
          a * (gagliardoIntegrand kappa (zeroExtension G (u + v)) z -
            gagliardoIntegrand kappa (zeroExtension G (u - v)) z) ∂(mu.prod mu) := by
    exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpoint)
  have hright : ∫ z : X × X,
      a * (gagliardoIntegrand kappa (zeroExtension G (u + v)) z -
        gagliardoIntegrand kappa (zeroExtension G (u - v)) z) ∂(mu.prod mu) =
        a * (∫ z : X × X,
          gagliardoIntegrand kappa (zeroExtension G (u + v)) z -
            gagliardoIntegrand kappa (zeroExtension G (u - v)) z ∂(mu.prod mu)) :=
    MeasureTheory.integral_const_mul a _
  have hqleft : zeroExteriorForm c kappa mu G (a • u + v) -
      zeroExteriorForm c kappa mu G (a • u - v) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (a • u + v)) z -
          gagliardoIntegrand kappa (zeroExtension G (a • u - v)) z ∂(mu.prod mu)) := by
    show (c / 2) * (∫ z : X × X,
      gagliardoIntegrand kappa (zeroExtension G (a • u + v)) z ∂(mu.prod mu)) -
      (c / 2) * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (a • u - v)) z ∂(mu.prod mu)) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (a • u + v)) z -
          gagliardoIntegrand kappa (zeroExtension G (a • u - v)) z ∂(mu.prod mu))
    rw [MeasureTheory.integral_sub huv hsv]
    ring
  have hqright : zeroExteriorForm c kappa mu G (u + v) -
      zeroExteriorForm c kappa mu G (u - v) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (u + v)) z -
          gagliardoIntegrand kappa (zeroExtension G (u - v)) z ∂(mu.prod mu)) := by
    show (c / 2) * (∫ z : X × X,
      gagliardoIntegrand kappa (zeroExtension G (u + v)) z ∂(mu.prod mu)) -
      (c / 2) * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (u - v)) z ∂(mu.prod mu)) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (u + v)) z -
          gagliardoIntegrand kappa (zeroExtension G (u - v)) z ∂(mu.prod mu))
    rw [MeasureTheory.integral_sub hpuv hpsv]
    ring
  rw [hqleft, hqright, hleft, hright]
  ring

theorem zeroExteriorForm_sub_sub_add_left_of_integrable
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    (G : Set X) (u v w : X → ℝ)
    (huvw : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (u + v + w)) z) (mu.prod mu))
    (huvmw : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (u + v - w)) z) (mu.prod mu))
    (huw : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (u + w)) z) (mu.prod mu))
    (huwm : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (u - w)) z) (mu.prod mu))
    (hvw : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (v + w)) z) (mu.prod mu))
    (hvwm : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G (v - w)) z) (mu.prod mu)) :
    zeroExteriorForm c kappa mu G (u + v + w) -
        zeroExteriorForm c kappa mu G (u + v - w) =
      (zeroExteriorForm c kappa mu G (u + w) -
        zeroExteriorForm c kappa mu G (u - w)) +
        (zeroExteriorForm c kappa mu G (v + w) -
          zeroExteriorForm c kappa mu G (v - w)) := by
  have hpoint : ∀ z : X × X,
      gagliardoIntegrand kappa (zeroExtension G (u + v + w)) z -
          gagliardoIntegrand kappa (zeroExtension G (u + v - w)) z =
        (gagliardoIntegrand kappa (zeroExtension G (u + w)) z -
          gagliardoIntegrand kappa (zeroExtension G (u - w)) z) +
          (gagliardoIntegrand kappa (zeroExtension G (v + w)) z -
            gagliardoIntegrand kappa (zeroExtension G (v - w)) z) := by
    intro z
    simp only [zeroExtension_add, zeroExtension_sub]
    exact gagliardoIntegrand_sub_sub_add_left kappa
      (zeroExtension G u) (zeroExtension G v) (zeroExtension G w) z
  have hleft : ∫ z : X × X,
      gagliardoIntegrand kappa (zeroExtension G (u + v + w)) z -
        gagliardoIntegrand kappa (zeroExtension G (u + v - w)) z ∂(mu.prod mu) =
        ∫ z : X × X,
          (gagliardoIntegrand kappa (zeroExtension G (u + w)) z -
            gagliardoIntegrand kappa (zeroExtension G (u - w)) z) +
            (gagliardoIntegrand kappa (zeroExtension G (v + w)) z -
              gagliardoIntegrand kappa (zeroExtension G (v - w)) z) ∂(mu.prod mu) :=
    MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpoint)
  have hright : ∫ z : X × X,
      (gagliardoIntegrand kappa (zeroExtension G (u + w)) z -
        gagliardoIntegrand kappa (zeroExtension G (u - w)) z) +
        (gagliardoIntegrand kappa (zeroExtension G (v + w)) z -
          gagliardoIntegrand kappa (zeroExtension G (v - w)) z) ∂(mu.prod mu) =
        (∫ z : X × X,
          gagliardoIntegrand kappa (zeroExtension G (u + w)) z -
            gagliardoIntegrand kappa (zeroExtension G (u - w)) z ∂(mu.prod mu)) +
        (∫ z : X × X,
          gagliardoIntegrand kappa (zeroExtension G (v + w)) z -
            gagliardoIntegrand kappa (zeroExtension G (v - w)) z ∂(mu.prod mu)) :=
    MeasureTheory.integral_add (huw.sub huwm) (hvw.sub hvwm)
  have hq : zeroExteriorForm c kappa mu G (u + v + w) -
      zeroExteriorForm c kappa mu G (u + v - w) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (u + v + w)) z -
          gagliardoIntegrand kappa (zeroExtension G (u + v - w)) z ∂(mu.prod mu)) := by
    show (c / 2) * (∫ z : X × X,
      gagliardoIntegrand kappa (zeroExtension G (u + v + w)) z ∂(mu.prod mu)) -
      (c / 2) * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (u + v - w)) z ∂(mu.prod mu)) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (u + v + w)) z -
          gagliardoIntegrand kappa (zeroExtension G (u + v - w)) z ∂(mu.prod mu))
    rw [MeasureTheory.integral_sub huvw huvmw]
    ring
  have hq1 : zeroExteriorForm c kappa mu G (u + w) -
      zeroExteriorForm c kappa mu G (u - w) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (u + w)) z -
          gagliardoIntegrand kappa (zeroExtension G (u - w)) z ∂(mu.prod mu)) := by
    show (c / 2) * (∫ z : X × X,
      gagliardoIntegrand kappa (zeroExtension G (u + w)) z ∂(mu.prod mu)) -
      (c / 2) * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (u - w)) z ∂(mu.prod mu)) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (u + w)) z -
          gagliardoIntegrand kappa (zeroExtension G (u - w)) z ∂(mu.prod mu))
    rw [MeasureTheory.integral_sub huw huwm]
    ring
  have hq2 : zeroExteriorForm c kappa mu G (v + w) -
      zeroExteriorForm c kappa mu G (v - w) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (v + w)) z -
          gagliardoIntegrand kappa (zeroExtension G (v - w)) z ∂(mu.prod mu)) := by
    show (c / 2) * (∫ z : X × X,
      gagliardoIntegrand kappa (zeroExtension G (v + w)) z ∂(mu.prod mu)) -
      (c / 2) * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (v - w)) z ∂(mu.prod mu)) =
      c / 2 * (∫ z : X × X,
        gagliardoIntegrand kappa (zeroExtension G (v + w)) z -
          gagliardoIntegrand kappa (zeroExtension G (v - w)) z ∂(mu.prod mu))
    rw [MeasureTheory.integral_sub hvw hvwm]
    ring
  rw [hq, hq1, hq2, hleft, hright]
  ring

theorem zeroExteriorForm_polar_eq_sub_sub_div_two
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    (G : Set X) (u v : X → ℝ)
    (hu : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa (zeroExtension G u) z) (mu.prod mu))
    (hv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa (zeroExtension G v) z) (mu.prod mu))
    (huv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G u + zeroExtension G v) z) (mu.prod mu))
    (hsv : MeasureTheory.Integrable
      (fun z : X × X => gagliardoIntegrand kappa
        (zeroExtension G u - zeroExtension G v) z) (mu.prod mu)) :
    zeroExteriorForm c kappa mu G (u + v) -
        zeroExteriorForm c kappa mu G u - zeroExteriorForm c kappa mu G v =
      (zeroExteriorForm c kappa mu G (u + v) -
        zeroExteriorForm c kappa mu G (u - v)) / 2 := by
  have h := zeroExteriorForm_add_add_sub_of_integrable c kappa mu G u v
    hu hv huv hsv
  have h2 : 2 * (zeroExteriorForm c kappa mu G (u + v) -
      zeroExteriorForm c kappa mu G u - zeroExteriorForm c kappa mu G v) =
      zeroExteriorForm c kappa mu G (u + v) - zeroExteriorForm c kappa mu G (u - v) := by
    linear_combination h
  field_simp
  rw [mul_comm] at h2
  exact h2

theorem restrictedZeroExteriorForm_polar_add_left
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu))
    (x y z : finiteGagliardoEnergySubmodule kappa mu G hK) :
    QuadraticMap.polar
      (fun u : finiteGagliardoEnergySubmodule kappa mu G hK =>
        zeroExteriorForm c kappa mu G (u : X → ℝ)) (x + y) z =
      QuadraticMap.polar
        (fun u : finiteGagliardoEnergySubmodule kappa mu G hK =>
          zeroExteriorForm c kappa mu G (u : X → ℝ)) x z +
        QuadraticMap.polar
          (fun u : finiteGagliardoEnergySubmodule kappa mu G hK =>
            zeroExteriorForm c kappa mu G (u : X → ℝ)) y z := by
  have hx : finiteGagliardoEnergy kappa mu G (x : X → ℝ) := x.2
  have hy : finiteGagliardoEnergy kappa mu G (y : X → ℝ) := y.2
  have hz : finiteGagliardoEnergy kappa mu G (z : X → ℝ) := z.2
  have hxy : finiteGagliardoEnergy kappa mu G ((x : X → ℝ) + y) :=
    finiteGagliardoEnergy_add kappa mu G hK hx hy
  have hxz : finiteGagliardoEnergy kappa mu G ((x : X → ℝ) + z) :=
    finiteGagliardoEnergy_add kappa mu G hK hx hz
  have hyz : finiteGagliardoEnergy kappa mu G ((y : X → ℝ) + z) :=
    finiteGagliardoEnergy_add kappa mu G hK hy hz
  have hxyz : finiteGagliardoEnergy kappa mu G (((x : X → ℝ) + y) + z) :=
    finiteGagliardoEnergy_add kappa mu G hK hxy hz
  have hxy_z : finiteGagliardoEnergy kappa mu G (((x : X → ℝ) + y) - z) :=
    finiteGagliardoEnergy_sub kappa mu G hK hxy hz
  have hx_z : finiteGagliardoEnergy kappa mu G ((x : X → ℝ) - z) :=
    finiteGagliardoEnergy_sub kappa mu G hK hx hz
  have hy_z : finiteGagliardoEnergy kappa mu G ((y : X → ℝ) - z) :=
    finiteGagliardoEnergy_sub kappa mu G hK hy hz
  have hp1 := zeroExteriorForm_polar_eq_sub_sub_div_two c kappa mu G
    ((x : X → ℝ) + y) z hxy.2 hz.2
    (by simpa only [zeroExtension_add] using hxyz.2)
    (by simpa only [zeroExtension_sub] using hxy_z.2)
  have hp2 := zeroExteriorForm_polar_eq_sub_sub_div_two c kappa mu G
    (x : X → ℝ) z hx.2 hz.2
    (by simpa only [zeroExtension_add] using hxz.2)
    (by simpa only [zeroExtension_sub] using hx_z.2)
  have hp3 := zeroExteriorForm_polar_eq_sub_sub_div_two c kappa mu G
    (y : X → ℝ) z hy.2 hz.2
    (by simpa only [zeroExtension_add] using hyz.2)
    (by simpa only [zeroExtension_sub] using hy_z.2)
  have hd := zeroExteriorForm_sub_sub_add_left_of_integrable c kappa mu G
    (x : X → ℝ) y z hxyz.2 hxy_z.2 hxz.2 hx_z.2 hyz.2 hy_z.2
  simp only [QuadraticMap.polar, Submodule.coe_add]
  rw [hp1, hp2, hp3, hd]
  ring

theorem restrictedZeroExteriorForm_polar_smul_left
    [MeasurableSpace X] (c kappa a : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu))
    (x y : finiteGagliardoEnergySubmodule kappa mu G hK) :
    QuadraticMap.polar
      (fun u : finiteGagliardoEnergySubmodule kappa mu G hK =>
        zeroExteriorForm c kappa mu G (u : X → ℝ)) (a • x) y =
      a • QuadraticMap.polar
        (fun u : finiteGagliardoEnergySubmodule kappa mu G hK =>
          zeroExteriorForm c kappa mu G (u : X → ℝ)) x y := by
  have hx : finiteGagliardoEnergy kappa mu G (x : X → ℝ) := x.2
  have hy : finiteGagliardoEnergy kappa mu G (y : X → ℝ) := y.2
  have hax : finiteGagliardoEnergy kappa mu G (a • (x : X → ℝ)) :=
    finiteGagliardoEnergy_smul kappa a mu G hx
  have hay : finiteGagliardoEnergy kappa mu G ((a • (x : X → ℝ)) + y) :=
    finiteGagliardoEnergy_add kappa mu G hK hax hy
  have hamy : finiteGagliardoEnergy kappa mu G ((a • (x : X → ℝ)) - y) :=
    finiteGagliardoEnergy_sub kappa mu G hK hax hy
  have hxy : finiteGagliardoEnergy kappa mu G ((x : X → ℝ) + y) :=
    finiteGagliardoEnergy_add kappa mu G hK hx hy
  have hxmy : finiteGagliardoEnergy kappa mu G ((x : X → ℝ) - y) :=
    finiteGagliardoEnergy_sub kappa mu G hK hx hy
  have hp1 := zeroExteriorForm_polar_eq_sub_sub_div_two c kappa mu G
    (a • (x : X → ℝ)) y hax.2 hy.2
    (by simpa only [zeroExtension_add] using hay.2)
    (by simpa only [zeroExtension_sub] using hamy.2)
  have hp2 := zeroExteriorForm_polar_eq_sub_sub_div_two c kappa mu G
    (x : X → ℝ) y hx.2 hy.2
    (by simpa only [zeroExtension_add] using hxy.2)
    (by simpa only [zeroExtension_sub] using hxmy.2)
  have hd := zeroExteriorForm_sub_sub_smul_left_of_integrable c kappa a mu G
    (x : X → ℝ) y hay.2 hamy.2 hxy.2 hxmy.2
  simp only [QuadraticMap.polar, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  rw [hp1, hp2, hd]
  ring

/-- The zero-exterior quadratic form restricted to the finite-energy domain. -/
noncomputable def restrictedZeroExteriorForm
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu)) :
    QuadraticMap ℝ (finiteGagliardoEnergySubmodule kappa mu G hK) ℝ :=
  QuadraticMap.ofPolar
    (fun u : finiteGagliardoEnergySubmodule kappa mu G hK =>
      zeroExteriorForm c kappa mu G (u : X → ℝ))
    (by
      intro a u
      rw [Submodule.coe_smul, zeroExteriorForm_smul, smul_eq_mul]
      ring)
    (restrictedZeroExteriorForm_polar_add_left c kappa mu G hK)
    (fun a => restrictedZeroExteriorForm_polar_smul_left c kappa a mu G hK)

theorem restrictedZeroExteriorForm_ker_toLp_le_radical
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu)) :
    LinearMap.ker (finiteGagliardoEnergy_toLpLinear kappa mu G hK) ≤
      (restrictedZeroExteriorForm c kappa mu G hK).radical := by
  intro x hx
  have hfx : finiteGagliardoEnergy.toLp kappa mu G x.1 x.2 = 0 := by
    simpa [finiteGagliardoEnergy_toLpLinear] using
      (LinearMap.mem_ker.mp hx)
  have hcoe : ⇑(finiteGagliardoEnergy.toLp kappa mu G x.1 x.2) =ᵐ[mu] 0 := by
    exact MeasureTheory.Lp.eq_zero_iff_ae_eq_zero.mp hfx
  have hzero : zeroExtension G x.1 =ᵐ[mu] 0 :=
    (finiteGagliardoEnergy.coeFn_toLp kappa mu G x.1 x.2).symm.trans hcoe
  have hQ : restrictedZeroExteriorForm c kappa mu G hK x = 0 := by
    show zeroExteriorForm c kappa mu G x.1 = 0
    have hcompare : zeroExtension G x.1 =ᵐ[mu] zeroExtension G 0 := by
      rw [zeroExtension_zero]
      exact hzero
    rw [zeroExteriorForm_congr_zeroExtension_ae c kappa mu G hcompare,
      zeroExteriorForm_zero]
  refine (QuadraticMap.mem_radical_iff').mpr ⟨hQ, ?_⟩
  intro n
  show zeroExteriorForm c kappa mu G ((x + n : finiteGagliardoEnergySubmodule _ _ _ _) : X → ℝ) =
    zeroExteriorForm c kappa mu G (n : X → ℝ)
  rw [Submodule.coe_add]
  exact zeroExteriorForm_add_congr_left_zero c kappa mu G hzero

open Classical in
noncomputable def restrictedZeroExteriorFormLift
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu)) :
    QuadraticMap ℝ (MeasureTheory.Lp ℝ 2 mu) ℝ := by
  let f := finiteGagliardoEnergy_toLpLinear kappa mu G hK
  let Q := restrictedZeroExteriorForm c kappa mu G hK
  let hker : LinearMap.ker f ≤ Q.radical :=
    restrictedZeroExteriorForm_ker_toLp_le_radical c kappa mu G hK
  let Qbar := Q.lift (LinearMap.ker f) hker
  let hcomp := Classical.choose
    (Submodule.exists_isCompl (LinearMap.range f))
  let hcompl := Classical.choose_spec
    (Submodule.exists_isCompl (LinearMap.range f))
  let p := (LinearMap.range f).projectionOnto hcomp hcompl
  exact Qbar.comp ((f.quotKerEquivRange.symm.toLinearMap).comp p)

theorem restrictedZeroExteriorFormLift_apply_toLp
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu))
    (u : finiteGagliardoEnergySubmodule kappa mu G hK) :
    restrictedZeroExteriorFormLift c kappa mu G hK
        (finiteGagliardoEnergy_toLpLinear kappa mu G hK u) =
      restrictedZeroExteriorForm c kappa mu G hK u := by
  set f := finiteGagliardoEnergy_toLpLinear kappa mu G hK
  set Q := restrictedZeroExteriorForm c kappa mu G hK
  set hker := restrictedZeroExteriorForm_ker_toLp_le_radical c kappa mu G hK
  set Qbar := Q.lift (LinearMap.ker f) hker
  set hcomp := Classical.choose
    (Submodule.exists_isCompl (LinearMap.range f))
  set hcompl := Classical.choose_spec
    (Submodule.exists_isCompl (LinearMap.range f))
  set p := (LinearMap.range f).projectionOnto hcomp hcompl
  have hmem : f u ∈ LinearMap.range f := LinearMap.mem_range_self f u
  have hp : p (f u) = ⟨f u, hmem⟩ :=
    Submodule.projectionOnto_apply_of_mem_left hcompl hmem
  have hq : f.quotKerEquivRange.symm ⟨f u, hmem⟩ =
      (LinearMap.ker f).mkQ u :=
    LinearMap.quotKerEquivRange_symm_apply_image f u hmem
  change Qbar (f.quotKerEquivRange.symm (p (f u))) = Q u
  rw [hp, hq]
  exact QuadraticMap.lift_mk hker u

/-- The lifted form has the same polar form as the restricted zero-exterior
form on finite-energy representatives.  This is the compatibility bridge used
when passing first-variation identities from the form domain to `L²`. -/
theorem restrictedZeroExteriorFormLift_polar_apply_toLp
    [MeasurableSpace X] (c kappa : ℝ) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu))
    (u v : finiteGagliardoEnergySubmodule kappa mu G hK) :
    QuadraticMap.polar
      (⇑(restrictedZeroExteriorFormLift c kappa mu G hK))
      (finiteGagliardoEnergy_toLpLinear kappa mu G hK u)
      (finiteGagliardoEnergy_toLpLinear kappa mu G hK v) =
    QuadraticMap.polar
      (⇑(restrictedZeroExteriorForm c kappa mu G hK)) u v := by
  have hadd :
      finiteGagliardoEnergy_toLpLinear kappa mu G hK u +
        finiteGagliardoEnergy_toLpLinear kappa mu G hK v =
      finiteGagliardoEnergy_toLpLinear kappa mu G hK (u + v) :=
    (map_add (finiteGagliardoEnergy_toLpLinear kappa mu G hK) u v).symm
  simp only [QuadraticMap.polar]
  rw [hadd,
    restrictedZeroExteriorFormLift_apply_toLp c kappa mu G hK (u + v),
    restrictedZeroExteriorFormLift_apply_toLp c kappa mu G hK u,
    restrictedZeroExteriorFormLift_apply_toLp c kappa mu G hK v]

/-- The lifted zero-exterior Gagliardo form is nonnegative whenever the
singular-integral normalization is nonnegative. -/
theorem restrictedZeroExteriorFormLift_nonneg
    [MeasurableSpace X] (c kappa : ℝ) (hc : 0 ≤ c) (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu] (G : Set X)
    (hK : MeasureTheory.AEStronglyMeasurable
      (fun z : X × X => gagliardoKernel kappa z.1 z.2) (mu.prod mu))
    (x : MeasureTheory.Lp ℝ 2 mu) :
    0 ≤ restrictedZeroExteriorFormLift c kappa mu G hK x := by
  set f := finiteGagliardoEnergy_toLpLinear kappa mu G hK
  set Q := restrictedZeroExteriorForm c kappa mu G hK
  set hker := restrictedZeroExteriorForm_ker_toLp_le_radical c kappa mu G hK
  set Qbar := Q.lift (LinearMap.ker f) hker
  set hcomp := Classical.choose
    (Submodule.exists_isCompl (LinearMap.range f))
  set hcompl := Classical.choose_spec
    (Submodule.exists_isCompl (LinearMap.range f))
  set p := (LinearMap.range f).projectionOnto hcomp hcompl
  change 0 ≤ Qbar (f.quotKerEquivRange.symm (p x))
  obtain ⟨u, hu⟩ := Quotient.exists_rep
    (f.quotKerEquivRange.symm (p x))
  rw [← hu]
  change 0 ≤ Qbar (Submodule.Quotient.mk u)
  rw [QuadraticMap.lift_mk]
  show 0 ≤ zeroExteriorForm c kappa mu G (u : X → ℝ)
  exact zeroExteriorForm_nonneg hc mu G (u : X → ℝ)

end Tunneling
