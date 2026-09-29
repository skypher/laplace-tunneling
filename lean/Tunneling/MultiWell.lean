import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Filter.Tendsto
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Tunneling.FractionalForm
import Tunneling.Statements

namespace Tunneling

/-! The finite-dimensional effective interaction matrix from the multi-well
section.  The analytic block operator and its compression remain separate; this
module records the exact real symmetric matrix used by the theorem. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : Type*} [NormedAddCommGroup X]

/-- The effective interaction matrix with zero diagonal and off-diagonal
entries `-c m^2 |a_i-a_j|^(-kappa)`. -/
noncomputable def effectiveInteractionMatrix
    (a : ι → X) (c m kappa : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    if i = j then 0
    else -c * m ^ 2 * ‖a i - a j‖ ^ (-kappa)

@[simp] theorem effectiveInteractionMatrix_apply
    (a : ι → X) (c m kappa : ℝ) (i j : ι) :
    effectiveInteractionMatrix a c m kappa i j =
      if i = j then 0
      else -c * m ^ 2 * ‖a i - a j‖ ^ (-kappa) := by
  rfl

theorem effectiveInteractionMatrix_diag
    (a : ι → X) (c m kappa : ℝ) (i : ι) :
    effectiveInteractionMatrix a c m kappa i i = 0 := by
  simp [effectiveInteractionMatrix]

theorem effectiveInteractionMatrix_nonzero
    (a : ι → X) (c m kappa : ℝ) (i j : ι)
    (hij : i ≠ j) (hpos : a i ≠ a j) (hc : c ≠ 0) (hm : m ≠ 0) :
    effectiveInteractionMatrix a c m kappa ≠ 0 := by
  intro hzero
  have hentry : effectiveInteractionMatrix a c m kappa i j = 0 := by
    rw [hzero]
    simp
  have happ := effectiveInteractionMatrix_apply a c m kappa i j
  rw [if_neg hij] at happ
  have hnorm : 0 < ‖a i - a j‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hpos)
  have hpow : 0 < ‖a i - a j‖ ^ (-kappa) :=
    Real.rpow_pos_of_pos hnorm _
  have hprod : -c * m ^ 2 * ‖a i - a j‖ ^ (-kappa) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact neg_ne_zero.mpr hc
      · exact pow_ne_zero 2 hm
    · exact ne_of_gt hpow
  exact hprod (happ.symm.trans hentry)

theorem effectiveInteractionMatrix_isSymm
    (a : ι → X) (c m kappa : ℝ) :
    (effectiveInteractionMatrix a c m kappa).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [effectiveInteractionMatrix]
  · have hji : j ≠ i := Ne.symm hij
    rw [effectiveInteractionMatrix_apply, effectiveInteractionMatrix_apply,
      if_neg hji, if_neg hij, norm_sub_rev]

theorem effectiveInteractionMatrix_isHermitian
    (a : ι → X) (c m kappa : ℝ) :
    (effectiveInteractionMatrix a c m kappa).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact effectiveInteractionMatrix_isSymm a c m kappa

theorem effectiveInteractionMatrix_trace_eq_zero
    (a : ι → X) (c m kappa : ℝ) :
    Matrix.trace (effectiveInteractionMatrix a c m kappa) = 0 := by
  unfold Matrix.trace
  apply Finset.sum_eq_zero
  intro i _
  exact effectiveInteractionMatrix_diag a c m kappa i

/-! The finite-well cross kernel in equation `eq:exact-compression`.  Unlike
the two-well reflected kernel, the distance between translated copies is
`center + x - y`. -/
noncomputable def multiWellCrossKernel
    (kappa : ℝ) (center x y : X) : ℝ :=
  ‖center + x - y‖ ^ (-kappa)

theorem multiWellCrossKernel_neg_center_swap
    (kappa : ℝ) (center x y : X) :
    multiWellCrossKernel kappa center x y =
      multiWellCrossKernel kappa (-center) y x := by
  show ‖center + x - y‖ ^ (-kappa) =
    ‖(-center) + y - x‖ ^ (-kappa)
  have h : center + x - y = -((-center) + y - x) := by abel
  rw [h, norm_neg]

theorem kernelCrossPairing_multiWell_swap
    [MeasurableSpace X] {mu : MeasureTheory.Measure X}
    [MeasureTheory.SFinite mu]
    (kappa : ℝ) (center : X) (u : X → ℝ) :
    kernelCrossPairing (multiWellCrossKernel kappa center) mu u u =
      kernelCrossPairing (multiWellCrossKernel kappa (-center)) mu u u := by
  have hpoint : ∀ z : X × X,
      u z.2 * u z.1 * multiWellCrossKernel kappa center z.2 z.1 =
        u z.1 * u z.2 * multiWellCrossKernel kappa (-center) z.1 z.2 := by
    intro z
    rcases z with ⟨x, y⟩
    rw [multiWellCrossKernel_neg_center_swap kappa center y x]
    ring
  have hswap :
      (∫ z : X × X,
          u z.1 * u z.2 * multiWellCrossKernel kappa center z.1 z.2
            ∂(mu.prod mu)) =
        ∫ z : X × X,
          u z.2 * u z.1 * multiWellCrossKernel kappa center z.2 z.1
            ∂(mu.prod mu) :=
    MeasureTheory.integral_prod_swap
      (fun z : X × X =>
        u z.2 * u z.1 * multiWellCrossKernel kappa center z.2 z.1)
  simp only [kernelCrossPairing]
  calc
    (∫ z : X × X,
        u z.1 * u z.2 * multiWellCrossKernel kappa center z.1 z.2
          ∂(mu.prod mu)) =
        ∫ z : X × X,
          u z.2 * u z.1 * multiWellCrossKernel kappa center z.2 z.1
            ∂(mu.prod mu) := hswap
    _ = ∫ z : X × X,
        u z.1 * u z.2 * multiWellCrossKernel kappa (-center) z.1 z.2
          ∂(mu.prod mu) := by
      apply MeasureTheory.integral_congr_ae
      exact MeasureTheory.ae_of_all _ hpoint

/-! The exact compression matrix `T_L=(t_ij(L))` from equation
`eq:exact-compression`, written through the ground-state kernel pairing. -/
noncomputable def multiWellCompressionMatrix
    [MeasurableSpace X] [Module ℝ X]
    (mu : MeasureTheory.Measure X)
    (kappa c : ℝ) (u : X → ℝ) (a : ι → X) (L : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    if i = j then 0
    else -c * kernelCrossPairing
      (multiWellCrossKernel kappa ((L : ℝ) • (a i - a j))) mu u u

@[simp] theorem multiWellCompressionMatrix_apply
    [MeasurableSpace X] [Module ℝ X]
    (mu : MeasureTheory.Measure X)
    (kappa c : ℝ) (u : X → ℝ) (a : ι → X) (L : ℝ) (i j : ι) :
    multiWellCompressionMatrix mu kappa c u a L i j =
      if i = j then 0
      else -c * kernelCrossPairing
        (multiWellCrossKernel kappa ((L : ℝ) • (a i - a j))) mu u u := by
  rfl

theorem multiWellCompressionMatrix_diag
    [MeasurableSpace X] [Module ℝ X]
    (mu : MeasureTheory.Measure X)
    (kappa c : ℝ) (u : X → ℝ) (a : ι → X) (L : ℝ) (i : ι) :
    multiWellCompressionMatrix mu kappa c u a L i i = 0 := by
  simp [multiWellCompressionMatrix]

theorem multiWellCompressionMatrix_isSymm
    [MeasurableSpace X] [Module ℝ X]
    (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu]
    (kappa c : ℝ) (u : X → ℝ) (a : ι → X) (L : ℝ) :
    (multiWellCompressionMatrix mu kappa c u a L).IsSymm := by
  classical
  refine Matrix.IsSymm.ext ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [multiWellCompressionMatrix]
  · have hji : j ≠ i := Ne.symm hij
    rw [multiWellCompressionMatrix_apply, multiWellCompressionMatrix_apply,
      if_neg hij, if_neg hji]
    have hcenter : (L : ℝ) • (a j - a i) =
        -((L : ℝ) • (a i - a j)) := by
      rw [show a j - a i = -(a i - a j) by abel, smul_neg]
    rw [hcenter]
    exact congrArg (fun z : ℝ => -c * z)
      (kernelCrossPairing_multiWell_swap kappa
        ((L : ℝ) • (a i - a j)) u).symm

theorem multiWellCompressionMatrix_isHermitian
    [MeasurableSpace X] [Module ℝ X]
    (mu : MeasureTheory.Measure X)
    [MeasureTheory.SFinite mu]
    (kappa c : ℝ) (u : X → ℝ) (a : ι → X) (L : ℝ) :
    (multiWellCompressionMatrix mu kappa c u a L).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact multiWellCompressionMatrix_isSymm mu kappa c u a L

/-! The second-order remainder for the finite-well kernel.  The linear term
is `inner center (x-y)`, so its product integral vanishes by symmetry. -/
noncomputable def multiWellTaylorRemainder
    [InnerProductSpace ℝ X] (kappa : ℝ) (center x y : X) : ℝ :=
  multiWellCrossKernel kappa center x y - ‖center‖ ^ (-kappa) +
    kappa * ‖center‖ ^ (-kappa - 2) * inner ℝ center (x - y)

theorem multiWellCrossKernel_taylor_decomp
    [InnerProductSpace ℝ X] (kappa : ℝ) (center x y : X) :
    multiWellCrossKernel kappa center x y =
      ‖center‖ ^ (-kappa) +
        (-kappa * ‖center‖ ^ (-kappa - 2)) * inner ℝ center (x - y) +
        multiWellTaylorRemainder kappa center x y := by
  simp only [multiWellTaylorRemainder]
  ring

/-- The finite-well Taylor bound from equation `eq:multi-taylor`.  Along the
segment from `0` to `x-y`, the translated center is at distance at least
`L*‖d‖/2`; the second derivative estimate and the factor `1/2` in Taylor's
theorem give the displayed constant `C_{kappa,R}`. -/
theorem multiWellTaylorRemainder_abs_le
    [InnerProductSpace ℝ X] (A : TwoWellConstants)
    (d x y : X) (L : ℝ)
    (hL : 0 < L) (hsep : 4 * A.R ≤ L * ‖d‖)
    (hx : ‖x‖ ≤ A.R) (hy : ‖y‖ ≤ A.R) :
    |multiWellTaylorRemainder A.kappa ((L : ℝ) • d) x y| ≤
      A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) := by
  set center : X := (L : ℝ) • d
  have hk : 0 ≤ A.kappa := A.kappa_pos.le
  have hR : 0 ≤ A.R := A.hR.le
  have hdpos : 0 < ‖d‖ := by
    have h4R : (0:ℝ) < 4 * A.R := mul_pos (by norm_num) A.hR
    have hprod : (0:ℝ) < L * ‖d‖ := lt_of_lt_of_le h4R hsep
    exact pos_of_mul_pos_left (by simpa [mul_comm] using hprod) hL.le
  have hcenterpos : 0 < ‖center‖ := by
    show 0 < ‖(L : ℝ) • d‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    exact mul_pos hL hdpos
  have hcenter : center ≠ 0 := norm_ne_zero_iff.mp hcenterpos.ne'
  set g : ℝ → ℝ := translatedCrossLine A.kappa center (-x) y
  have hxy : ‖x - y‖ ≤ 2 * A.R := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ A.R + A.R := add_le_add hx hy
      _ = 2 * A.R := by ring
  have hxy2 : ‖x - y‖ ^ 2 ≤ (2 * A.R) ^ 2 := by
    refine sq_le_sq.mpr ?_
    rw [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (mul_nonneg (by norm_num) hR)]
    exact hxy
  have hvec : (-x) + y = -(x - y) := by abel
  have hlineNorm : ‖(-x) + y‖ = ‖x - y‖ := by
    rw [hvec, norm_neg]
  have hlineNonzero : ∀ t ∈ Set.Icc (0:ℝ) 1,
      center - (t:ℝ) • ((-x) + y) ≠ 0 := by
    intro t ht
    have htnonneg : 0 ≤ (t:ℝ) := ht.1
    have htle : (t:ℝ) ≤ 1 := ht.2
    have hterm : ‖(t:ℝ) • ((-x) + y)‖ ≤ 2 * A.R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htnonneg,
        hlineNorm]
      calc
        (t:ℝ) * ‖x - y‖ ≤ 1 * (2 * A.R) :=
          mul_le_mul htle hxy (norm_nonneg _) zero_le_one
        _ = 2 * A.R := by ring
    have htri : ‖center‖ ≤
        ‖center - (t:ℝ) • ((-x) + y)‖ +
          ‖(t:ℝ) • ((-x) + y)‖ := by
      calc
        ‖center‖ = ‖center - (t:ℝ) • ((-x) + y) +
            (t:ℝ) • ((-x) + y)‖ := by rw [sub_add_cancel]
        _ ≤ ‖center - (t:ℝ) • ((-x) + y)‖ +
            ‖(t:ℝ) • ((-x) + y)‖ := norm_add_le _ _
    have hcenterEq : ‖center‖ = L * ‖d‖ := by
      show ‖(L : ℝ) • d‖ = L * ‖d‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    have hlower : (L * ‖d‖) / 2 ≤
        ‖center - (t:ℝ) • ((-x) + y)‖ := by
      have hstep : (L * ‖d‖) / 2 ≤ L * ‖d‖ - 2 * A.R := by
        linarith
      have hnorm : L * ‖d‖ - ‖(t:ℝ) • ((-x) + y)‖ ≤
          ‖center - (t:ℝ) • ((-x) + y)‖ := by
        linarith [hcenterEq]
      linarith
    intro hzero
    have hnorm : ‖center - (t:ℝ) • ((-x) + y)‖ = 0 := by
      rw [hzero, norm_zero]
    have hpos : (0:ℝ) < L * ‖d‖ / 2 := by positivity
    linarith
  have hcontDiff : ContDiffOn ℝ 2 g (Set.Icc (0:ℝ) 1) :=
    translatedCrossLine_contDiffOn A.kappa center (-x) y hlineNonzero
  have hg0 : g 0 = ‖center‖ ^ (-A.kappa) :=
    translatedCrossLine_zero A.kappa center (-x) y
  have hg1 : g 1 = multiWellCrossKernel A.kappa center x y := by
    show translatedCrossLine A.kappa center (-x) y 1 =
      multiWellCrossKernel A.kappa center x y
    rw [translatedCrossLine_one]
    show translatedCrossKernel A.kappa center (-x) y =
      multiWellCrossKernel A.kappa center x y
    simp only [translatedCrossKernel, multiWellCrossKernel]
    rw [show center - (-x) - y = center + x - y by abel]
  have hderiv : derivWithin g (Set.Icc (0:ℝ) 1) 0 =
      -A.kappa * ‖center‖ ^ (-A.kappa - 2) *
        inner ℝ center (x - y) := by
    have hhas := translatedCrossLine_hasDerivAt_zero A.kappa center (-x) y hcenter
    have hunique : UniqueDiffWithinAt ℝ (Set.Icc (0:ℝ) 1) 0 :=
      (uniqueDiffOn_Icc (show (0:ℝ) < 1 by norm_num)).uniqueDiffWithinAt
        (by simp)
    refine (hhas.hasDerivWithinAt.derivWithin hunique).trans ?_
    rw [hvec, inner_neg_right]
    ring
  have hexp : -A.kappa - 2 ≤ (0:ℝ) := by linarith
  have hscale : ((L * ‖d‖) / 2) ^ (-A.kappa - 2) =
      (2:ℝ) ^ (A.kappa + 2) *
        L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) := by
    have hpowHalf : ((L * ‖d‖) / 2) ^ (-A.kappa - 2) =
        (2:ℝ) ^ (A.kappa + 2) * (L * ‖d‖) ^ (-A.kappa - 2) := by
      calc
        ((L * ‖d‖) / 2) ^ (-A.kappa - 2) =
            (((L * ‖d‖) / 2)⁻¹) ^ (A.kappa + 2) := by
          rw [show (-A.kappa - 2 : ℝ) = -(A.kappa + 2) by ring,
            Real.rpow_neg_eq_inv_rpow]
        _ = (2 / (L * ‖d‖)) ^ (A.kappa + 2) := by rw [inv_div]
        _ = (2:ℝ) ^ (A.kappa + 2) / (L * ‖d‖) ^ (A.kappa + 2) :=
          Real.div_rpow (by norm_num) (mul_nonneg hL.le hdpos.le) _
        _ = (2:ℝ) ^ (A.kappa + 2) *
            (L * ‖d‖) ^ (-A.kappa - 2) := by
          rw [div_eq_mul_inv,
            show (-A.kappa - 2 : ℝ) = -(A.kappa + 2) by ring,
            Real.rpow_neg (mul_nonneg hL.le hdpos.le)]
    rw [hpowHalf, Real.mul_rpow hL.le hdpos.le]
    ring
  have hsecond : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      |iteratedDerivWithin 2 g (Set.Icc (0:ℝ) 1) t| ≤
        2 * A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) := by
    intro t ht
    have hne : center - (t:ℝ) • ((-x) + y) ≠ 0 :=
      hlineNonzero t (Set.mem_Icc_of_Ioo ht)
    have hcontAt := hcontDiff.contDiffAt (Icc_mem_nhds ht.1 ht.2)
    have hiter : iteratedDerivWithin 2 g (Set.Icc (0:ℝ) 1) t =
        deriv (deriv g) t := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (show (0:ℝ) < 1 by norm_num))
        hcontAt (Set.mem_Icc_of_Ioo ht),
        iteratedDeriv_succ, iteratedDeriv_one]
    have hnorm : (L * ‖d‖) / 2 ≤
        ‖center - (t:ℝ) • ((-x) + y)‖ := by
      rcases hlineNonzero t (Set.mem_Icc_of_Ioo ht) with _
      have hterm : ‖(t:ℝ) • ((-x) + y)‖ ≤ 2 * A.R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le,
          hlineNorm]
        calc
          (t:ℝ) * ‖x - y‖ ≤ 1 * (2 * A.R) :=
            mul_le_mul ht.2.le hxy (norm_nonneg _) zero_le_one
          _ = 2 * A.R := by ring
      have htri : ‖center‖ ≤
          ‖center - (t:ℝ) • ((-x) + y)‖ +
            ‖(t:ℝ) • ((-x) + y)‖ := by
        calc
          ‖center‖ = ‖center - (t:ℝ) • ((-x) + y) +
              (t:ℝ) • ((-x) + y)‖ := by rw [sub_add_cancel]
          _ ≤ ‖center - (t:ℝ) • ((-x) + y)‖ +
              ‖(t:ℝ) • ((-x) + y)‖ := norm_add_le _ _
      have hcenterEq : ‖center‖ = L * ‖d‖ := by
        show ‖(L : ℝ) • d‖ = L * ‖d‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
      have hstep : (L * ‖d‖) / 2 ≤ L * ‖d‖ - 2 * A.R := by
        linarith
      have hrev : L * ‖d‖ - ‖(t:ℝ) • ((-x) + y)‖ ≤
          ‖center - (t:ℝ) • ((-x) + y)‖ := by
        linarith [hcenterEq]
      linarith
    have hpow : ‖center - (t:ℝ) • ((-x) + y)‖ ^ (-A.kappa - 2) ≤
        ((L * ‖d‖) / 2) ^ (-A.kappa - 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hnorm hexp
    have hbase : 0 ≤
        A.kappa * (A.kappa + 1) *
          ((L * ‖d‖) / 2) ^ (-A.kappa - 2) * (2 * A.R) ^ 2 := by
      positivity
    have hproduct :
        A.kappa * (A.kappa + 1) *
            ‖center - (t:ℝ) • ((-x) + y)‖ ^ (-A.kappa - 2) *
            ‖(-x) + y‖ ^ 2 ≤
          A.kappa * (A.kappa + 1) *
            ((L * ‖d‖) / 2) ^ (-A.kappa - 2) * (2 * A.R) ^ 2 := by
      have hfirst : A.kappa * (A.kappa + 1) *
          ‖center - (t:ℝ) • ((-x) + y)‖ ^ (-A.kappa - 2) *
          ‖(-x) + y‖ ^ 2 ≤
        A.kappa * (A.kappa + 1) *
          ((L * ‖d‖) / 2) ^ (-A.kappa - 2) *
          ‖(-x) + y‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity))
          (sq_nonneg _)
      rw [hlineNorm] at hfirst
      calc
        A.kappa * (A.kappa + 1) *
            ‖center - (t:ℝ) • ((-x) + y)‖ ^ (-A.kappa - 2) *
            ‖(-x) + y‖ ^ 2 =
          A.kappa * (A.kappa + 1) *
            ‖center - (t:ℝ) • ((-x) + y)‖ ^ (-A.kappa - 2) *
            ‖x - y‖ ^ 2 := by rw [hlineNorm]
        _ ≤ A.kappa * (A.kappa + 1) *
            ((L * ‖d‖) / 2) ^ (-A.kappa - 2) * ‖x - y‖ ^ 2 := hfirst
        _ ≤ A.kappa * (A.kappa + 1) *
            ((L * ‖d‖) / 2) ^ (-A.kappa - 2) * (2 * A.R) ^ 2 :=
          mul_le_mul_of_nonneg_left hxy2 (by positivity)
    rw [hiter]
    refine (translatedCrossLine_second_deriv_abs_le A.kappa hk center (-x) y t hne).trans ?_
    refine hproduct.trans ?_
    show A.kappa * (A.kappa + 1) *
        ((L * ‖d‖) / 2) ^ (-A.kappa - 2) * (2 * A.R) ^ 2 ≤
      2 * A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2)
    rw [hscale]
    show A.kappa * (A.kappa + 1) *
        ((2:ℝ) ^ (A.kappa + 2) * L ^ (-A.kappa - 2) *
          ‖d‖ ^ (-A.kappa - 2)) * (2 * A.R) ^ 2 ≤
      2 * A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2)
    have hconst :
        A.kappa * (A.kappa + 1) *
          ((2:ℝ) ^ (A.kappa + 2) * L ^ (-A.kappa - 2) *
            ‖d‖ ^ (-A.kappa - 2)) * (2 * A.R) ^ 2 =
        2 * A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) := by
      show A.kappa * (A.kappa + 1) *
          ((2:ℝ) ^ (A.kappa + 2) * L ^ (-A.kappa - 2) *
            ‖d‖ ^ (-A.kappa - 2)) * (2 * A.R) ^ 2 =
        2 * ((2:ℝ) ^ (A.kappa + 3) * A.kappa *
          (A.kappa + 1) * A.R ^ 2) *
          L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2)
      rw [show (2:ℝ) ^ (A.kappa + 3) =
          (2:ℝ) ^ (A.kappa + 2) * 2 by
        rw [show (A.kappa + 3 : ℝ) = (A.kappa + 2) + 1 by ring,
          Real.rpow_add_one (by norm_num)]]
      ring
    exact hconst.le
  have hC : 0 ≤
      2 * A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) := by
    have hA : 0 ≤ A.C := A.hC.le
    positivity
  have hsc := scalar_taylor_remainder_bound g 0 1
    (2 * A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2))
    (by norm_num) (by norm_num) hC hcontDiff hsecond
  rw [hg0, hg1, hderiv] at hsc
  simp only [sub_zero, one_mul, one_pow, mul_one] at hsc
  have hcalc :
      (2 * A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2)) / 2 =
        A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) := by
    ring
  rw [hcalc] at hsc
  simpa [multiWellTaylorRemainder] using hsc

theorem kernelCrossPairing_multiWell_taylor
    [MeasurableSpace X] [InnerProductSpace ℝ X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    (kappa : ℝ) (center : X) (u : X → ℝ) (m r : ℝ)
    (hprodInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2) (mu.prod mu))
    (hlinInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2 * inner ℝ center (z.1 - z.2))
        (mu.prod mu))
    (hRInt : MeasureTheory.Integrable
      (fun z : X × X =>
        u z.1 * u z.2 * multiWellTaylorRemainder kappa center z.1 z.2)
        (mu.prod mu))
    (hmass : ∫ x, u x ∂mu = m)
    (hnonneg : ∀ x, 0 ≤ u x)
    (hr : 0 ≤ r)
    (hRbound : ∀ x y,
      |multiWellTaylorRemainder kappa center x y| ≤ r) :
    |kernelCrossPairing (multiWellCrossKernel kappa center) mu u u -
      m * m * ‖center‖ ^ (-kappa)| ≤ r * m * m := by
  refine interactionMass_taylor_remainder_prod mu u
    (multiWellCrossKernel kappa center)
    (fun z : X × X => inner ℝ center (z.1 - z.2))
    (fun z : X × X => multiWellTaylorRemainder kappa center z.1 z.2)
    m (‖center‖ ^ (-kappa))
    (-kappa * ‖center‖ ^ (-kappa - 2)) r
    hprodInt hlinInt hRInt hmass
    (linear_sub_integral_zero mu center u)
    hnonneg hr ?_ hRbound
  intro x y
  exact multiWellCrossKernel_taylor_decomp kappa center x y

/-- The off-diagonal entry estimate in equation `eq:compression-error`.  The
linear Taylor term cancels in the kernel pairing, while the pointwise remainder
is bounded by `multiWellTaylorRemainder_abs_le`. -/
theorem multiWellCompressionMatrix_entry_taylor
    [MeasurableSpace X] [InnerProductSpace ℝ X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    (A : TwoWellConstants) (a : ι → X) (u : X → ℝ)
    (L : ℝ) (i j : ι)
    (hL : 0 < L) (hij : i ≠ j)
    (hsep : 4 * A.R ≤ L * ‖a i - a j‖)
    (hX : ∀ x : X, ‖x‖ ≤ A.R)
    (hprodInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2) (mu.prod mu))
    (hlinInt : MeasureTheory.Integrable
      (fun z : X × X =>
        u z.1 * u z.2 * inner ℝ ((L : ℝ) • (a i - a j)) (z.1 - z.2))
        (mu.prod mu))
    (hRInt : MeasureTheory.Integrable
      (fun z : X × X =>
        u z.1 * u z.2 *
          multiWellTaylorRemainder A.kappa
            ((L : ℝ) • (a i - a j)) z.1 z.2) (mu.prod mu))
    (hmass : ∫ x, u x ∂mu = A.phiMass)
    (hnonneg : ∀ x, 0 ≤ u x) :
    |multiWellCompressionMatrix mu A.kappa A.c u a L i j -
      L ^ (-A.kappa) *
        effectiveInteractionMatrix a A.c A.phiMass A.kappa i j| ≤
      A.c * A.C * A.phiMass ^ 2 *
        L ^ (-A.kappa - 2) * ‖a i - a j‖ ^ (-A.kappa - 2) := by
  set d : X := a i - a j
  set center : X := (L : ℝ) • d
  have hdpos : 0 < ‖d‖ := by
    have h4R : (0:ℝ) < 4 * A.R := mul_pos (by norm_num) A.hR
    have hprod : (0:ℝ) < L * ‖d‖ := lt_of_lt_of_le h4R hsep
    exact pos_of_mul_pos_left (by simpa [mul_comm] using hprod) hL.le
  have hcenterScale : ‖center‖ ^ (-A.kappa) =
      L ^ (-A.kappa) * ‖d‖ ^ (-A.kappa) := by
    show ‖(L : ℝ) • d‖ ^ (-A.kappa) =
      L ^ (-A.kappa) * ‖d‖ ^ (-A.kappa)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    exact Real.mul_rpow hL.le (norm_nonneg _)
  have hbound : ∀ x y : X,
      |multiWellTaylorRemainder A.kappa center x y| ≤
        A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) := by
    intro x y
    exact multiWellTaylorRemainder_abs_le A d x y L hL hsep (hX x) (hX y)
  have hr : 0 ≤ A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) := by
    have hLpow : 0 ≤ L ^ (-A.kappa - 2) :=
      Real.rpow_nonneg hL.le _
    have hdpow : 0 ≤ ‖d‖ ^ (-A.kappa - 2) :=
      Real.rpow_nonneg (norm_nonneg _) _
    exact mul_nonneg (mul_nonneg A.hC.le hLpow) hdpow
  have hpair := kernelCrossPairing_multiWell_taylor mu A.kappa center u
    A.phiMass (A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2))
    hprodInt hlinInt hRInt hmass hnonneg hr hbound
  have hcenterPair :
      |kernelCrossPairing (multiWellCrossKernel A.kappa center) mu u u -
        A.phiMass ^ 2 * (L ^ (-A.kappa) * ‖d‖ ^ (-A.kappa))| ≤
        A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) *
          A.phiMass ^ 2 := by
    have hpair' :
        |kernelCrossPairing (multiWellCrossKernel A.kappa center) mu u u -
          A.phiMass ^ 2 * ‖center‖ ^ (-A.kappa)| ≤
          A.C * L ^ (-A.kappa - 2) * ‖d‖ ^ (-A.kappa - 2) *
            A.phiMass ^ 2 := by
      simpa only [pow_two, mul_assoc] using hpair
    rw [hcenterScale] at hpair'
    exact hpair'
  have hentry : multiWellCompressionMatrix mu A.kappa A.c u a L i j =
      -A.c * kernelCrossPairing (multiWellCrossKernel A.kappa center) mu u u := by
    rw [multiWellCompressionMatrix_apply, if_neg hij]
  have heff :
      L ^ (-A.kappa) *
        effectiveInteractionMatrix a A.c A.phiMass A.kappa i j =
      -A.c *
        (A.phiMass ^ 2 * (L ^ (-A.kappa) * ‖d‖ ^ (-A.kappa))) := by
    rw [effectiveInteractionMatrix_apply, if_neg hij]
    show L ^ (-A.kappa) * (-A.c * A.phiMass ^ 2 * ‖d‖ ^ (-A.kappa)) =
      -A.c * (A.phiMass ^ 2 * (L ^ (-A.kappa) * ‖d‖ ^ (-A.kappa)))
    ring
  have hdiff :
      multiWellCompressionMatrix mu A.kappa A.c u a L i j -
        L ^ (-A.kappa) *
          effectiveInteractionMatrix a A.c A.phiMass A.kappa i j =
        -A.c *
          (kernelCrossPairing (multiWellCrossKernel A.kappa center) mu u u -
            A.phiMass ^ 2 * (L ^ (-A.kappa) * ‖d‖ ^ (-A.kappa))) := by
    rw [hentry, heff]
    ring
  rw [hdiff, abs_mul, abs_neg, abs_of_nonneg A.hc.le]
  have hmul := mul_le_mul_of_nonneg_left hcenterPair A.hc.le
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- The entrywise Taylor bound with the error entry used by the row-sum norm
estimate.  Diagonal entries are exactly zero, matching the effective matrix. -/
theorem multiWellCompressionMatrix_entry_error
    [MeasurableSpace X] [InnerProductSpace ℝ X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    (A : TwoWellConstants) (a : ι → X) (u : X → ℝ)
    (L : ℝ) (i j : ι)
    (hL : 0 < L)
    (hsep : ∀ p q : ι, p ≠ q → 4 * A.R ≤ L * ‖a p - a q‖)
    (hX : ∀ x : X, ‖x‖ ≤ A.R)
    (hprodInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2) (mu.prod mu))
    (hlinInt : ∀ p q : ι, MeasureTheory.Integrable
      (fun z : X × X =>
        u z.1 * u z.2 * inner ℝ ((L : ℝ) • (a p - a q)) (z.1 - z.2))
        (mu.prod mu))
    (hRInt : ∀ p q : ι, MeasureTheory.Integrable
      (fun z : X × X =>
        u z.1 * u z.2 *
          multiWellTaylorRemainder A.kappa
            ((L : ℝ) • (a p - a q)) z.1 z.2) (mu.prod mu))
    (hmass : ∫ x, u x ∂mu = A.phiMass)
    (hnonneg : ∀ x, 0 ≤ u x) :
    |multiWellCompressionMatrix mu A.kappa A.c u a L i j -
      L ^ (-A.kappa) *
        effectiveInteractionMatrix a A.c A.phiMass A.kappa i j| ≤
      (if i = j then 0
        else A.c * A.C * A.phiMass ^ 2 *
          L ^ (-A.kappa - 2) * ‖a i - a j‖ ^ (-A.kappa - 2)) := by
  by_cases hij : i = j
  · subst hij
    simp [multiWellCompressionMatrix, effectiveInteractionMatrix]
  · rw [if_neg hij]
    exact multiWellCompressionMatrix_entry_taylor mu A a u L i j hL hij
      (hsep i j hij) hX hprodInt (hlinInt i j) (hRInt i j) hmass hnonneg

/-- The ordered spectral coordinates of the effective interaction matrix. -/
noncomputable def effectiveInteractionEigenvalues
    (a : ι → X) (c m kappa : ℝ) : ι → ℝ :=
  (effectiveInteractionMatrix_isHermitian a c m kappa).eigenvalues

/-- The ordered spectral coordinates `theta_1 <= ... <= theta_N` of the
effective interaction matrix.  Mathlib indexes the antitone eigenvalue
sequence in the reverse order, so `Fin.rev` produces the paper's increasing
convention. -/
noncomputable def effectiveInteractionTheta
    (a : ι → X) (c m kappa : ℝ) : Fin (Fintype.card ι) → ℝ :=
  fun i => (effectiveInteractionMatrix_isHermitian a c m kappa).eigenvalues₀
    (Fin.rev i)

theorem effectiveInteractionTheta_monotone
    (a : ι → X) (c m kappa : ℝ) :
    Monotone (effectiveInteractionTheta a c m kappa) := by
  intro i j hij
  simp only [effectiveInteractionTheta]
  exact (effectiveInteractionMatrix_isHermitian a c m kappa).eigenvalues₀_antitone
    (Fin.rev_anti hij)

theorem effectiveInteractionTheta_sum_eq_zero
    (a : ι → X) (c m kappa : ℝ) :
    ∑ i, effectiveInteractionTheta a c m kappa i = 0 := by
  have hA := effectiveInteractionMatrix_isHermitian a c m kappa
  have heig : ∑ i : ι, hA.eigenvalues i =
      ∑ j : Fin (Fintype.card ι), hA.eigenvalues₀ j := by
    let e : ι ≃ Fin (Fintype.card ι) :=
      (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    have hcomp : ∀ i : ι, hA.eigenvalues i = hA.eigenvalues₀ (e i) := fun i => rfl
    calc
      ∑ i : ι, hA.eigenvalues i = ∑ i : ι, hA.eigenvalues₀ (e i) := by
        simp only [hcomp]
      _ = ∑ j : Fin (Fintype.card ι), hA.eigenvalues₀ j :=
        Equiv.sum_comp e hA.eigenvalues₀
  have hsumEig : ∑ i, effectiveInteractionEigenvalues a c m kappa i = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    rw [effectiveInteractionMatrix_trace_eq_zero] at h
    simpa [effectiveInteractionEigenvalues] using h.symm
  have htheta : ∑ i, effectiveInteractionTheta a c m kappa i =
      ∑ j : Fin (Fintype.card ι), hA.eigenvalues₀ j := by
    simp only [effectiveInteractionTheta]
    exact Equiv.sum_comp (Fin.revPerm (n := Fintype.card ι)) hA.eigenvalues₀
  rw [htheta, ← heig]
  exact hsumEig

theorem exists_positive_effectiveInteractionTheta
    (a : ι → X) (c m kappa : ℝ)
    (hne : effectiveInteractionMatrix a c m kappa ≠ 0) :
    ∃ i : Fin (Fintype.card ι), 0 < effectiveInteractionTheta a c m kappa i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hsum := effectiveInteractionTheta_sum_eq_zero a c m kappa
  have hzero : ∀ i, effectiveInteractionTheta a c m kappa i = 0 := by
    have hnonpos : ∀ i ∈ Finset.univ,
        effectiveInteractionTheta a c m kappa i ≤ 0 := fun i _ => h i
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum i
      (Finset.mem_univ i)
  have hA := effectiveInteractionMatrix_isHermitian a c m kappa
  have hzero₀ : hA.eigenvalues₀ = 0 := by
    funext i
    have hrev := hzero (Fin.rev i)
    simpa [effectiveInteractionTheta, Fin.rev_rev] using hrev
  have hzeroEig : hA.eigenvalues = 0 := by
    funext i
    exact congrFun hzero₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
  exact hne (hA.eigenvalues_eq_zero_iff.mp hzeroEig)

theorem exists_negative_effectiveInteractionTheta
    (a : ι → X) (c m kappa : ℝ)
    (hne : effectiveInteractionMatrix a c m kappa ≠ 0) :
    ∃ i : Fin (Fintype.card ι), effectiveInteractionTheta a c m kappa i < 0 := by
  obtain ⟨i, hi⟩ := exists_positive_effectiveInteractionTheta a c m kappa hne
  by_contra h
  simp only [not_exists, not_lt] at h
  have hsum := effectiveInteractionTheta_sum_eq_zero a c m kappa
  have hzero : ∀ k, effectiveInteractionTheta a c m kappa k = 0 := by
    have hnonneg : ∀ k ∈ Finset.univ,
        0 ≤ effectiveInteractionTheta a c m kappa k := fun k _ => h k
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum k
      (Finset.mem_univ k)
  exact absurd (hzero i) (ne_of_gt hi)

theorem effectiveInteractionTheta_extreme_signs
    (a : ι → X) (c m kappa : ℝ)
    (hne : effectiveInteractionMatrix a c m kappa ≠ 0)
    [NeZero (Fintype.card ι)] :
    effectiveInteractionTheta a c m kappa ⊥ < 0 ∧
      0 < effectiveInteractionTheta a c m kappa ⊤ := by
  have hneg := exists_negative_effectiveInteractionTheta a c m kappa hne
  have hpos := exists_positive_effectiveInteractionTheta a c m kappa hne
  obtain ⟨i, hi⟩ := hneg
  obtain ⟨j, hj⟩ := hpos
  have hmono := effectiveInteractionTheta_monotone a c m kappa
  constructor
  · exact lt_of_le_of_lt (hmono bot_le) hi
  · exact lt_of_lt_of_le hj (hmono le_top)

theorem effectiveInteractionTheta_extreme_signs_of_distinct
    (a : ι → X) (c m kappa : ℝ) (i j : ι)
    (hij : i ≠ j) (hpos : a i ≠ a j) (hc : c ≠ 0) (hm : m ≠ 0)
    [NeZero (Fintype.card ι)] :
    effectiveInteractionTheta a c m kappa ⊥ < 0 ∧
      0 < effectiveInteractionTheta a c m kappa ⊤ :=
  effectiveInteractionTheta_extreme_signs a c m kappa
    (effectiveInteractionMatrix_nonzero a c m kappa i j hij hpos hc hm)

theorem effectiveInteractionEigenvalues_sum_eq_zero
    (a : ι → X) (c m kappa : ℝ) :
    ∑ i, effectiveInteractionEigenvalues a c m kappa i = 0 := by
  have h := (effectiveInteractionMatrix_isHermitian a c m kappa).trace_eq_sum_eigenvalues
  rw [effectiveInteractionMatrix_trace_eq_zero] at h
  simpa [effectiveInteractionEigenvalues] using h.symm

open scoped Matrix.Norms.L2Operator

/-- The largest absolute row sum of a real matrix.  This is the row-sum scale
used in the final estimate of Lemma 4.3. -/
noncomputable def maxAbsRowSum (A : Matrix ι ι ℝ) : ℝ :=
  ⨆ i, ∑ j, |A i j|

theorem le_maxAbsRowSum (A : Matrix ι ι ℝ) (i : ι) :
    ∑ j, |A i j| ≤ maxAbsRowSum A := by
  exact Finite.le_ciSup (f := fun i => ∑ j, |A i j|) i

theorem maxAbsRowSum_nonneg (A : Matrix ι ι ℝ) : 0 ≤ maxAbsRowSum A := by
  exact Real.iSup_nonneg fun i => Finset.sum_nonneg fun j _ => abs_nonneg (A i j)

/-- The quadratic-form estimate behind the symmetric row-sum operator-norm
bound.  Symmetry identifies row and column absolute sums. -/
theorem symmetric_matrix_quadratic_le_maxAbsRowSum
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (x : ι → ℝ) :
    ∑ i, (∑ j, A i j * x j) ^ 2 ≤
      maxAbsRowSum A ^ 2 * ∑ j, x j ^ 2 := by
  classical
  set M : ℝ := maxAbsRowSum A
  have hrow : ∀ i, ∑ j, |A i j| ≤ M := fun i => le_maxAbsRowSum A i
  have hcol : ∀ j, ∑ i, |A i j| ≤ M := by
    intro j
    have h : ∑ i, |A i j| = ∑ i, |A j i| := by
      congr 1 with i
      rw [hA.apply j i]
    rw [h]
    exact hrow j
  have hpoint : ∀ i, (∑ j, A i j * x j) ^ 2 ≤
      (∑ j, |A i j|) * (∑ j, |A i j| * x j ^ 2) := by
    intro i
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (f := fun j => |A i j|)
      (g := fun j => |A i j| * x j ^ 2)
      (fun j _ => abs_nonneg (A i j))
      (fun j _ => mul_nonneg (abs_nonneg (A i j)) (sq_nonneg (x j)))
      (fun j _ => by
        have h : (A i j * x j) ^ 2 = |A i j| * (|A i j| * x j ^ 2) := by
          rw [mul_pow, ← sq_abs (A i j)]
          ring
        rw [h])
    simpa [Finset.sum_mul_sum] using hcs
  have hsum : ∑ i, (∑ j, A i j * x j) ^ 2 ≤
      ∑ i, (∑ j, |A i j|) * (∑ j, |A i j| * x j ^ 2) :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hsplit : ∀ i,
      (∑ j, |A i j|) * (∑ j, |A i j| * x j ^ 2) =
        ∑ j, (∑ k, |A i k|) * (|A i j| * x j ^ 2) := by
    intro i
    exact Finset.mul_sum _ _ _
  have hbound : ∑ i, (∑ j, |A i j|) * (∑ j, |A i j| * x j ^ 2) ≤
      M * (∑ j, (∑ i, |A i j|) * x j ^ 2) := by
    calc
      ∑ i, (∑ j, |A i j|) * (∑ j, |A i j| * x j ^ 2) =
          ∑ i, ∑ j, (∑ k, |A i k|) * (|A i j| * x j ^ 2) := by
        exact Finset.sum_congr rfl fun i _ => hsplit i
      _ ≤ ∑ i, ∑ j, M * (|A i j| * x j ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_right (hrow i)
          (mul_nonneg (abs_nonneg (A i j)) (sq_nonneg (x j)))
      _ = M * (∑ j, (∑ i, |A i j|) * x j ^ 2) := by
        rw [Finset.sum_comm]
        have hinner : ∀ j,
            (∑ i, M * (|A i j| * x j ^ 2)) = M * ((∑ i, |A i j|) * x j ^ 2) := by
          intro j
          calc
            (∑ i, M * (|A i j| * x j ^ 2)) =
                M * (∑ i, |A i j| * x j ^ 2) := (Finset.mul_sum _ _ _).symm
            _ = M * ((∑ i, |A i j|) * x j ^ 2) := by
              rw [Finset.sum_mul]
        calc
          ∑ j, ∑ i, M * (|A i j| * x j ^ 2) =
              ∑ j, M * ((∑ i, |A i j|) * x j ^ 2) :=
            Finset.sum_congr rfl fun j _ => hinner j
          _ = M * (∑ j, (∑ i, |A i j|) * x j ^ 2) := (Finset.mul_sum _ _ _).symm
  have hcolsum : ∑ j, (∑ i, |A i j|) * x j ^ 2 ≤ M * ∑ j, x j ^ 2 := by
    calc
      ∑ j, (∑ i, |A i j|) * x j ^ 2 ≤ ∑ j, M * x j ^ 2 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg (x j))
      _ = M * ∑ j, x j ^ 2 := by rw [Finset.mul_sum]
  calc
    ∑ i, (∑ j, A i j * x j) ^ 2 ≤
        ∑ i, (∑ j, |A i j|) * (∑ j, |A i j| * x j ^ 2) := hsum
    _ ≤ M * (∑ j, (∑ i, |A i j|) * x j ^ 2) := hbound
    _ ≤ M * (M * ∑ j, x j ^ 2) := mul_le_mul_of_nonneg_left hcolsum (maxAbsRowSum_nonneg A)
    _ = M ^ 2 * ∑ j, x j ^ 2 := by ring

/-- The induced Euclidean operator norm of a real symmetric matrix is at most
its largest absolute row sum, as used in Lemma 4.3. -/
theorem symmetric_matrix_l2_opNorm_le_maxAbsRowSum
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    ‖A‖ ≤ maxAbsRowSum A := by
  classical
  have hM : 0 ≤ maxAbsRowSum A := maxAbsRowSum_nonneg A
  have hbound : ∀ x : EuclideanSpace ℝ ι,
      ‖Matrix.toEuclideanLin A x‖ ≤ maxAbsRowSum A * ‖x‖ := by
    intro x
    have hq := symmetric_matrix_quadratic_le_maxAbsRowSum A hA
      (fun i => x i)
    have hnorm : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := EuclideanSpace.real_norm_sq_eq x
    have hout : ‖Matrix.toEuclideanLin A x‖ ^ 2 =
        ∑ i, (∑ j, A i j * x j) ^ 2 := by
      rw [Matrix.toEuclideanLin_apply, EuclideanSpace.real_norm_sq_eq]
      simp only [Matrix.mulVec_apply_eq_sum, PiLp.toLp_apply]
    have h : ∑ i, (∑ j, A i j * x j) ^ 2 ≤
        maxAbsRowSum A ^ 2 * ‖x‖ ^ 2 := by
      calc
        ∑ i, (∑ j, A i j * x j) ^ 2 ≤
            maxAbsRowSum A ^ 2 * ∑ j, x j ^ 2 := hq
        _ = maxAbsRowSum A ^ 2 * ‖x‖ ^ 2 := by rw [hnorm]
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))]
    simpa [hout, hnorm, mul_pow, abs_of_nonneg hM] using h
  refine le_trans (le_of_eq (Matrix.l2_opNorm_def A).symm) ?_
  exact ContinuousLinearMap.opNorm_le_bound _ hM (fun x => by
    simpa [Matrix.toEuclideanLin_apply] using hbound x)

/-- The entrywise-to-operator-norm compression estimate from Lemma 4.3.
If the entries of the compression error are bounded by `E` and every row
sum of `E` is at most `epsilon`, then the symmetric error matrix has L2
operator norm at most `epsilon`. -/
theorem entrywise_matrix_norm_le
    (T M : Matrix ι ι ℝ) (E : ι → ι → ℝ) (epsilon : ℝ)
    (hT : (T - M).IsSymm)
    (hentry : ∀ i j, |T i j - M i j| ≤ E i j)
    (hrow : ∀ i, ∑ j, E i j ≤ epsilon) (hnonneg : 0 ≤ epsilon) :
    ‖T - M‖ ≤ epsilon := by
  classical
  have hentry' : ∀ i j, |(T - M) i j| ≤ E i j := by
    intro i j
    rw [Matrix.sub_apply]
    exact hentry i j
  have hrow' : ∀ i, ∑ j, |(T - M) i j| ≤ epsilon := by
    intro i
    exact le_trans (Finset.sum_le_sum fun j _ => hentry' i j) (hrow i)
  have hmax : maxAbsRowSum (T - M) ≤ epsilon := by
    exact Real.iSup_le hrow' hnonneg
  exact le_trans (symmetric_matrix_l2_opNorm_le_maxAbsRowSum (T - M) hT) hmax

theorem exists_positive_effectiveInteractionEigenvalue
    (a : ι → X) (c m kappa : ℝ)
    (hne : effectiveInteractionMatrix a c m kappa ≠ 0) :
    ∃ i, 0 < effectiveInteractionEigenvalues a c m kappa i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hsum := effectiveInteractionEigenvalues_sum_eq_zero a c m kappa
  have hzero : ∀ i, effectiveInteractionEigenvalues a c m kappa i = 0 := by
    have hnonpos : ∀ i ∈ Finset.univ,
        effectiveInteractionEigenvalues a c m kappa i ≤ 0 := fun i _ => h i
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum i
      (Finset.mem_univ i)
  have hzeroEig :
      (effectiveInteractionMatrix_isHermitian a c m kappa).eigenvalues = 0 := by
    funext i
    exact hzero i
  have hmatrix : effectiveInteractionMatrix a c m kappa = 0 :=
    (effectiveInteractionMatrix_isHermitian a c m kappa).eigenvalues_eq_zero_iff.mp
      hzeroEig
  exact hne hmatrix

theorem exists_positive_effectiveInteractionEigenvalue_of_distinct
    (a : ι → X) (c m kappa : ℝ) (i j : ι)
    (hij : i ≠ j) (hpos : a i ≠ a j) (hc : c ≠ 0) (hm : m ≠ 0) :
    ∃ k, 0 < effectiveInteractionEigenvalues a c m kappa k :=
  exists_positive_effectiveInteractionEigenvalue a c m kappa
    (effectiveInteractionMatrix_nonzero a c m kappa i j hij hpos hc hm)

theorem exists_negative_effectiveInteractionEigenvalue
    (a : ι → X) (c m kappa : ℝ)
    (hne : effectiveInteractionMatrix a c m kappa ≠ 0) :
    ∃ i, effectiveInteractionEigenvalues a c m kappa i < 0 := by
  obtain ⟨i, hi⟩ := exists_positive_effectiveInteractionEigenvalue a c m kappa hne
  by_contra h
  simp only [not_exists, not_lt] at h
  have hsum := effectiveInteractionEigenvalues_sum_eq_zero a c m kappa
  have hzero : ∀ k, effectiveInteractionEigenvalues a c m kappa k = 0 := by
    have hnonneg : ∀ k ∈ Finset.univ,
        0 ≤ effectiveInteractionEigenvalues a c m kappa k := fun k _ => h k
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum k
      (Finset.mem_univ k)
  exact absurd (hzero i) (ne_of_gt hi)

/-- The geometric constant `Sigma_p(a) = max_i sum_{j != i} |a_i - a_j|^(-p)` from
equation `eq:geometry-constants`. -/
noncomputable def sigmaKappa (a : ι → X) (kappa : ℝ) : ℝ :=
  ⨆ i, ∑ j, if i = j then (0:ℝ) else ‖a i - a j‖ ^ (-kappa)

theorem sigmaKappa_row_nonneg (a : ι → X) (kappa : ℝ) (i : ι) :
    0 ≤ ∑ j, (if i = j then (0:ℝ) else ‖a i - a j‖ ^ (-kappa)) := by
  apply Finset.sum_nonneg
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij]
    exact Real.rpow_nonneg (norm_nonneg _) _

theorem sigmaKappa_nonneg (a : ι → X) (kappa : ℝ) :
    0 ≤ sigmaKappa a kappa :=
  Real.iSup_nonneg (sigmaKappa_row_nonneg a kappa)

/-- Each row sum is bounded by the maximal row sum `Sigma_p(a)`. -/
theorem row_le_sigmaKappa (a : ι → X) (kappa : ℝ) (i : ι) :
    ∑ j, (if i = j then (0:ℝ) else ‖a i - a j‖ ^ (-kappa)) ≤ sigmaKappa a kappa :=
  le_ciSup (f := fun i => ∑ j, (if i = j then (0:ℝ) else ‖a i - a j‖ ^ (-kappa)))
    (Set.finite_range _).bddAbove i

/-- The perturbation scale `gamma_L` from Lemma 4.1. -/
noncomputable def multiWellGamma
    (A : TwoWellConstants) (a : ι → X) (L : ℝ) : ℝ :=
  A.c * 2 ^ A.kappa * A.volumeD * sigmaKappa a A.kappa * L ^ (-A.kappa)

/-- The compression-error scale `epsilon_L` from Lemma 4.3. -/
noncomputable def multiWellEpsilon
    (A : TwoWellConstants) (a : ι → X) (L : ℝ) : ℝ :=
  A.c * A.C * A.phiMass ^ 2 * sigmaKappa a (A.kappa + 2) *
    L ^ (-A.kappa - 2)

theorem multiWellEpsilon_nonneg
    (A : TwoWellConstants) (a : ι → X) (L : ℝ) (hL : 0 ≤ L) :
    0 ≤ multiWellEpsilon A a L := by
  have hc : 0 ≤ A.c := A.hc.le
  have hC : 0 ≤ A.C := A.hC.le
  have hm : 0 ≤ A.phiMass ^ 2 := sq_nonneg _
  have hs : 0 ≤ sigmaKappa a (A.kappa + 2) :=
    sigmaKappa_nonneg a (A.kappa + 2)
  have hLpow : 0 ≤ L ^ (-A.kappa - 2) := Real.rpow_nonneg hL _
  have hbase : 0 ≤ A.c * A.C * A.phiMass ^ 2 := by
    positivity
  have hsigma : 0 ≤ A.c * A.C * A.phiMass ^ 2 *
      sigmaKappa a (A.kappa + 2) :=
    mul_nonneg hbase hs
  simpa [multiWellEpsilon] using mul_nonneg hsigma hLpow

/-- The row sum of the finite-well Taylor error entries.  The row is bounded
by the full nonnegative double sum `Sigma_{kappa+2}(a)`, giving the explicit
`epsilon_L` budget from equation `eq:compression-error`. -/
theorem multiWellCompressionMatrix_error_row
    (A : TwoWellConstants) (a : ι → X) (L : ℝ) (i : ι)
    (hL : 0 ≤ L) :
    ∑ j, (if i = j then (0:ℝ)
      else A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) *
        ‖a i - a j‖ ^ (-A.kappa - 2)) ≤
      multiWellEpsilon A a L := by
  classical
  set c₀ : ℝ := A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2)
  have hpow : ∀ x : ℝ, x ^ (-A.kappa - 2) = x ^ (-(A.kappa + 2)) := by
    intro x
    rw [show (-A.kappa - 2 : ℝ) = -(A.kappa + 2) by ring]
  set q : ι → ι → ℝ := fun p r =>
    if p = r then (0:ℝ) else ‖a p - a r‖ ^ (-(A.kappa + 2))
  have hq_nonneg : ∀ p r, 0 ≤ q p r := by
    intro p r
    by_cases hpr : p = r
    · simp [q, hpr]
    · have hqp : q p r =
          if p = r then (0:ℝ) else ‖a p - a r‖ ^ (-(A.kappa + 2)) := rfl
      rw [hqp, if_neg hpr]
      exact Real.rpow_nonneg (norm_nonneg _) _
  have hrowq : ∑ r, q i r ≤ sigmaKappa a (A.kappa + 2) :=
    row_le_sigmaKappa a (A.kappa + 2) i
  have hc₀ : 0 ≤ c₀ := by
    have hLpow : 0 ≤ L ^ (-A.kappa - 2) := Real.rpow_nonneg hL _
    have hbase : 0 ≤ A.c * A.C * A.phiMass ^ 2 :=
      mul_nonneg (mul_nonneg A.hc.le A.hC.le) (sq_nonneg _)
    exact mul_nonneg hbase hLpow
  have hterm : ∀ j,
      (if i = j then (0:ℝ)
        else A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) *
          ‖a i - a j‖ ^ (-A.kappa - 2)) = c₀ * q i j := by
    intro j
    by_cases hij : i = j
    · subst hij
      simp [q, c₀]
    · rw [if_neg hij]
      have hqij : q i j =
          if i = j then (0:ℝ) else ‖a i - a j‖ ^ (-(A.kappa + 2)) := rfl
      rw [hqij, if_neg hij]
      show A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) *
          ‖a i - a j‖ ^ (-A.kappa - 2) =
        c₀ * ‖a i - a j‖ ^ (-(A.kappa + 2))
      simp only [c₀]
      rw [hpow (‖a i - a j‖)]
  calc
    ∑ j, (if i = j then (0:ℝ)
        else A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) *
          ‖a i - a j‖ ^ (-A.kappa - 2)) =
        ∑ j, c₀ * q i j := Finset.sum_congr rfl (fun j _ => hterm j)
    _ = c₀ * ∑ j, q i j := (Finset.mul_sum _ _ _).symm
    _ ≤ c₀ * sigmaKappa a (A.kappa + 2) :=
      mul_le_mul_of_nonneg_left hrowq hc₀
    _ = multiWellEpsilon A a L := by
      simp [multiWellEpsilon, c₀, mul_assoc, mul_comm,
        mul_left_comm]

/-- The finite-well compression matrix satisfies the operator-norm estimate
`hnorm` of `FinalTheoremMultiWell_exactCompression` whenever the ground-state
pairing hypotheses of the Taylor theorem are available. -/
theorem multiWellCompressionMatrix_norm_le
    [MeasurableSpace X] [InnerProductSpace ℝ X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    (A : TwoWellConstants) (a : ι → X) (u : X → ℝ) (L : ℝ)
    (hL : 0 < L)
    (hsep : ∀ p q : ι, p ≠ q → 4 * A.R ≤ L * ‖a p - a q‖)
    (hX : ∀ x : X, ‖x‖ ≤ A.R)
    (hprodInt : MeasureTheory.Integrable
      (fun z : X × X => u z.1 * u z.2) (mu.prod mu))
    (hlinInt : ∀ p q : ι, MeasureTheory.Integrable
      (fun z : X × X =>
        u z.1 * u z.2 * inner ℝ ((L : ℝ) • (a p - a q)) (z.1 - z.2))
        (mu.prod mu))
    (hRInt : ∀ p q : ι, MeasureTheory.Integrable
      (fun z : X × X =>
        u z.1 * u z.2 *
          multiWellTaylorRemainder A.kappa
            ((L : ℝ) • (a p - a q)) z.1 z.2) (mu.prod mu))
    (hmass : ∫ x, u x ∂mu = A.phiMass)
    (hnonneg : ∀ x, 0 ≤ u x) :
    ‖multiWellCompressionMatrix mu A.kappa A.c u a L -
      L ^ (-A.kappa) •
        effectiveInteractionMatrix a A.c A.phiMass A.kappa‖ ≤
      multiWellEpsilon A a L := by
  classical
  set E : ι → ι → ℝ := fun p r =>
    if p = r then (0:ℝ)
    else A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) *
      ‖a p - a r‖ ^ (-A.kappa - 2)
  have hentry : ∀ p r,
      |multiWellCompressionMatrix mu A.kappa A.c u a L p r -
        L ^ (-A.kappa) *
          effectiveInteractionMatrix a A.c A.phiMass A.kappa p r| ≤ E p r := by
    intro p r
    exact multiWellCompressionMatrix_entry_error mu A a u L p r hL hsep hX
      hprodInt hlinInt hRInt hmass hnonneg
  have hrow : ∀ p, ∑ r, E p r ≤ multiWellEpsilon A a L := by
    intro p
    exact multiWellCompressionMatrix_error_row A a L p hL.le
  have hsymm :
      (multiWellCompressionMatrix mu A.kappa A.c u a L -
        L ^ (-A.kappa) •
          effectiveInteractionMatrix a A.c A.phiMass A.kappa).IsSymm :=
    (multiWellCompressionMatrix_isSymm mu A.kappa A.c u a L).sub
      ((effectiveInteractionMatrix_isSymm a A.c A.phiMass A.kappa).smul _)
  refine entrywise_matrix_norm_le
    (multiWellCompressionMatrix mu A.kappa A.c u a L)
    (L ^ (-A.kappa) •
      effectiveInteractionMatrix a A.c A.phiMass A.kappa)
    E (multiWellEpsilon A a L) hsymm ?_ hrow
    (multiWellEpsilon_nonneg A a L hL.le)
  intro p r
  simpa [Matrix.smul_apply, smul_eq_mul] using hentry p r

/-- The exact compression-error matrix estimate from Lemma 4.3, specialized
to the effective interaction matrix.  The compression matrix `T` is left as
the matrix produced by the finite-dimensional block compression; only its
entrywise Taylor bounds are consumed here. -/
theorem compressionNorm_le_of_entrywise
    (A : TwoWellConstants) (a : ι → X) (L : ℝ)
    (T : Matrix ι ι ℝ) (E : ι → ι → ℝ)
    (hT : (T - L ^ (-A.kappa) •
      effectiveInteractionMatrix a A.c A.phiMass A.kappa).IsSymm)
    (hentry : ∀ i j,
      |T i j - L ^ (-A.kappa) *
        effectiveInteractionMatrix a A.c A.phiMass A.kappa i j| ≤ E i j)
    (hrow : ∀ i, ∑ j, E i j ≤ multiWellEpsilon A a L)
    (heps : 0 ≤ multiWellEpsilon A a L) :
    ‖T - L ^ (-A.kappa) •
      effectiveInteractionMatrix a A.c A.phiMass A.kappa‖ ≤
      multiWellEpsilon A a L := by
  refine entrywise_matrix_norm_le T
    (L ^ (-A.kappa) • effectiveInteractionMatrix a A.c A.phiMass A.kappa)
    E (multiWellEpsilon A a L) hT ?_ hrow heps
  intro i j
  simpa [Matrix.smul_apply, smul_eq_mul] using hentry i j

section Weyl

open scoped RealInnerProductSpace

variable {n : ℕ} {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Rayleigh upper bound on a span of eigenvectors.  This is the elementary
quadratic-form half of the Courant--Fischer comparison used for Lemma 4.3. -/
theorem rayleigh_le_on_eigenvectorSpan
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (m : ℝ) (s : Set (Fin n))
    (hm : ∀ i ∈ s, hT.eigenvalues hn i ≤ m)
    (x : E)
    (hx : x ∈ Submodule.span ℝ ((hT.eigenvectorBasis hn).toBasis '' s)) :
    inner ℝ (T x) x ≤ m * ‖x‖ ^ 2 := by
  classical
  set b := hT.eigenvectorBasis hn
  set mu := hT.eigenvalues hn
  have hrepr : ∀ i : Fin n, b.toBasis.repr x i = inner ℝ (b i) x := by
    intro i
    simpa [OrthonormalBasis.coe_toBasis_repr_apply]
      using OrthonormalBasis.repr_apply_apply b x i
  have hsupport : ∀ i : Fin n, inner ℝ (b i) x ≠ 0 → i ∈ s := by
    intro i hi
    have hsub := Module.Basis.repr_support_subset_of_mem_span b.toBasis s hx
    have hmem : i ∈ (b.toBasis.repr x).support := by
      simpa [Finsupp.mem_support_iff, hrepr] using hi
    exact hsub hmem
  have hsum : inner ℝ (T x) x =
      ∑ i, mu i * inner ℝ (b i) x * inner ℝ (b i) x := by
    calc
      inner ℝ (T x) x =
          ∑ i, inner ℝ (T x) (b i) * inner ℝ (b i) x :=
        (OrthonormalBasis.sum_inner_mul_inner b (T x) x).symm
      _ = ∑ i, inner ℝ x (T (b i)) * inner ℝ (b i) x := by
        congr 1 with i
        rw [hT x (b i)]
      _ = ∑ i, mu i * inner ℝ (b i) x * inner ℝ (b i) x := by
        congr 1 with i
        have hbi : T (b i) = mu i • b i := by
          simpa [b, mu] using hT.apply_eigenvectorBasis hn i
        rw [hbi, inner_smul_right, real_inner_comm x (b i)]
  have hpoint : ∀ i, mu i * inner ℝ (b i) x * inner ℝ (b i) x ≤
      m * inner ℝ (b i) x * inner ℝ (b i) x := by
    intro i
    by_cases hi : i ∈ s
    · nlinarith [hm i hi, sq_nonneg (inner ℝ (b i) x)]
    · have hzero : inner ℝ (b i) x = 0 := by
        by_contra h
        exact hi (hsupport i h)
      simp [hzero]
  have hsumle : ∑ i, mu i * inner ℝ (b i) x * inner ℝ (b i) x ≤
      ∑ i, m * inner ℝ (b i) x * inner ℝ (b i) x :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hnorm : ∑ i, inner ℝ (b i) x * inner ℝ (b i) x = ‖x‖ ^ 2 := by
    have h := OrthonormalBasis.sum_sq_norm_inner_right b x
    calc
      ∑ i, inner ℝ (b i) x * inner ℝ (b i) x =
          ∑ i, |inner ℝ (b i) x| ^ 2 := by
        congr 1 with i
        rw [sq_abs]
        ring
      _ = ‖x‖ ^ 2 := by
        simpa [Real.norm_eq_abs] using h
  calc
    inner ℝ (T x) x =
        ∑ i, mu i * inner ℝ (b i) x * inner ℝ (b i) x := hsum
    _ ≤ ∑ i, m * inner ℝ (b i) x * inner ℝ (b i) x := hsumle
    _ = m * (∑ i, inner ℝ (b i) x * inner ℝ (b i) x) := by
      rw [Finset.mul_sum]
      congr 1 with i
      ring
    _ = m * ‖x‖ ^ 2 := by rw [hnorm]

/-- Rayleigh lower bound on a span of eigenvectors. -/
theorem rayleigh_ge_on_eigenvectorSpan
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (m : ℝ) (s : Set (Fin n))
    (hm : ∀ i ∈ s, m ≤ hT.eigenvalues hn i)
    (x : E)
    (hx : x ∈ Submodule.span ℝ ((hT.eigenvectorBasis hn).toBasis '' s)) :
    m * ‖x‖ ^ 2 ≤ inner ℝ (T x) x := by
  classical
  set b := hT.eigenvectorBasis hn
  set mu := hT.eigenvalues hn
  have hrepr : ∀ i : Fin n, b.toBasis.repr x i = inner ℝ (b i) x := by
    intro i
    simpa [OrthonormalBasis.coe_toBasis_repr_apply]
      using OrthonormalBasis.repr_apply_apply b x i
  have hsupport : ∀ i : Fin n, inner ℝ (b i) x ≠ 0 → i ∈ s := by
    intro i hi
    have hsub := Module.Basis.repr_support_subset_of_mem_span b.toBasis s hx
    have hmem : i ∈ (b.toBasis.repr x).support := by
      simpa [Finsupp.mem_support_iff, hrepr] using hi
    exact hsub hmem
  have hsum : inner ℝ (T x) x =
      ∑ i, mu i * inner ℝ (b i) x * inner ℝ (b i) x := by
    calc
      inner ℝ (T x) x =
          ∑ i, inner ℝ (T x) (b i) * inner ℝ (b i) x :=
        (OrthonormalBasis.sum_inner_mul_inner b (T x) x).symm
      _ = ∑ i, inner ℝ x (T (b i)) * inner ℝ (b i) x := by
        congr 1 with i
        rw [hT x (b i)]
      _ = ∑ i, mu i * inner ℝ (b i) x * inner ℝ (b i) x := by
        congr 1 with i
        have hbi : T (b i) = mu i • b i := by
          simpa [b, mu] using hT.apply_eigenvectorBasis hn i
        rw [hbi, inner_smul_right, real_inner_comm x (b i)]
  have hpoint : ∀ i, m * inner ℝ (b i) x * inner ℝ (b i) x ≤
      mu i * inner ℝ (b i) x * inner ℝ (b i) x := by
    intro i
    by_cases hi : i ∈ s
    · nlinarith [hm i hi, sq_nonneg (inner ℝ (b i) x)]
    · have hzero : inner ℝ (b i) x = 0 := by
        by_contra h
        exact hi (hsupport i h)
      simp [hzero]
  have hsumle : ∑ i, m * inner ℝ (b i) x * inner ℝ (b i) x ≤
      ∑ i, mu i * inner ℝ (b i) x * inner ℝ (b i) x :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hnorm : ∑ i, inner ℝ (b i) x * inner ℝ (b i) x = ‖x‖ ^ 2 := by
    have h := OrthonormalBasis.sum_sq_norm_inner_right b x
    calc
      ∑ i, inner ℝ (b i) x * inner ℝ (b i) x =
          ∑ i, |inner ℝ (b i) x| ^ 2 := by
        congr 1 with i
        rw [sq_abs]
        ring
      _ = ‖x‖ ^ 2 := by
        simpa [Real.norm_eq_abs] using h
  calc
    m * ‖x‖ ^ 2 = m * (∑ i, inner ℝ (b i) x * inner ℝ (b i) x) := by rw [hnorm]
    _ = ∑ i, m * inner ℝ (b i) x * inner ℝ (b i) x := by
      rw [Finset.mul_sum]
      congr 1 with i
      ring
    _ ≤ ∑ i, mu i * inner ℝ (b i) x * inner ℝ (b i) x := hsumle
    _ = inner ℝ (T x) x := hsum.symm

theorem finrank_eigenvectorSpan_Iic
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Module.finrank ℝ
      (Submodule.span ℝ ((hT.eigenvectorBasis hn).toBasis ''
        (Finset.Iic k : Set (Fin n)))) = k.val + 1 := by
  classical
  set b := hT.eigenvectorBasis hn
  set s := (Finset.Iic k : Set (Fin n))
  have hli : LinearIndependent ℝ (fun i : ↥(Finset.Iic k) => b.toBasis i.val) :=
    b.toBasis.linearIndependent.comp (fun i : ↥(Finset.Iic k) => i.val)
      Subtype.val_injective
  have hspan : Submodule.span ℝ
      (Set.range (fun i : ↥(Finset.Iic k) => b.toBasis i.val)) =
      Submodule.span ℝ (b.toBasis '' s) := by
    congr 1
    ext x
    simp [s, Set.image_eq_range]
  rw [← hspan, finrank_span_eq_card hli]
  rw [Fintype.card_coe, Fin.card_Iic]

theorem finrank_eigenvectorSpan_Ici
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Module.finrank ℝ
      (Submodule.span ℝ ((hT.eigenvectorBasis hn).toBasis ''
        (Finset.Ici k : Set (Fin n)))) = n - k.val := by
  classical
  set b := hT.eigenvectorBasis hn
  set s := (Finset.Ici k : Set (Fin n))
  have hli : LinearIndependent ℝ (fun i : ↥(Finset.Ici k) => b.toBasis i.val) :=
    b.toBasis.linearIndependent.comp (fun i : ↥(Finset.Ici k) => i.val)
      Subtype.val_injective
  have hspan : Submodule.span ℝ
      (Set.range (fun i : ↥(Finset.Ici k) => b.toBasis i.val)) =
      Submodule.span ℝ (b.toBasis '' s) := by
    congr 1
    ext x
    simp [s, Set.image_eq_range]
  rw [← hspan, finrank_span_eq_card hli]
  rw [Fintype.card_coe, Fin.card_Ici]

/-- A finite-dimensional intersection lemma used in the Courant--Fischer
argument: two subspaces of dimensions `r` and `q` in an `n`-dimensional
space with `r + q = n + 1` have a nonzero intersection. -/
theorem exists_mem_ne_zero_of_finrank_inf
    (S U : Submodule ℝ E) {r q : ℕ}
    (hS : Module.finrank ℝ ↥S = r) (hU : Module.finrank ℝ ↥U = q)
    (hn : Module.finrank ℝ E = n) (h : r + q = n + 1) :
    ∃ x, x ∈ S ∧ x ∈ U ∧ x ≠ 0 := by
  have hsup_le : Module.finrank ℝ ↥(S ⊔ U) ≤ n := by
    rw [← hn]
    exact (Submodule.finrank_mono (le_top : S ⊔ U ≤ ⊤)).trans
      (le_of_eq (finrank_top ℝ E))
  have hkey : Module.finrank ℝ ↥(S ⊔ U) + Module.finrank ℝ ↥(S ⊓ U) = n + 1 := by
    rw [Submodule.finrank_sup_add_finrank_inf_eq, hS, hU, h]
  have hinf : 0 < Module.finrank ℝ ↥(S ⊓ U) := by
    omega
  have hne : S ⊓ U ≠ ⊥ := by
    intro hbot
    rw [hbot] at hinf
    simp at hinf
  obtain ⟨x, hx, hne0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨x, hx.1, hx.2, hne0⟩

/-- One-sided Weyl comparison from a quadratic-form perturbation bound. -/
theorem eigenvalue_le_of_quadratic_perturbation
    (T S : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpert : ∀ x : E, |inner ℝ ((T - S) x) x| ≤ δ * ‖x‖ ^ 2)
    (k : Fin n) :
    hT.eigenvalues hn k ≤ hS.eigenvalues hn k + δ := by
  classical
  set UT := Submodule.span ℝ ((hT.eigenvectorBasis hn).toBasis ''
    (Finset.Iic k : Set (Fin n)))
  set VS := Submodule.span ℝ ((hS.eigenvectorBasis hn).toBasis ''
    (Finset.Ici k : Set (Fin n)))
  have hdimT : Module.finrank ℝ ↥UT = k.val + 1 :=
    finrank_eigenvectorSpan_Iic T hT hn k
  have hdimS : Module.finrank ℝ ↥VS = n - k.val :=
    finrank_eigenvectorSpan_Ici S hS hn k
  obtain ⟨x, hxT, hxS, hxne⟩ := exists_mem_ne_zero_of_finrank_inf
    UT VS hdimT hdimS hn (by omega)
  have hmT : ∀ i ∈ (Finset.Iic k : Set (Fin n)),
      hT.eigenvalues hn k ≤ hT.eigenvalues hn i := by
    intro i hi
    exact hT.eigenvalues_antitone hn (Finset.mem_Iic.mp hi)
  have hmS : ∀ i ∈ (Finset.Ici k : Set (Fin n)),
      hS.eigenvalues hn i ≤ hS.eigenvalues hn k := by
    intro i hi
    exact hS.eigenvalues_antitone hn (Finset.mem_Ici.mp hi)
  have hqT := rayleigh_ge_on_eigenvectorSpan T hT hn
    (hT.eigenvalues hn k) (Finset.Iic k : Set (Fin n)) hmT x hxT
  have hqS := rayleigh_le_on_eigenvectorSpan S hS hn
    (hS.eigenvalues hn k) (Finset.Ici k : Set (Fin n)) hmS x hxS
  have hq : inner ℝ ((T - S) x) x =
      inner ℝ (T x) x - inner ℝ (S x) x := by
    simp [map_sub, inner_sub_left]
  have hupper : inner ℝ (T x) x - inner ℝ (S x) x ≤ δ * ‖x‖ ^ 2 := by
    rw [← hq]
    exact (abs_le.mp (hpert x)).2
  have hnormpos : 0 < ‖x‖ ^ 2 := by
    positivity
  have hcore : hT.eigenvalues hn k * ‖x‖ ^ 2 ≤
      (hS.eigenvalues hn k + δ) * ‖x‖ ^ 2 := by
    nlinarith [hqT, hqS, hupper]
  have hdiv := div_le_div_of_nonneg_right hcore (le_of_lt hnormpos)
  have hleft : (hT.eigenvalues hn k * ‖x‖ ^ 2) / ‖x‖ ^ 2 =
      hT.eigenvalues hn k := by
    field_simp [hnormpos.ne']
  have hright : ((hS.eigenvalues hn k + δ) * ‖x‖ ^ 2) / ‖x‖ ^ 2 =
      hS.eigenvalues hn k + δ := by
    field_simp [hnormpos.ne']
  rw [hleft, hright] at hdiv
  exact hdiv

/-- Absolute Weyl comparison from a quadratic-form perturbation bound. -/
theorem eigenvalue_abs_le_of_quadratic_perturbation
    (T S : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpert : ∀ x : E, |inner ℝ ((T - S) x) x| ≤ δ * ‖x‖ ^ 2)
    (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ δ := by
  have h1 := eigenvalue_le_of_quadratic_perturbation T S hT hS hn δ hδ hpert k
  have hpert' : ∀ x : E, |inner ℝ ((S - T) x) x| ≤ δ * ‖x‖ ^ 2 := by
    intro x
    have hq : inner ℝ ((S - T) x) x = - inner ℝ ((T - S) x) x := by
      simp [map_sub, inner_sub_left]
    rw [hq]
    simpa using hpert x
  have h2 := eigenvalue_le_of_quadratic_perturbation S T hS hT hn δ hδ hpert' k
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The quadratic form of a matrix is controlled by its L2 operator norm. -/
theorem matrix_quadratic_le_opNorm
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    |inner ℝ (Matrix.toEuclideanLin A x) x| ≤ ‖A‖ * ‖x‖ ^ 2 := by
  have hle : ‖Matrix.toEuclideanLin A x‖ ≤ ‖A‖ * ‖x‖ := by
    have h := ContinuousLinearMap.le_opNorm
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) x
    rw [Matrix.l2_opNorm_def A]
    simpa [Matrix.toEuclideanLin_apply] using h
  calc
    |inner ℝ (Matrix.toEuclideanLin A x) x| ≤
        ‖Matrix.toEuclideanLin A x‖ * ‖x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg x)
    _ = ‖A‖ * ‖x‖ ^ 2 := by ring

/-- Matrix Weyl comparison from an L2 operator-norm bound. -/
theorem matrix_eigenvalue_abs_le_of_opNorm
    (A B : Matrix ι ι ℝ) (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (δ : ℝ) (hδ : 0 ≤ δ) (hnorm : ‖A - B‖ ≤ δ)
    (k : Fin (Fintype.card ι)) :
    |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ δ := by
  have hsymA : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hsymB : (Matrix.toEuclideanLin B).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hpert : ∀ x : EuclideanSpace ℝ ι,
      |inner ℝ ((Matrix.toEuclideanLin A - Matrix.toEuclideanLin B) x) x| ≤
        δ * ‖x‖ ^ 2 := by
    intro x
    have h := matrix_quadratic_le_opNorm (A - B) x
    have heq : Matrix.toEuclideanLin (A - B) =
        Matrix.toEuclideanLin A - Matrix.toEuclideanLin B := by
      simp [map_sub]
    rw [heq] at h
    exact h.trans (mul_le_mul_of_nonneg_right hnorm (sq_nonneg _))
  exact eigenvalue_abs_le_of_quadratic_perturbation
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B)
    hsymA hsymB (finrank_euclideanSpace (𝕜 := ℝ) (ι := ι)) δ hδ hpert k

/-- Scaling a matrix scales its characteristic-polynomial roots. -/
theorem charpoly_smul_eq_scaleRoots (c : ℝ) (A : Matrix ι ι ℝ) :
    (c • A).charpoly = A.charpoly.scaleRoots c := by
  by_cases hc : c = 0
  · subst hc
    have hzero : ((0 : ℝ) • A).charpoly = Polynomial.X ^ Fintype.card ι := by
      rw [zero_smul, Matrix.charpoly_zero]
    have hscale : A.charpoly.scaleRoots 0 =
        Polynomial.X ^ Fintype.card ι := by
      rw [Polynomial.scaleRoots_zero, Matrix.charpoly_natDegree_eq_dim]
      simpa [Matrix.charpoly_monic A] using
        (Polynomial.Monic.leadingCoeff (Matrix.charpoly_monic A)).symm
    exact hzero.trans hscale.symm
  · apply Polynomial.funext
    intro x
    have hxc : c * (x / c) = x := by field_simp [hc]
    calc
      ((c • A).charpoly).eval x =
          (Matrix.scalar ι x - c • A).det :=
        Matrix.eval_charpoly _ _
      _ = (c • (Matrix.scalar ι (x / c) - A)).det := by
        congr 1
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.sub_apply,
            Matrix.diagonal_apply_eq]
          field_simp [hc]
        · simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.sub_apply,
            Matrix.diagonal_apply_ne _ hij]
      _ = c ^ Fintype.card ι *
          (Matrix.scalar ι (x / c) - A).det :=
        Matrix.det_smul _ _
      _ = c ^ Fintype.card ι * A.charpoly.eval (x / c) := by
        rw [Matrix.eval_charpoly]
      _ = (A.charpoly.scaleRoots c).eval x := by
        rw [← hxc, Polynomial.scaleRoots_eval_mul,
          Matrix.charpoly_natDegree_eq_dim]
        field_simp [hc]

/-- Positive scalar multiplication scales the ordered eigenvalues. -/
theorem eigenvalues₀_smul (c : ℝ) (A : Matrix ι ι ℝ)
    (hA : Matrix.IsHermitian A) (hCA : Matrix.IsHermitian (c • A))
    (hc : 0 < c) (k : Fin (Fintype.card ι)) :
    hCA.eigenvalues₀ k = c * hA.eigenvalues₀ k := by
  have hroots : (c • A).charpoly.roots =
      A.charpoly.roots.map (fun x => c * x) := by
    rw [charpoly_smul_eq_scaleRoots]
    exact Polynomial.roots_scaleRoots A.charpoly
      (isUnit_iff_ne_zero.mpr (ne_of_gt hc))
  have hre : ((c • A).charpoly.roots.map RCLike.re) =
      (A.charpoly.roots.map RCLike.re).map (c * ·) := by
    rw [hroots]
    simp [Multiset.map_map]
  have hA' := hA.sort_roots_charpoly_eq_eigenvalues₀
  have hCA' := hCA.sort_roots_charpoly_eq_eigenvalues₀
  have horder : ∀ a ∈ A.charpoly.roots.map RCLike.re,
      ∀ b ∈ A.charpoly.roots.map RCLike.re,
        (a ≥ b) ↔ (c * a ≥ c * b) := by
    intro a _ b _
    constructor <;> intro h
    · exact mul_le_mul_of_nonneg_left h hc.le
    · exact le_of_mul_le_mul_left h hc
  have hsortmap : List.map (c * ·)
      ((A.charpoly.roots.map RCLike.re).sort (· ≥ ·)) =
      ((A.charpoly.roots.map RCLike.re).map (c * ·)).sort (· ≥ ·) :=
    Multiset.map_sort _ _ _ _ horder
  have hlist : List.map (c * ·) (List.ofFn hA.eigenvalues₀) =
      List.ofFn (fun i => c * hA.eigenvalues₀ i) := by
    rw [List.map_ofFn]
    rfl
  have heq : List.ofFn hCA.eigenvalues₀ =
      List.ofFn (fun i => c * hA.eigenvalues₀ i) := by
    rw [← hCA', hre, ← hsortmap, hA']
    exact hlist
  exact congrFun (List.ofFn_inj.mp heq) k

/-- Matrix norm control implies the ordered scalar compression estimate used
by `hcompress`, after the positive scalar is absorbed into the eigenvalues. -/
theorem hcompress_of_matrixNorm
    (T M : Matrix ι ι ℝ) (c : ℝ)
    (hT : Matrix.IsHermitian T) (hM : Matrix.IsHermitian M)
    (hCM : Matrix.IsHermitian (c • M)) (hc : 0 < c)
    (δ : ℝ) (hδ : 0 ≤ δ) (hnorm : ‖T - c • M‖ ≤ δ)
    (k : Fin (Fintype.card ι)) :
    |hT.eigenvalues₀ (Fin.rev k) - c * hM.eigenvalues₀ (Fin.rev k)| ≤ δ := by
  have h := matrix_eigenvalue_abs_le_of_opNorm T (c • M)
    hT hCM δ hδ hnorm (Fin.rev k)
  rw [eigenvalues₀_smul c M hM hCM hc (Fin.rev k)] at h
  exact h

end Weyl

/-- The rescaled total error in the last paragraph of Theorem 4.3 tends to
zero.  This is the explicit asymptotic input used by
`multiWellLimit_of_conclusion`. -/
theorem multiWellRescaledError_tendsto_zero
    (A : TwoWellConstants) (a : ι → X) :
    Filter.Tendsto
      (fun L : ℝ => L ^ A.kappa *
        (multiWellEpsilon A a L +
          2 * multiWellGamma A a L ^ 2 / A.gap))
      Filter.atTop (nhds 0) := by
  have hk : 0 < A.kappa := A.kappa_pos
  have hgap : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  set Cε : ℝ := A.c * A.C * A.phiMass ^ 2 * sigmaKappa a (A.kappa + 2)
  set Cγ : ℝ := A.c * 2 ^ A.kappa * A.volumeD * sigmaKappa a A.kappa
  have hε : Filter.Tendsto
      (fun L : ℝ => Cε * L ^ (-2 : ℝ)) Filter.atTop (nhds 0) :=
    by simpa [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : 0 < (2:ℝ))).const_mul Cε
  have hγ : Filter.Tendsto
      (fun L : ℝ => (2 * Cγ ^ 2 / A.gap) * L ^ (-A.kappa))
      Filter.atTop (nhds 0) :=
    by simpa [mul_zero] using
      (tendsto_rpow_neg_atTop hk).const_mul (2 * Cγ ^ 2 / A.gap)
  have hsum : Filter.Tendsto
      (fun L : ℝ => Cε * L ^ (-2 : ℝ) +
        (2 * Cγ ^ 2 / A.gap) * L ^ (-A.kappa))
      Filter.atTop (nhds 0) := by
    simpa [zero_add] using hε.add hγ
  refine Filter.Tendsto.congr'
    (f₁ := fun L : ℝ => Cε * L ^ (-2 : ℝ) +
      (2 * Cγ ^ 2 / A.gap) * L ^ (-A.kappa)) ?_ hsum
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with L hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hpowOne : L ^ A.kappa * L ^ (-A.kappa) = 1 := by
    rw [← Real.rpow_add hLpos, add_neg_cancel]
    exact Real.rpow_zero L
  have hεpow : L ^ A.kappa * L ^ (-A.kappa - 2) = L ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  have hγpow : L ^ A.kappa * (L ^ (-A.kappa)) ^ 2 = L ^ (-A.kappa) := by
    rw [pow_two, ← mul_assoc, hpowOne, one_mul]
  have hεeq : L ^ A.kappa *
      (A.c * A.C * A.phiMass ^ 2 * sigmaKappa a (A.kappa + 2) *
        L ^ (-A.kappa - 2)) = Cε * L ^ (-2 : ℝ) := by
    have h : L ^ A.kappa *
        (A.c * A.C * A.phiMass ^ 2 * sigmaKappa a (A.kappa + 2) *
          L ^ (-A.kappa - 2)) =
        (A.c * A.C * A.phiMass ^ 2 * sigmaKappa a (A.kappa + 2)) *
          (L ^ A.kappa * L ^ (-A.kappa - 2)) := by
      ring
    rw [h, hεpow]
  have hγeq : L ^ A.kappa *
      (2 * (A.c * 2 ^ A.kappa * A.volumeD * sigmaKappa a A.kappa *
        L ^ (-A.kappa)) ^ 2 / A.gap) =
      (2 * Cγ ^ 2 / A.gap) * L ^ (-A.kappa) := by
    have h : L ^ A.kappa *
        (2 * (A.c * 2 ^ A.kappa * A.volumeD * sigmaKappa a A.kappa *
          L ^ (-A.kappa)) ^ 2 / A.gap) =
        (2 * (A.c * 2 ^ A.kappa * A.volumeD * sigmaKappa a A.kappa) ^ 2 /
          A.gap) * (L ^ A.kappa * (L ^ (-A.kappa)) ^ 2) := by
      rw [mul_pow]
      field_simp [hgap.ne']
    rw [h, hγpow]
  show Cε * L ^ (-2 : ℝ) + (2 * Cγ ^ 2 / A.gap) * L ^ (-A.kappa) =
      L ^ A.kappa *
        (multiWellEpsilon A a L +
          2 * multiWellGamma A a L ^ 2 / A.gap)
  simp only [multiWellEpsilon, multiWellGamma]
  rw [mul_add, hεeq, hγeq]

/-- Fixed distinct sites satisfy the separation and smallness conditions in
equation `eq:multi-size-conditions` for all sufficiently large separations. -/
theorem multiWellCondition_eventually
    (A : TwoWellConstants) (a : ι → X)
    (hne : ∀ i j : ι, i ≠ j → a i ≠ a j) :
    ∀ᶠ L : ℝ in Filter.atTop,
      0 < L ∧
        (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) ∧
          multiWellGamma A a L ≤ A.gap / 4 := by
  have hgap : 0 < A.gap := by
    simpa [TwoWellConstants.gap] using A.hgap
  set sepBound : ℝ := ∑ p : ι × ι,
    if p.1 = p.2 then (0:ℝ) else 4 * A.R / ‖a p.1 - a p.2‖ with hsepBound
  have hterm_nonneg : ∀ p : ι × ι,
      0 ≤ if p.1 = p.2 then (0:ℝ)
        else 4 * A.R / ‖a p.1 - a p.2‖ := by
    intro p
    by_cases hp : p.1 = p.2
    · simp [hp]
    · rw [if_neg hp]
      exact div_nonneg
        (mul_nonneg (by norm_num) A.hR.le) (norm_nonneg _)
  have hsepBound_le : ∀ i j : ι, i ≠ j →
      4 * A.R / ‖a i - a j‖ ≤ sepBound := by
    intro i j hij
    rw [hsepBound]
    have hle := Finset.single_le_sum
      (fun p _ => hterm_nonneg p) (Finset.mem_univ (i, j))
    have hterm : (if (i, j).1 = (i, j).2 then (0:ℝ)
        else 4 * A.R / ‖a (i, j).1 - a (i, j).2‖) =
        4 * A.R / ‖a i - a j‖ := by
      simp [hij]
    rwa [hterm] at hle
  have hsmall : ∀ᶠ L : ℝ in Filter.atTop,
      multiWellGamma A a L < A.gap / 4 := by
    have hk : 0 < A.kappa := A.kappa_pos
    have hgap4 : 0 < A.gap / 4 := by positivity
    have hγ : Filter.Tendsto
        (fun L => multiWellGamma A a L) Filter.atTop (nhds 0) := by
      set Cγ : ℝ := A.c * 2 ^ A.kappa * A.volumeD * sigmaKappa a A.kappa
      have h : Filter.Tendsto
          (fun L => Cγ * L ^ (-A.kappa)) Filter.atTop (nhds (Cγ * 0)) :=
        (tendsto_rpow_neg_atTop hk).const_mul Cγ
      simpa [multiWellGamma, Cγ, mul_zero] using h
    exact hγ.eventually (Iio_mem_nhds hgap4)
  filter_upwards [Filter.eventually_ge_atTop (max 1 sepBound), hsmall]
    with L hL hsmallL
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by norm_num) ((le_max_left 1 sepBound).trans hL)
  have hsepBound : sepBound ≤ L :=
    (le_max_right 1 sepBound).trans hL
  refine ⟨hLpos, ?_, hsmallL.le⟩
  intro i j hij
  have hnorm : 0 < ‖a i - a j‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hne i j hij))
  have hle : 4 * A.R / ‖a i - a j‖ ≤ L :=
    (hsepBound_le i j hij).trans hsepBound
  exact (div_le_iff₀ hnorm).mp hle

/-- The quantitative conclusion of paper Theorem 4.3. -/
def multiWellConclusion
    (A : TwoWellConstants) (a : ι → X)
    (theta : Fin (Fintype.card ι) → ℝ) (lambda : ℝ → ℕ → ℝ) (L : ℝ) : Prop :=
  (∀ k : Fin (Fintype.card ι),
      |lambda L k.val - (A.mu1 + L ^ (-A.kappa) * theta k)| ≤
        multiWellEpsilon A a L +
          2 * multiWellGamma A a L ^ 2 / A.gap) ∧
    lambda L (Fintype.card ι - 1) ≤ A.mu1 + multiWellGamma A a L ∧
    A.mu1 + A.gap - multiWellGamma A a L ≤
      lambda L (Fintype.card ι) ∧
    A.gap - 2 * multiWellGamma A a L ≤
      lambda L (Fintype.card ι) - lambda L (Fintype.card ι - 1)

/-- The finite-dimensional comparison in the proof of Theorem 4.3.  The
isolated-cluster estimate is combined with the compression error for the
effective matrix by the triangle inequality; the cluster-edge estimates then
give the quantitative gap bound. -/
theorem multiWellConclusion_of_clusterCompression
    (A : TwoWellConstants) (a : ι → X)
    (theta : Fin (Fintype.card ι) → ℝ)
    (lambda : ℝ → ℕ → ℝ) (L : ℝ)
    (tau : Fin (Fintype.card ι) → ℝ)
    (hcluster : ∀ k : Fin (Fintype.card ι),
      -(2 * multiWellGamma A a L ^ 2 / A.gap) ≤
        lambda L k.val - (A.mu1 + tau k) ∧
        lambda L k.val - (A.mu1 + tau k) ≤ 0)
    (hcompress : ∀ k : Fin (Fintype.card ι),
      |tau k - L ^ (-A.kappa) * theta k| ≤ multiWellEpsilon A a L)
    (hupper : lambda L (Fintype.card ι - 1) ≤ A.mu1 + multiWellGamma A a L)
    (hnext : A.mu1 + A.gap - multiWellGamma A a L ≤
      lambda L (Fintype.card ι)) :
    multiWellConclusion A a theta lambda L := by
  have hgap : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  have hC : 0 ≤ 2 * multiWellGamma A a L ^ 2 / A.gap := by
    apply div_nonneg
    · exact mul_nonneg (by norm_num) (sq_nonneg _)
    · exact hgap.le
  refine ⟨?_, hupper, hnext, ?_⟩
  · intro k
    obtain ⟨hlo, hhi⟩ := hcluster k
    have hclusterAbs : |lambda L k.val - (A.mu1 + tau k)| ≤
        2 * multiWellGamma A a L ^ 2 / A.gap := by
      refine abs_le.mpr ⟨hlo, ?_⟩
      exact le_trans hhi hC
    have hsplit : lambda L k.val -
        (A.mu1 + L ^ (-A.kappa) * theta k) =
        (lambda L k.val - (A.mu1 + tau k)) +
          (tau k - L ^ (-A.kappa) * theta k) := by
      ring
    rw [hsplit]
    calc
      |(lambda L k.val - (A.mu1 + tau k)) +
          (tau k - L ^ (-A.kappa) * theta k)| ≤
          |lambda L k.val - (A.mu1 + tau k)| +
            |tau k - L ^ (-A.kappa) * theta k| :=
        abs_add_le _ _
      _ ≤ 2 * multiWellGamma A a L ^ 2 / A.gap +
          multiWellEpsilon A a L :=
        add_le_add hclusterAbs (hcompress k)
      _ = multiWellEpsilon A a L +
          2 * multiWellGamma A a L ^ 2 / A.gap := by
        ring
  · nlinarith [hupper, hnext]

/-- Matrix form of the cluster-compression comparison.  The `hcompress`
obligation is supplied by the ordered Weyl estimate instead of being an
independent scalar hypothesis. -/
theorem multiWellConclusion_of_clusterCompression_matrix
    (A : TwoWellConstants) (a : ι → X) (L : ℝ)
    (T M : Matrix ι ι ℝ) (hT : Matrix.IsHermitian T) (hM : Matrix.IsHermitian M)
    (hCM : Matrix.IsHermitian (L ^ (-A.kappa) • M))
    (hL : 0 < L) (hnorm : ‖T - L ^ (-A.kappa) • M‖ ≤ multiWellEpsilon A a L)
    (lambda : ℝ → ℕ → ℝ)
    (hcluster : ∀ k : Fin (Fintype.card ι),
      -(2 * multiWellGamma A a L ^ 2 / A.gap) ≤
        lambda L k.val - (A.mu1 + hT.eigenvalues₀ (Fin.rev k)) ∧
        lambda L k.val - (A.mu1 + hT.eigenvalues₀ (Fin.rev k)) ≤ 0)
    (hupper : lambda L (Fintype.card ι - 1) ≤ A.mu1 + multiWellGamma A a L)
    (hnext : A.mu1 + A.gap - multiWellGamma A a L ≤
      lambda L (Fintype.card ι)) :
    multiWellConclusion A a
      (fun k => hM.eigenvalues₀ (Fin.rev k)) lambda L := by
  have hc : 0 < L ^ (-A.kappa) := Real.rpow_pos_of_pos hL _
  apply multiWellConclusion_of_clusterCompression A a
    (fun k => hM.eigenvalues₀ (Fin.rev k)) lambda L
    (fun k => hT.eigenvalues₀ (Fin.rev k))
  · exact hcluster
  · intro k
    exact hcompress_of_matrixNorm T M (L ^ (-A.kappa)) hT hM hCM hc
      (multiWellEpsilon A a L) (multiWellEpsilon_nonneg A a L hL.le) hnorm k
  · exact hupper
  · exact hnext

/-- The limiting assertion in equation `eq:multi-limit`. -/
def multiWellLimit
    (A : TwoWellConstants) (a : ι → X)
    (theta : Fin (Fintype.card ι) → ℝ) (lambda : ℝ → ℕ → ℝ) : Prop :=
  ∀ k : Fin (Fintype.card ι),
    Filter.Tendsto
      (fun L : ℝ => L ^ A.kappa * (lambda L k.val - A.mu1))
      Filter.atTop (nhds (theta k))

/-- The full finite multi-well statement, with the pairwise-separation and
smallness conditions from equation `eq:multi-size-conditions`. -/
def multiWellStatement
    (A : TwoWellConstants) (a : ι → X)
    (theta : Fin (Fintype.card ι) → ℝ) (lambda : ℝ → ℕ → ℝ) : Prop :=
  (∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      multiWellConclusion A a theta lambda L) ∧
    multiWellLimit A a theta lambda

/-- The limiting assertion follows from the quantitative conclusion whenever
the rescaled total error tends to zero.  This is the algebraic implication
used in the last paragraph of paper Theorem 4.3. -/
theorem multiWellLimit_of_conclusion
    (A : TwoWellConstants) (a : ι → X)
    (theta : Fin (Fintype.card ι) → ℝ) (lambda : ℝ → ℕ → ℝ)
    (h : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      multiWellConclusion A a theta lambda L)
    (hcond : ∀ᶠ L : ℝ in Filter.atTop,
      0 < L ∧
        (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) ∧
          multiWellGamma A a L ≤ A.gap / 4)
    (herr : Filter.Tendsto
    (fun L : ℝ => L ^ A.kappa *
        (multiWellEpsilon A a L +
          2 * multiWellGamma A a L ^ 2 / A.gap))
      Filter.atTop (nhds 0)) :
    multiWellLimit A a theta lambda := by
  intro k
  have hk : ∀ᶠ L : ℝ in Filter.atTop,
      |lambda L k.val - (A.mu1 + L ^ (-A.kappa) * theta k)| ≤
        multiWellEpsilon A a L +
          2 * multiWellGamma A a L ^ 2 / A.gap := by
    filter_upwards [hcond] with L hL
    exact (h L hL.1 hL.2.1 hL.2.2).1 k
  have hbound : ∀ᶠ L : ℝ in Filter.atTop,
      |L ^ A.kappa * (lambda L k.val - A.mu1) - theta k| ≤
        L ^ A.kappa *
          (multiWellEpsilon A a L +
            2 * multiWellGamma A a L ^ 2 / A.gap) := by
    filter_upwards [hk, hcond] with L hL hpos
    have hcalc :
        L ^ A.kappa * (lambda L k.val - A.mu1) - theta k =
          L ^ A.kappa *
            (lambda L k.val - (A.mu1 + L ^ (-A.kappa) * theta k)) := by
      have hpow : L ^ A.kappa * L ^ (-A.kappa) = 1 := by
        rw [Real.rpow_neg hpos.1.le,
          mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos.1 _).ne']
      have h1 :
          L ^ A.kappa *
              (lambda L k.val - (A.mu1 + L ^ (-A.kappa) * theta k)) =
            L ^ A.kappa * (lambda L k.val - A.mu1) - theta k := by
        rw [mul_sub, mul_add, ← mul_assoc, hpow, one_mul]
        ring
      exact h1.symm
    rw [hcalc, abs_mul, abs_of_nonneg (Real.rpow_nonneg hpos.1.le _)]
    exact mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hpos.1.le _)
  refine tendsto_sub_nhds_zero_iff.mp ?_
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun L => norm_nonneg _)
    (by
      filter_upwards [hbound] with L hL
      simpa [Real.norm_eq_abs] using hL)
    herr

/-- The finite multi-well capstone assembled from the isolated-cluster
comparison and the matrix compression estimate.  The compression matrix `T L`
is the finite-dimensional block compression from Lemma 4.3; its operator-norm
error is converted to the ordered eigenvalue comparison by the Weyl bridge. -/
theorem FinalTheoremMultiWell
    (A : TwoWellConstants) (a : ι → X)
    (lambda : ℝ → ℕ → ℝ)
    (T : ℝ → Matrix ι ι ℝ)
    (hne : ∀ i j : ι, i ≠ j → a i ≠ a j)
    (hT : ∀ L : ℝ, Matrix.IsHermitian (T L))
    (hnorm : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      ‖T L - L ^ (-A.kappa) •
        effectiveInteractionMatrix a A.c A.phiMass A.kappa‖ ≤
        multiWellEpsilon A a L)
    (hcluster : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      ∀ k : Fin (Fintype.card ι),
        -(2 * multiWellGamma A a L ^ 2 / A.gap) ≤
          lambda L k.val -
            (A.mu1 + (hT L).eigenvalues₀ (Fin.rev k)) ∧
          lambda L k.val -
            (A.mu1 + (hT L).eigenvalues₀ (Fin.rev k)) ≤ 0)
    (hupper : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      lambda L (Fintype.card ι - 1) ≤ A.mu1 + multiWellGamma A a L)
    (hnext : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      A.mu1 + A.gap - multiWellGamma A a L ≤
        lambda L (Fintype.card ι)) :
    multiWellStatement A a
      (fun k => (effectiveInteractionMatrix_isHermitian
        a A.c A.phiMass A.kappa).eigenvalues₀ (Fin.rev k)) lambda := by
  have hcond := multiWellCondition_eventually A a hne
  have hM : Matrix.IsHermitian
      (effectiveInteractionMatrix a A.c A.phiMass A.kappa) :=
    effectiveInteractionMatrix_isHermitian a A.c A.phiMass A.kappa
  have hpoint : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      multiWellConclusion A a
        (fun k => (effectiveInteractionMatrix_isHermitian
          a A.c A.phiMass A.kappa).eigenvalues₀ (Fin.rev k)) lambda L := by
    intro L hL hsep hsmall
    have hCM : Matrix.IsHermitian
        (L ^ (-A.kappa) • effectiveInteractionMatrix a A.c A.phiMass A.kappa) :=
      (effectiveInteractionMatrix_isHermitian a A.c A.phiMass A.kappa).smul
        (IsSelfAdjoint.all _)
    have hmatrix : multiWellConclusion A a
        (fun k => (effectiveInteractionMatrix_isHermitian
          a A.c A.phiMass A.kappa).eigenvalues₀ (Fin.rev k)) lambda L :=
      multiWellConclusion_of_clusterCompression_matrix A a L
        (T L) (effectiveInteractionMatrix a A.c A.phiMass A.kappa)
        (hT L) (effectiveInteractionMatrix_isHermitian a A.c A.phiMass A.kappa)
        hCM hL (hnorm L hL hsep hsmall) lambda
        (hcluster L hL hsep hsmall) (hupper L hL hsep hsmall)
        (hnext L hL hsep hsmall)
    simpa [effectiveInteractionTheta] using hmatrix
  exact ⟨hpoint,
    multiWellLimit_of_conclusion A a
      (fun k => (effectiveInteractionMatrix_isHermitian
        a A.c A.phiMass A.kappa).eigenvalues₀ (Fin.rev k)) lambda hpoint hcond
      (multiWellRescaledError_tendsto_zero A a)⟩

/-- The capstone specialized to the exact ground-state compression matrix
`T_L` from equation `eq:exact-compression`. -/
theorem FinalTheoremMultiWell_exactCompression
    [MeasurableSpace X] [Module ℝ X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.SFinite mu]
    (A : TwoWellConstants) (a : ι → X) (u : X → ℝ)
    (lambda : ℝ → ℕ → ℝ)
    (hne : ∀ i j : ι, i ≠ j → a i ≠ a j)
    (hnorm : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      ‖multiWellCompressionMatrix mu A.kappa A.c u a L -
        L ^ (-A.kappa) • effectiveInteractionMatrix a A.c A.phiMass A.kappa‖ ≤
        multiWellEpsilon A a L)
    (hcluster : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      ∀ k : Fin (Fintype.card ι),
        -(2 * multiWellGamma A a L ^ 2 / A.gap) ≤
          lambda L k.val - (A.mu1 +
            (multiWellCompressionMatrix_isHermitian
              mu A.kappa A.c u a L).eigenvalues₀ (Fin.rev k)) ∧
          lambda L k.val - (A.mu1 +
            (multiWellCompressionMatrix_isHermitian
              mu A.kappa A.c u a L).eigenvalues₀ (Fin.rev k)) ≤ 0)
    (hupper : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      lambda L (Fintype.card ι - 1) ≤ A.mu1 + multiWellGamma A a L)
    (hnext : ∀ L : ℝ,
      0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      A.mu1 + A.gap - multiWellGamma A a L ≤
        lambda L (Fintype.card ι)) :
    multiWellStatement A a
      (fun k => (effectiveInteractionMatrix_isHermitian
        a A.c A.phiMass A.kappa).eigenvalues₀ (Fin.rev k)) lambda := by
  exact FinalTheoremMultiWell A a lambda
    (fun L => multiWellCompressionMatrix mu A.kappa A.c u a L) hne
    (fun L => multiWellCompressionMatrix_isHermitian mu A.kappa A.c u a L)
    hnorm hcluster hupper hnext

end Tunneling
