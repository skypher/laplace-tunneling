import Tunneling.Euclid.FormDomain
import Tunneling.MultiWell

/-
# The compression error on `ℝ^d` (paper Lemma 4.3)

The Taylor estimate `eq:multi-taylor` holds for `|x|, |y| ≤ R`.  On `ℝ^d` the
ground state is supported in `D ⊆ B_R(0)`, so the pointwise hypothesis
`∀ x : X, ‖x‖ ≤ R` of `multiWellCompressionMatrix_entry_error` is replaced by
the support condition `u x ≠ 0 → ‖x‖ ≤ R`.
-/

namespace Tunneling

open MeasureTheory

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem integrablePairMulBound (A : TwoWellConstants) (u : Eucl d → ℝ)
    (_hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ A.R)
    (hint : Integrable u (volume : Measure (Eucl d)))
    (f : Eucl d × Eucl d → ℝ)
    (hf : AEStronglyMeasurable f ((volume : Measure (Eucl d)).prod volume))
    (B : ℝ) (_hB : 0 ≤ B)
    (hbound : ∀ x y, u x ≠ 0 → u y ≠ 0 → ‖f (x,y)‖ ≤ B) :
    Integrable (fun z : Eucl d × Eucl d => u z.1 * u z.2 * f z)
      ((volume : Measure (Eucl d)).prod volume) := by
  have hp : Integrable (fun z : Eucl d × Eucl d => u z.1 * u z.2)
      ((volume : Measure (Eucl d)).prod volume) := hint.mul_prod hint
  refine (hp.norm.const_mul B).mono' (hp.aestronglyMeasurable.mul hf) ?_
  filter_upwards with z
  rcases z with ⟨x,y⟩
  by_cases hx : u x = 0
  · simp [hx]
  by_cases hy : u y = 0
  · simp [hy]
  have hb := hbound x y hx hy
  calc
    ‖u x * u y * f (x,y)‖ = ‖u x * u y‖ * ‖f (x,y)‖ := by rw [norm_mul]
    _ ≤ ‖u x * u y‖ * B := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = B * ‖u x * u y‖ := by ring

private theorem euclidCrossKernel_measurable (kappa : ℝ) (center : Eucl d) :
    Measurable (fun z : Eucl d × Eucl d => multiWellCrossKernel kappa center z.1 z.2) := by
  change Measurable (fun z : Eucl d × Eucl d => ‖center + z.1 - z.2‖ ^ (-kappa))
  have hc : Continuous (fun z : Eucl d × Eucl d => center + z.1 - z.2) :=
    (continuous_const.add continuous_fst).sub continuous_snd
  exact ((continuous_norm.comp hc).measurable).pow_const _

private theorem euclidTaylorRemainder_measurable (kappa : ℝ) (center : Eucl d) :
    Measurable (fun z : Eucl d × Eucl d => multiWellTaylorRemainder kappa center z.1 z.2) := by
  unfold multiWellTaylorRemainder
  have hk := euclidCrossKernel_measurable kappa center
  have hl : Measurable (fun z : Eucl d × Eucl d => inner ℝ center (z.1-z.2)) := by fun_prop
  exact hk.sub measurable_const |>.add (measurable_const.mul hl)

private theorem euclidSeparatedDistanceBounds (A : TwoWellConstants) (dvec x y : Eucl d)
    (L : ℝ) (hL : 0 < L) (hsep : 4 * A.R ≤ L * ‖dvec‖)
    (hx : ‖x‖ ≤ A.R) (hy : ‖y‖ ≤ A.R) :
    2 * A.R ≤ ‖(L : ℝ) • dvec + x - y‖ ∧
      ‖(L : ℝ) • dvec + x - y‖ ≤ L * ‖dvec‖ + 2 * A.R := by
  have hcenter : ‖(L : ℝ) • dvec‖ = L * ‖dvec‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have hxy : ‖x - y‖ ≤ 2 * A.R := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ A.R + A.R := add_le_add hx hy
      _ = 2 * A.R := by ring
  have hvec : (L : ℝ) • dvec + x - y = (L : ℝ) • dvec + (x-y) := by abel
  constructor
  · rw [hvec]
    have htri : ‖(L : ℝ) • dvec‖ ≤
        ‖(L : ℝ) • dvec + (x-y)‖ + ‖x-y‖ := by
      calc
        ‖(L : ℝ) • dvec‖ = ‖((L : ℝ) • dvec + (x-y)) - (x-y)‖ := by congr 1 <;> abel
        _ ≤ _ := norm_sub_le _ _
    rw [hcenter] at htri
    linarith
  · rw [hvec]
    calc
      ‖(L : ℝ) • dvec + (x-y)‖ ≤
          ‖(L : ℝ) • dvec‖ + ‖x-y‖ := norm_add_le _ _
      _ ≤ ‖(L : ℝ) • dvec‖ + 2 * A.R :=
        add_le_add (le_refl _) hxy
      _ = L * ‖dvec‖ + 2 * A.R := by rw [hcenter]

private theorem kernelCrossPairing_taylor_support
    (A : TwoWellConstants) (u : Eucl d → ℝ) (center : Eucl d) (m r : ℝ)
    (hprodInt : Integrable (fun z : Eucl d × Eucl d => u z.1 * u z.2)
      ((volume : Measure (Eucl d)).prod volume))
    (hlinInt : Integrable (fun z : Eucl d × Eucl d =>
      u z.1 * u z.2 * inner ℝ center (z.1-z.2))
      ((volume : Measure (Eucl d)).prod volume))
    (hRInt : Integrable (fun z : Eucl d × Eucl d => u z.1 * u z.2 *
      multiWellTaylorRemainder A.kappa center z.1 z.2)
      ((volume : Measure (Eucl d)).prod volume))
    (hmass : ∫ x, u x = m) (hnonneg : ∀ x, 0 ≤ u x) (hr : 0 ≤ r)
    (hRbound : ∀ x y, u x ≠ 0 → u y ≠ 0 →
      |multiWellTaylorRemainder A.kappa center x y| ≤ r) :
    |kernelCrossPairing (multiWellCrossKernel A.kappa center)
        (volume : Measure (Eucl d)) u u - m * m * ‖center‖ ^ (-A.kappa)| ≤ r * m * m := by
  let R' : Eucl d × Eucl d → ℝ := fun z =>
    if u z.1 ≠ 0 ∧ u z.2 ≠ 0 then
      multiWellTaylorRemainder A.kappa center z.1 z.2 else 0
  let T' : Eucl d → Eucl d → ℝ := fun x y =>
    ‖center‖ ^ (-A.kappa) +
      (-A.kappa * ‖center‖ ^ (-A.kappa - 2)) * inner ℝ center (x-y) + R' (x,y)
  have hRBound' : ∀ x y, |R' (x,y)| ≤ r := by
    intro x y
    by_cases hx : u x ≠ 0 <;> by_cases hy : u y ≠ 0
    · simp [R', hx, hy, hRbound x y hx hy]
    · simp [R', hx, hy, hr]
    · simp [R', hx, hy, hr]
    · simp [R', hx, hy, hr]
  have hRInt' : Integrable (fun z : Eucl d × Eucl d => u z.1 * u z.2 * R' z)
      ((volume : Measure (Eucl d)).prod volume) := by
    apply hRInt.congr
    filter_upwards with z
    rcases z with ⟨x,y⟩
    by_cases hx : u x = 0
    · simp [R', hx]
    by_cases hy : u y = 0
    · simp [R', hy]
    simp [R', hx, hy]
  have hdecomp : ∀ x y, T' x y =
      ‖center‖ ^ (-A.kappa) +
        (-A.kappa * ‖center‖ ^ (-A.kappa - 2)) * inner ℝ center (x-y) + R' (x,y) := by
    intro x y
    rfl
  have hzero := linear_sub_integral_zero (volume : Measure (Eucl d)) center u
  have hmassTaylor := interactionMass_taylor_remainder_prod
    (volume : Measure (Eucl d)) u T'
    (fun z => inner ℝ center (z.1-z.2)) R' m (‖center‖ ^ (-A.kappa))
    (-A.kappa * ‖center‖ ^ (-A.kappa - 2)) r
    hprodInt hlinInt hRInt' hmass hzero hnonneg hr hdecomp hRBound'
  have hteq : ∀ z : Eucl d × Eucl d,
      u z.1 * u z.2 * multiWellCrossKernel A.kappa center z.1 z.2 =
      u z.1 * u z.2 * T' z.1 z.2 := by
    intro z
    rcases z with ⟨x,y⟩
    by_cases hx : u x = 0
    · simp [T', hx]
    by_cases hy : u y = 0
    · simp [T', hy]
    simp [T', R', hx, hy, multiWellCrossKernel_taylor_decomp]
  have hIntEq : (∫ z : Eucl d × Eucl d,
      u z.1 * u z.2 * multiWellCrossKernel A.kappa center z.1 z.2
        ∂((volume : Measure (Eucl d)).prod volume)) =
      ∫ z : Eucl d × Eucl d, u z.1 * u z.2 * T' z.1 z.2
        ∂((volume : Measure (Eucl d)).prod volume) := by
    apply MeasureTheory.integral_congr_ae
    exact MeasureTheory.ae_of_all _ hteq
  rw [show kernelCrossPairing (multiWellCrossKernel A.kappa center)
      (volume : Measure (Eucl d)) u u =
      ∫ z : Eucl d × Eucl d, u z.1 * u z.2 * multiWellCrossKernel A.kappa center z.1 z.2
        ∂((volume : Measure (Eucl d)).prod volume) by rfl,
    hIntEq]
  exact hmassTaylor

private theorem compression_entry_taylor_support (A : TwoWellConstants)
    (a : ι → Eucl d) (u : Eucl d → ℝ) (L : ℝ) (i j : ι)
    (hL : 0 < L) (hij : i ≠ j)
    (hsep : 4 * A.R ≤ L * ‖a i - a j‖)
    (hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ A.R)
    (hint : Integrable u (volume : Measure (Eucl d)))
    (hmass : ∫ x, u x = A.phiMass) (hnonneg : ∀ x, 0 ≤ u x) :
    |multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L i j -
      L ^ (-A.kappa) * effectiveInteractionMatrix a A.c A.phiMass A.kappa i j| ≤
      A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) *
        ‖a i - a j‖ ^ (-A.kappa - 2) := by
  set dvec : Eucl d := a i - a j
  set center : Eucl d := (L : ℝ) • dvec
  have hdpos : 0 < ‖dvec‖ := by
    have h4R : (0:ℝ) < 4 * A.R := mul_pos (by norm_num) A.hR
    have hprod : (0:ℝ) < L * ‖dvec‖ := lt_of_lt_of_le h4R hsep
    exact pos_of_mul_pos_left (by simpa [mul_comm] using hprod) hL.le
  have hcenterScale : ‖center‖ ^ (-A.kappa) =
      L ^ (-A.kappa) * ‖dvec‖ ^ (-A.kappa) := by
    show ‖(L : ℝ) • dvec‖ ^ (-A.kappa) =
      L ^ (-A.kappa) * ‖dvec‖ ^ (-A.kappa)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    exact Real.mul_rpow hL.le (norm_nonneg _)
  have hprodInt : Integrable (fun z : Eucl d × Eucl d => u z.1 * u z.2)
      ((volume : Measure (Eucl d)).prod volume) := hint.mul_prod hint
  let hlinB : ℝ := L * ‖dvec‖ * (2 * A.R)
  have hlinB_nonneg : 0 ≤ hlinB := by
    dsimp [hlinB]
    exact mul_nonneg (mul_nonneg hL.le (norm_nonneg _))
      (mul_nonneg (by norm_num) A.hR.le)
  have hlinBound : ∀ x y, u x ≠ 0 → u y ≠ 0 →
      ‖inner ℝ center (x-y)‖ ≤ hlinB := by
    intro x y hx hy
    have hx' := hsupp x hx
    have hy' := hsupp y hy
    have hxy : ‖x-y‖ ≤ 2*A.R := by
      calc
        ‖x-y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
        _ ≤ A.R + A.R := add_le_add hx' hy'
        _ = 2*A.R := by ring
    have hc : ‖center‖ = L * ‖dvec‖ := by
      simp [center, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    have hi := abs_real_inner_le_norm center (x-y)
    rw [Real.norm_eq_abs]
    calc
      |inner ℝ center (x-y)| ≤ ‖center‖ * ‖x-y‖ := hi
      _ ≤ hlinB := by rw [hc]; exact mul_le_mul_of_nonneg_left hxy (by positivity)
  have hRbound : ∀ x y, u x ≠ 0 → u y ≠ 0 →
      |multiWellTaylorRemainder A.kappa center x y| ≤
        A.C * L ^ (-A.kappa - 2) * ‖dvec‖ ^ (-A.kappa - 2) := by
    intro x y hx hy
    exact multiWellTaylorRemainder_abs_le A dvec x y L hL hsep
      (hsupp x hx) (hsupp y hy)
  have hr : 0 ≤ A.C * L ^ (-A.kappa - 2) * ‖dvec‖ ^ (-A.kappa - 2) := by
    have hlp : 0 ≤ L ^ (-A.kappa - 2) := Real.rpow_nonneg hL.le _
    have hdp : 0 ≤ ‖dvec‖ ^ (-A.kappa - 2) :=
      Real.rpow_nonneg (norm_nonneg _) _
    exact mul_nonneg (mul_nonneg A.hC.le hlp) hdp
  have hlinInt := integrablePairMulBound A u hsupp hint
    (fun z : Eucl d × Eucl d => inner ℝ center (z.1-z.2))
    (by fun_prop) hlinB hlinB_nonneg hlinBound
  have hRInt := integrablePairMulBound A u hsupp hint
    (fun z : Eucl d × Eucl d => multiWellTaylorRemainder A.kappa center z.1 z.2)
    (euclidTaylorRemainder_measurable A.kappa center).aestronglyMeasurable
    (A.C * L ^ (-A.kappa - 2) * ‖dvec‖ ^ (-A.kappa - 2)) hr hRbound
  have hpair := kernelCrossPairing_taylor_support A u center A.phiMass
    (A.C * L ^ (-A.kappa - 2) * ‖dvec‖ ^ (-A.kappa - 2))
    hprodInt hlinInt hRInt hmass hnonneg hr hRbound
  have hcenterPair :
      |kernelCrossPairing (multiWellCrossKernel A.kappa center)
        (volume : Measure (Eucl d)) u u -
        A.phiMass ^ 2 * (L ^ (-A.kappa) * ‖dvec‖ ^ (-A.kappa))| ≤
        A.C * L ^ (-A.kappa - 2) * ‖dvec‖ ^ (-A.kappa - 2) *
          A.phiMass ^ 2 := by
    have hpair' :
        |kernelCrossPairing (multiWellCrossKernel A.kappa center)
          (volume : Measure (Eucl d)) u u - A.phiMass ^ 2 * ‖center‖ ^ (-A.kappa)| ≤
        A.C * L ^ (-A.kappa - 2) * ‖dvec‖ ^ (-A.kappa - 2) *
          A.phiMass ^ 2 := by
      simpa only [pow_two, mul_assoc] using hpair
    rw [hcenterScale] at hpair'
    exact hpair'
  have hentry : multiWellCompressionMatrix (volume : Measure (Eucl d))
      A.kappa A.c u a L i j =
      -A.c * kernelCrossPairing (multiWellCrossKernel A.kappa center)
        (volume : Measure (Eucl d)) u u := by
    rw [multiWellCompressionMatrix_apply, if_neg hij]
  have heff : L ^ (-A.kappa) * effectiveInteractionMatrix a A.c A.phiMass A.kappa i j =
      -A.c * (A.phiMass ^ 2 * (L ^ (-A.kappa) * ‖dvec‖ ^ (-A.kappa))) := by
    rw [effectiveInteractionMatrix_apply, if_neg hij]
    show L ^ (-A.kappa) * (-A.c * A.phiMass ^ 2 * ‖dvec‖ ^ (-A.kappa)) = _
    ring
  have hdiff :
      multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L i j -
        L ^ (-A.kappa) * effectiveInteractionMatrix a A.c A.phiMass A.kappa i j =
      -A.c * (kernelCrossPairing (multiWellCrossKernel A.kappa center)
        (volume : Measure (Eucl d)) u u -
        A.phiMass ^ 2 * (L ^ (-A.kappa) * ‖dvec‖ ^ (-A.kappa))) := by
    rw [hentry, heff]
    ring
  rw [hdiff, abs_mul, abs_neg, abs_of_nonneg A.hc.le]
  have hmul := mul_le_mul_of_nonneg_left hcenterPair A.hc.le
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Entrywise compression error of Lemma 4.3 on `ℝ^d`. -/
theorem compression_entry_error_euclid (A : TwoWellConstants) (a : ι → Eucl d)
    (u : Eucl d → ℝ) (L : ℝ) (i j : ι) (hL : 0 < L)
    (hsep : ∀ p q : ι, p ≠ q → 4 * A.R ≤ L * ‖a p - a q‖)
    (hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ A.R)
    (hint : Integrable u (volume : Measure (Eucl d)))
    (hmass : ∫ x, u x = A.phiMass) (hnonneg : ∀ x, 0 ≤ u x) :
    |multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L i j -
      L ^ (-A.kappa) * effectiveInteractionMatrix a A.c A.phiMass A.kappa i j| ≤
      (if i = j then 0
        else A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) *
          ‖a i - a j‖ ^ (-A.kappa - 2)) := by
  by_cases hij : i = j
  · subst j
    simp [multiWellCompressionMatrix, effectiveInteractionMatrix]
  · rw [if_neg hij]
    exact compression_entry_taylor_support A a u L i j hL hij
      (hsep i j hij) hsupp hint hmass hnonneg

/-- Operator-norm form of Lemma 4.3 on `ℝ^d`:
`‖T_L - L^{-κ} M_a‖ ≤ ε_L`. -/
theorem compression_norm_le_euclid (A : TwoWellConstants) (a : ι → Eucl d)
    (u : Eucl d → ℝ) (L : ℝ) (hL : 0 < L)
    (hsep : ∀ p q : ι, p ≠ q → 4 * A.R ≤ L * ‖a p - a q‖)
    (hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ A.R)
    (hint : Integrable u (volume : Measure (Eucl d)))
    (hmass : ∫ x, u x = A.phiMass) (hnonneg : ∀ x, 0 ≤ u x) :
    ‖multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L -
      L ^ (-A.kappa) • effectiveInteractionMatrix a A.c A.phiMass A.kappa‖ ≤
      multiWellEpsilon A a L := by
  classical
  set E : ι → ι → ℝ := fun p r =>
    if p = r then (0:ℝ)
    else A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) *
      ‖a p - a r‖ ^ (-A.kappa - 2)
  have hentry : ∀ p r,
      |multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L p r -
        L ^ (-A.kappa) *
          effectiveInteractionMatrix a A.c A.phiMass A.kappa p r| ≤ E p r := by
    intro p r
    exact compression_entry_error_euclid A a u L p r hL hsep hsupp hint hmass hnonneg
  have hrow : ∀ p, ∑ r, E p r ≤ multiWellEpsilon A a L := by
    intro p
    exact multiWellCompressionMatrix_error_row A a L p hL.le
  have hsymm :
      (multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L -
        L ^ (-A.kappa) •
          effectiveInteractionMatrix a A.c A.phiMass A.kappa).IsSymm :=
    (multiWellCompressionMatrix_isSymm (volume : Measure (Eucl d))
      A.kappa A.c u a L).sub
      ((effectiveInteractionMatrix_isSymm a A.c A.phiMass A.kappa).smul _)
  refine entrywise_matrix_norm_le
    (multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L)
    (L ^ (-A.kappa) •
      effectiveInteractionMatrix a A.c A.phiMass A.kappa)
    E (multiWellEpsilon A a L) hsymm ?_ hrow
    (multiWellEpsilon_nonneg A a L hL.le)
  intro p r
  simpa [Matrix.smul_apply, smul_eq_mul] using hentry p r

/-- The two-sided kernel bound gives `-t_{ij}(L) ≥ c m₁² (L|a_i - a_j| + 2R)^{-κ}`
for `i ≠ j` (used for the simplicity statement of paper Theorem 3.3). -/
theorem compression_entry_le_euclid (A : TwoWellConstants) (a : ι → Eucl d)
    (u : Eucl d → ℝ) (L : ℝ) (i j : ι) (hij : i ≠ j) (hL : 0 < L)
    (hsep : ∀ p q : ι, p ≠ q → 4 * A.R ≤ L * ‖a p - a q‖)
    (hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ A.R)
    (hint : Integrable u (volume : Measure (Eucl d)))
    (hmass : ∫ x, u x = A.phiMass) (hnonneg : ∀ x, 0 ≤ u x) :
    multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c u a L i j ≤
      -(A.c * A.phiMass ^ 2 * (L * ‖a i - a j‖ + 2 * A.R) ^ (-A.kappa)) := by
  set dvec : Eucl d := a i - a j
  set center : Eucl d := (L : ℝ) • dvec
  let lower : ℝ := (L * ‖dvec‖ + 2 * A.R) ^ (-A.kappa)
  let B : ℝ := (2 * A.R) ^ (-A.kappa)
  have hprodInt : Integrable (fun z : Eucl d × Eucl d => u z.1 * u z.2)
      ((volume : Measure (Eucl d)).prod volume) := hint.mul_prod hint
  have hκneg : -A.kappa ≤ 0 := by linarith [A.kappa_pos]
  have htwoR : 0 < 2 * A.R := mul_pos (by norm_num) A.hR
  have htwoR_nonneg : 0 ≤ 2 * A.R := htwoR.le
  have hB : 0 ≤ B := by
    simpa [B] using Real.rpow_nonneg htwoR_nonneg (-A.kappa)
  have hkernelBound : ∀ x y, u x ≠ 0 → u y ≠ 0 →
      ‖multiWellCrossKernel A.kappa center x y‖ ≤ B := by
    intro x y hx hy
    have hdist := euclidSeparatedDistanceBounds A dvec x y L hL
      (hsep i j hij) (hsupp x hx) (hsupp y hy)
    have hpow : ‖(L : ℝ) • dvec + x - y‖ ^ (-A.kappa) ≤ B := by
      simpa [B] using Real.rpow_le_rpow_of_nonpos htwoR hdist.1 hκneg
    have hkernonneg : 0 ≤ multiWellCrossKernel A.kappa center x y :=
      Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.norm_eq_abs, abs_of_nonneg hkernonneg]
    simpa [multiWellCrossKernel, center] using hpow
  have hkernelInt := integrablePairMulBound A u hsupp hint
    (fun z : Eucl d × Eucl d => multiWellCrossKernel A.kappa center z.1 z.2)
    (euclidCrossKernel_measurable A.kappa center).aestronglyMeasurable
    B hB hkernelBound
  have hlowInt : Integrable (fun z : Eucl d × Eucl d =>
      lower * (u z.1 * u z.2)) ((volume : Measure (Eucl d)).prod volume) := by
    have h := hprodInt.const_mul lower
    apply h.congr
    filter_upwards with z
    ring
  have hprodMass : ∫ z : Eucl d × Eucl d, u z.1 * u z.2
      ∂((volume : Measure (Eucl d)).prod volume) = A.phiMass * A.phiMass := by
    rw [MeasureTheory.integral_prod_mul u u, hmass]
  have hlowIntegral : ∫ z : Eucl d × Eucl d, lower * (u z.1 * u z.2)
      ∂((volume : Measure (Eucl d)).prod volume) = lower * A.phiMass * A.phiMass := by
    rw [MeasureTheory.integral_const_mul, hprodMass]
    ring
  have hkernelLower : ∀ z : Eucl d × Eucl d,
      lower * (u z.1 * u z.2) ≤
        u z.1 * u z.2 * multiWellCrossKernel A.kappa center z.1 z.2 := by
    intro z
    rcases z with ⟨x,y⟩
    by_cases hx : u x = 0
    · simp [hx]
    by_cases hy : u y = 0
    · simp [hy]
    have hdist := euclidSeparatedDistanceBounds A dvec x y L hL
      (hsep i j hij) (hsupp x hx) (hsupp y hy)
    have hdistpos : 0 < ‖(L : ℝ) • dvec + x - y‖ :=
      lt_of_lt_of_le htwoR hdist.1
    have hpow : lower ≤ multiWellCrossKernel A.kappa center x y := by
      have hp := Real.rpow_le_rpow_of_nonpos hdistpos
        (by simpa [center] using hdist.2) hκneg
      simpa [lower, multiWellCrossKernel, center] using hp
    have hu : 0 ≤ u x * u y := mul_nonneg (hnonneg x) (hnonneg y)
    calc
      lower * (u x * u y) ≤
          multiWellCrossKernel A.kappa center x y * (u x * u y) :=
        mul_le_mul_of_nonneg_right hpow hu
      _ = u x * u y * multiWellCrossKernel A.kappa center x y := by ring
  have hpairLower : lower * A.phiMass ^ 2 ≤
      kernelCrossPairing (multiWellCrossKernel A.kappa center)
        (volume : Measure (Eucl d)) u u := by
    calc
      lower * A.phiMass ^ 2 =
          ∫ z : Eucl d × Eucl d, lower * (u z.1 * u z.2)
            ∂((volume : Measure (Eucl d)).prod volume) := by
        rw [hlowIntegral]
        ring
      _ ≤ ∫ z : Eucl d × Eucl d,
          u z.1 * u z.2 * multiWellCrossKernel A.kappa center z.1 z.2
          ∂((volume : Measure (Eucl d)).prod volume) :=
        MeasureTheory.integral_mono_ae hlowInt hkernelInt
          (MeasureTheory.ae_of_all _ hkernelLower)
      _ = kernelCrossPairing (multiWellCrossKernel A.kappa center)
          (volume : Measure (Eucl d)) u u := by rfl
  have hentry : multiWellCompressionMatrix (volume : Measure (Eucl d))
      A.kappa A.c u a L i j =
      -A.c * kernelCrossPairing (multiWellCrossKernel A.kappa center)
        (volume : Measure (Eucl d)) u u := by
    rw [multiWellCompressionMatrix_apply, if_neg hij]
  rw [hentry]
  have hmul := mul_le_mul_of_nonpos_left hpairLower
    (neg_nonpos.mpr A.hc.le)
  calc
    -A.c * kernelCrossPairing (multiWellCrossKernel A.kappa center)
        (volume : Measure (Eucl d)) u u
        ≤ -A.c * (lower * A.phiMass ^ 2) := hmul
    _ = -(A.c * A.phiMass ^ 2 * lower) := by ring
    _ = -(A.c * A.phiMass ^ 2 *
          (L * ‖a i - a j‖ + 2 * A.R) ^ (-A.kappa)) := by
      simp [lower, dvec]

end Tunneling
