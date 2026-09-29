- `formQ_eq`: proved.
- Helpers added for translated support, geometric separation, finite-support integrability, kernel integrability, translation of the pairing, and the off diagonal polar identity.
- Type-checked the complete file through `lean --stdin`; no errors or sorry warnings. Lean emitted only non-fatal linter notices.

===BEGIN FILE Tunneling/Euclid/DecompForm.lean===
import Tunneling.Euclid.Decomp
/-!
# The exact block identity of paper Lemma 4.1
-/
namespace Tunneling
open MeasureTheory
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace WellGeometry
variable (G : WellGeometry d ι)
private theorem formQ_phi (c : ℝ) (φ : formDomain G.κ G.D) (j : ι) :
    formQ c G.κ G.Ω (G.Φ φ j) = formQ c G.κ G.D φ := by
  change formQ c G.κ G.Ω
      (⟨translateL2 (G.L • G.a j) (φ : L2 d), G.translate_mem_Ω φ j⟩) = _
  rw [formQ_apply, formQ_apply]
  congr 1
  exact gagliardoSeminormSq_translateL2 G.κ (G.L • G.a j) (φ : L2 d)
private theorem sumPhi_eq (ψ : formDomain G.κ G.Ω) :
    ψ = ∑ j, G.Φ (G.wellMap j ψ) j := by
  classical
  let v : formDomain G.κ G.Ω := ∑ j, G.Φ (G.wellMap j ψ) j
  have hpieces (i : ι) :
      G.pieceL2 i (v : L2 d) = G.pieceL2 i (ψ : L2 d) := by
    dsimp [v]
    rw [Submodule.coe_sum, map_sum]
    simp only [G.pieceL2_Φ]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji.symm]
    · simp
  let e : formDomain G.κ G.Ω := ψ - v
  have hpiece0 (i : ι) : G.pieceL2 i (e : L2 d) = 0 := by
    dsimp [e]
    rw [map_sub, hpieces]
    simp
  have heinner : inner ℝ (e : L2 d) (e : L2 d) = 0 := by
    rw [G.inner_eq_sum e e]
    simp [hpiece0]
  have he0 : (e : L2 d) = 0 := inner_self_eq_zero.mp heinner
  have he0' : e = 0 := Subtype.ext he0
  dsimp [e] at he0'
  exact sub_eq_zero.mp he0'
private theorem polar_sum_right {α : Type*} [DecidableEq α] {M : Type*}
    [AddCommGroup M] [Module ℝ M] (q : QuadraticMap ℝ M ℝ) (x : M) (f : α → M)
    (s : Finset α) :
    QuadraticMap.polar q x (∑ i ∈ s, f i) =
      ∑ i ∈ s, QuadraticMap.polar q x (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, QuadraticMap.polar_add_right, ih]
private theorem q_sum_offdiag {α : Type*} [DecidableEq α] {M : Type*}
    [AddCommGroup M] [Module ℝ M] (q : QuadraticMap ℝ M ℝ) (f : α → M)
    (hsym : ∀ x y, QuadraticMap.polar q x y = QuadraticMap.polar q y x)
    (s : Finset α) :
    q (∑ i ∈ s, f i) =
      (∑ i ∈ s, q (f i)) +
        (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
          if i = j then 0 else QuadraticMap.polar q (f i) (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hp := polar_sum_right q (f a) f s
    have hrow :
        (∑ j ∈ s, if a = j then 0 else QuadraticMap.polar q (f a) (f j)) =
        ∑ j ∈ s, QuadraticMap.polar q (f a) (f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hne : a ≠ j := (ne_of_mem_of_not_mem hj ha).symm
      simp [hne]
    have hcol :
        (∑ i ∈ s, if i = a then 0 else QuadraticMap.polar q (f i) (f a)) =
        ∑ i ∈ s, QuadraticMap.polar q (f a) (f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hne : i ≠ a := ne_of_mem_of_not_mem hi ha
      simp [hne, hsym]
    have hcross :
        (∑ i ∈ insert a s, ∑ j ∈ insert a s,
          if i = j then 0 else QuadraticMap.polar q (f i) (f j)) =
        (∑ i ∈ s, ∑ j ∈ s,
          if i = j then 0 else QuadraticMap.polar q (f i) (f j)) +
          2 * ∑ j ∈ s, QuadraticMap.polar q (f a) (f j) := by
      simp only [Finset.sum_insert ha]
      rw [Finset.sum_add_distrib, hrow, hcol]
      simp
      ring
    calc
      q (∑ i ∈ insert a s, f i) = q (f a + ∑ i ∈ s, f i) := by
        congr 1
        rw [Finset.sum_insert ha]
      _ = q (f a) + q (∑ i ∈ s, f i) +
            QuadraticMap.polar q (f a) (∑ i ∈ s, f i) :=
        QuadraticMap.map_add q _ _
      _ = q (f a) + (∑ i ∈ s, q (f i) +
            (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
              if i = j then 0 else QuadraticMap.polar q (f i) (f j)) +
            ∑ i ∈ s, QuadraticMap.polar q (f a) (f i) := by rw [ih, hp]
      _ = (∑ i ∈ insert a s, q (f i)) +
            (1 / 2 : ℝ) * ∑ i ∈ insert a s, ∑ j ∈ insert a s,
              if i = j then 0 else QuadraticMap.polar q (f i) (f j) := by
        rw [Finset.sum_insert ha, hcross]
        ring
private theorem crossPair_swap {α : Type*} [Fintype α]
    (H : WellGeometry d α) (i j : α) (u v : L2 d) :
    H.crossPair i j u v = H.crossPair j i v u := by
  unfold crossPair
  have hc : H.L • (H.a j - H.a i) = -(H.L • (H.a i - H.a j)) := by
    rw [show H.a j - H.a i = -(H.a i - H.a j) by abel, smul_neg]
  rw [hc]
  simp only [kernelCrossPairing]
  calc
    (∫ z : Eucl d × Eucl d,
        (u : Eucl d → ℝ) z.1 * (v : Eucl d → ℝ) z.2 *
          multiWellCrossKernel H.κ (H.L • (H.a i - H.a j)) z.1 z.2
        ∂((volume : Measure (Eucl d)).prod volume)) =
        ∫ z : Eucl d × Eucl d,
          (u : Eucl d → ℝ) z.2 * (v : Eucl d → ℝ) z.1 *
            multiWellCrossKernel H.κ (H.L • (H.a i - H.a j)) z.2 z.1
          ∂((volume : Measure (Eucl d)).prod volume) := by
      exact MeasureTheory.integral_prod_swap
        (fun z : Eucl d × Eucl d =>
          (u : Eucl d → ℝ) z.2 * (v : Eucl d → ℝ) z.1 *
            multiWellCrossKernel H.κ (H.L • (H.a i - H.a j)) z.2 z.1)
    _ = ∫ z : Eucl d × Eucl d,
          (v : Eucl d → ℝ) z.1 * (u : Eucl d → ℝ) z.2 *
            multiWellCrossKernel H.κ (-(H.L • (H.a i - H.a j))) z.1 z.2
          ∂((volume : Measure (Eucl d)).prod volume) := by
      apply MeasureTheory.integral_congr_ae
      apply MeasureTheory.ae_of_all
      intro z
      rcases z with ⟨x,y⟩
      change (u : Eucl d → ℝ) y * (v : Eucl d → ℝ) x *
          multiWellCrossKernel H.κ (H.L • (H.a i - H.a j)) y x =
        (v : Eucl d → ℝ) x * (u : Eucl d → ℝ) y *
          multiWellCrossKernel H.κ (-(H.L • (H.a i - H.a j))) x y
      rw [multiWellCrossKernel_neg_center_swap H.κ (H.L • (H.a i - H.a j)) y x]
      ring
private theorem formQ_diag_eq (c : ℝ) (ψ : formDomain G.κ G.Ω) :
    (∑ j, formQ c G.κ G.Ω (G.Φ (G.wellMap j ψ) j)) = G.Q0 c ψ := by
  simp [WellGeometry.Q0, QuadraticMap.comp_apply, formQ_phi]
private def testRegion (G : WellGeometry d ι) (j : ι) : Set (Eucl d) :=
  {x | x - G.L • G.a j ∈ G.D}
private theorem test_zero_off_region (φ : formDomain G.κ G.D) (j : ι) :
    ∀ᵐ x ∂(volume : Measure (Eucl d)),
      x ∉ G.testRegion j → ((G.Φ φ j : formDomain G.κ G.Ω) : L2 d) x = 0 := by
  let b := G.L • G.a j
  have hφ := φ.property.1
  have hpull :=
    (measurePreserving_sub_right (volume : Measure (Eucl d)) b).quasiMeasurePreserving.ae hφ
  have hrep := translateL2_ae b (φ : L2 d)
  filter_upwards [hpull, hrep] with x hx hrep
  intro hout
  change ((translateL2 b (φ : L2 d) : L2 d) x) = 0
  rw [hrep]
  apply hx
  simpa [testRegion, b] using hout
private theorem testRegion_sub_closedBall (j : ι) :
    G.testRegion j ⊆ Metric.closedBall (G.L • G.a j) G.R := by
  intro x hx
  apply Metric.mem_closedBall.mpr
  rw [dist_eq_norm]
  have h := G.hDR hx
  have hnorm : ‖x - G.L • G.a j‖ < G.R := by
    simpa [Metric.mem_ball, dist_eq_norm] using h
  exact hnorm.le
private theorem testRegion_dist (i j : ι) (hij : i ≠ j)
    {x y : Eucl d} (hx : x ∈ G.testRegion i) (hy : y ∈ G.testRegion j) :
    2 * G.R ≤ dist x y := by
  let bi := G.L • G.a i
  let bj := G.L • G.a j
  let xi := x - bi
  let yj := y - bj
  have hxi : ‖xi‖ < G.R := by
    have h := G.hDR hx
    simpa [xi, Metric.mem_ball, dist_eq_norm] using h
  have hyj : ‖yj‖ < G.R := by
    have h := G.hDR hy
    simpa [yj, Metric.mem_ball, dist_eq_norm] using h
  have hcent : 4 * G.R ≤ ‖bi - bj‖ := by
    have hsub : bi - bj = G.L • (G.a i - G.a j) := by
      dsimp [bi, bj]
      rw [smul_sub]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos G.hL]
    exact G.hsep i j hij
  have hxy : ‖xi - yj‖ ≤ 2 * G.R := by
    calc
      ‖xi - yj‖ ≤ ‖xi‖ + ‖yj‖ := norm_sub_le _ _
      _ ≤ G.R + G.R := add_le_add hxi.le hyj.le
      _ = 2 * G.R := by ring
  have hkey : bi - bj + (xi - yj) = x - y := by
    dsimp only [xi, yj]
    abel
  have hrev : ‖bi - bj‖ - ‖xi - yj‖ ≤ ‖x - y‖ := by
    have htri := norm_sub_norm_le (bi - bj) (-(xi - yj))
    rw [norm_neg] at htri
    have hrev' : ‖bi - bj‖ - ‖xi - yj‖ ≤
        ‖(bi - bj) - (-(xi - yj))‖ := by linarith
    calc
      ‖bi - bj‖ - ‖xi - yj‖ ≤ ‖(bi - bj) - (-(xi - yj))‖ := hrev'
      _ = ‖x - y‖ := by rw [sub_neg_eq_add, hkey]
  have hfinal : 2 * G.R ≤ ‖x - y‖ := by linarith
  simpa [dist_eq_norm] using hfinal
private theorem testRegion_disjoint (i j : ι) (hij : i ≠ j) :
    Disjoint (G.testRegion i) (G.testRegion j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hd := G.testRegion_dist i j hij hxi hxj
  rw [dist_self] at hd
  have hp : 0 < 2 * G.R := by nlinarith [G.hR]
  linarith
private theorem l1_of_supported_closedBall (f : L2 d) (center : Eucl d) (r : ℝ)
    (hsupp : ∀ᵐ x ∂(volume : Measure (Eucl d)),
      x ∉ Metric.closedBall center r → f x = 0) :
    Integrable (fun x : Eucl d => f x) (volume : Measure (Eucl d)) := by
  let E : Set (Eucl d) := Metric.closedBall center r
  have hmem : MemLp (fun x : Eucl d => f x) 2 ((volume : Measure (Eucl d)).restrict E) :=
    (Lp.memLp f).restrict E
  have hfin : (volume : Measure (Eucl d)) E ≠ ⊤ := by
    simpa [E] using measure_closedBall_lt_top.ne
  letI : IsFiniteMeasure ((volume : Measure (Eucl d)).restrict E) :=
    isFiniteMeasure_restrict.mpr hfin
  have hint : Integrable (fun x : Eucl d => f x) ((volume : Measure (Eucl d)).restrict E) :=
    MemLp.integrable (by norm_num) hmem
  have hind : Integrable (E.indicator (fun x : Eucl d => f x)) (volume : Measure (Eucl d)) :=
    (integrable_indicator_iff (by exact Metric.isClosed_closedBall.measurableSet)).2 hint
  have heq : E.indicator (fun x : Eucl d => f x) =ᵐ[volume] fun x => f x := by
    filter_upwards [hsupp] with x hx
    by_cases hxe : x ∈ E
    · simp [Set.indicator, hxe]
    · simp [Set.indicator, hxe, hx hxe]
  exact hind.congr heq
private theorem testPhi_integrable (φ : formDomain G.κ G.D) (j : ι) :
    Integrable (fun x : Eucl d => ((G.Φ φ j : formDomain G.κ G.Ω) : L2 d) x)
      (volume : Measure (Eucl d)) := by
  let b := G.L • G.a j
  have hsupp : ∀ᵐ x ∂(volume : Measure (Eucl d)),
      x ∉ Metric.closedBall b G.R →
        ((G.Φ φ j : formDomain G.κ G.Ω) : L2 d) x = 0 := by
    filter_upwards [G.test_zero_off_region φ j] with x hx
    intro hball
    apply hx
    intro hreg
    exact hball (G.testRegion_sub_closedBall j hreg)
  exact l1_of_supported_closedBall
    ((G.Φ φ j : formDomain G.κ G.Ω) : L2 d) b G.R hsupp
private theorem testKernel_bound (x y : Eucl d) (hxy : 2 * G.R ≤ dist x y) :
    ‖gagliardoKernel G.κ x y‖ ≤ (2 * G.R) ^ (-G.κ) := by
  have hpos : 0 < 2 * G.R := by nlinarith [G.hR]
  have hnorm : 2 * G.R ≤ ‖x - y‖ := by simpa [dist_eq_norm] using hxy
  have hexp : -G.κ ≤ 0 := by linarith [G.hκ]
  have hp := Real.rpow_le_rpow_of_nonpos hpos hnorm hexp
  change ‖‖x - y‖ ^ (-G.κ)‖ ≤ _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact hp
private theorem testCross_integrable (φi φj : formDomain G.κ G.D) (i j : ι)
    (hij : i ≠ j) :
    Integrable
      (fun z : Eucl d × Eucl d =>
        ((G.Φ φi i : formDomain G.κ G.Ω) : L2 d) z.1 *
          ((G.Φ φj j : formDomain G.κ G.Ω) : L2 d) z.2 *
            gagliardoKernel G.κ z.1 z.2)
      ((volume : Measure (Eucl d)).prod volume) := by
  let fi : L2 d := (G.Φ φi i : formDomain G.κ G.Ω)
  let fj : L2 d := (G.Φ φj j : formDomain G.κ G.Ω)
  have hfi : Integrable (fun x : Eucl d => fi x) (volume : Measure (Eucl d)) :=
    G.testPhi_integrable φi i
  have hfj : Integrable (fun x : Eucl d => fj x) (volume : Measure (Eucl d)) :=
    G.testPhi_integrable φj j
  have hprodAbs : Integrable
      (fun z : Eucl d × Eucl d => |fi z.1| * |fj z.2|)
      ((volume : Measure (Eucl d)).prod volume) := hfi.abs.mul_prod hfj.abs
  have hfi0 := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae
      (G.test_zero_off_region φi i)
  have hfj0 := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae
      (G.test_zero_off_region φj j)
  let C : ℝ := (2 * G.R) ^ (-G.κ)
  have hbound : ∀ᵐ z : Eucl d × Eucl d
      ∂((volume : Measure (Eucl d)).prod volume),
      ‖fi z.1 * fj z.2 * gagliardoKernel G.κ z.1 z.2‖ ≤
        C * (|fi z.1| * |fj z.2|) := by
    filter_upwards [hfi0, hfj0] with z hi hj
    by_cases hfi_zero : fi z.1 = 0
    · simp [hfi_zero, C]
    · by_cases hfj_zero : fj z.2 = 0
      · simp [hfj_zero, C]
      · have hri : z.1 ∈ G.testRegion i := by
          by_contra hout
          exact hfi_zero (hi hout)
        have hrj : z.2 ∈ G.testRegion j := by
          by_contra hout
          exact hfj_zero (hj hout)
        have hk := G.testKernel_bound z.1 z.2 (G.testRegion_dist i j hij hri hrj)
        calc
          ‖fi z.1 * fj z.2 * gagliardoKernel G.κ z.1 z.2‖ =
              |fi z.1| * |fj z.2| * ‖gagliardoKernel G.κ z.1 z.2‖ := by
                simp [Real.norm_eq_abs]
          _ ≤ (|fi z.1| * |fj z.2|) * C := by
                exact mul_le_mul_of_nonneg_left hk
                  (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = C * (|fi z.1| * |fj z.2|) := by ring
  have hkernel := gagliardoKernel_aestronglyMeasurable G.κ
    (volume : Measure (Eucl d))
  have hmeasfi : AEStronglyMeasurable (fun z : Eucl d × Eucl d => fi z.1)
      ((volume : Measure (Eucl d)).prod volume) :=
    (Lp.aestronglyMeasurable fi).comp_fst
  have hmeasfj : AEStronglyMeasurable (fun z : Eucl d × Eucl d => fj z.2)
      ((volume : Measure (Eucl d)).prod volume) :=
    (Lp.aestronglyMeasurable fj).comp_snd
  have hmeas : AEStronglyMeasurable
      (fun z : Eucl d × Eucl d => fi z.1 * fj z.2 * gagliardoKernel G.κ z.1 z.2)
      ((volume : Measure (Eucl d)).prod volume) :=
    (hmeasfi.mul hmeasfj).mul hkernel
  have htarget := (hprodAbs.const_mul C).mono' hmeas hbound
  simpa [fi, fj, C] using htarget
private theorem test_translate_pairing (φi φj : formDomain G.κ G.D) (i j : ι) :
    ∫ z : Eucl d × Eucl d,
        ((G.Φ φi i : formDomain G.κ G.Ω) : L2 d) z.1 *
          ((G.Φ φj j : formDomain G.κ G.Ω) : L2 d) z.2 *
            gagliardoKernel G.κ z.1 z.2
          ∂((volume : Measure (Eucl d)).prod volume) =
      G.crossPair i j (φi : L2 d) (φj : L2 d) := by
  let bi := G.L • G.a i
  let bj := G.L • G.a j
  let fi : L2 d := G.Φ φi i
  let fj : L2 d := G.Φ φj j
  let A : Eucl d × Eucl d → ℝ := fun z =>
    fi z.1 * fj z.2 * gagliardoKernel G.κ z.1 z.2
  let e : (Eucl d × Eucl d) ≃ᵐ (Eucl d × Eucl d) :=
    (MeasurableEquiv.addRight bi).prodCongr (MeasurableEquiv.addRight bj)
  have hmp : MeasurePreserving e
      ((volume : Measure (Eucl d)).prod volume)
      ((volume : Measure (Eucl d)).prod volume) := by
    have h := MeasurePreserving.prod
      (measurePreserving_sub_right (volume : Measure (Eucl d)) (-bi))
      (measurePreserving_sub_right (volume : Measure (Eucl d)) (-bj))
    have he : ⇑e = fun z : Eucl d × Eucl d => (z.1 + bi, z.2 + bj) := by
      funext z
      rcases z with ⟨x,y⟩
      simp [e, MeasurableEquiv.prodCongr, MeasurableEquiv.addRight,
        sub_neg_eq_add]
    rw [he]
    convert h using 1 <;> ext z <;> simp [sub_neg_eq_add]
  have hfiShift : (fun x : Eucl d => fi (x + bi)) =ᵐ[volume] fun x => (φi : L2 d) x := by
    have h := (measurePreserving_sub_right (volume : Measure (Eucl d)) (-bi))
      |>.quasiMeasurePreserving.ae_eq_comp (translateL2_ae bi (φi : L2 d))
    filter_upwards [h] with x hx
    simpa [fi, WellGeometry.Φ, Function.comp_apply, sub_neg_eq_add] using hx
  have hfjShift : (fun y : Eucl d => fj (y + bj)) =ᵐ[volume] fun y => (φj : L2 d) y := by
    have h := (measurePreserving_sub_right (volume : Measure (Eucl d)) (-bj))
      |>.quasiMeasurePreserving.ae_eq_comp (translateL2_ae bj (φj : L2 d))
    filter_upwards [h] with y hy
    simpa [fj, WellGeometry.Φ, Function.comp_apply, sub_neg_eq_add] using hy
  have hfst := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae_eq_comp hfiShift
  have hsnd := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae_eq_comp hfjShift
  have htrans : (fun z : Eucl d × Eucl d => A (e z)) =ᵐ[volume.prod volume]
      fun z => (φi : L2 d) z.1 * (φj : L2 d) z.2 *
        multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2 := by
    filter_upwards [hfst, hsnd] with z hx hy
    rcases z with ⟨x,y⟩
    have hx' : fi (x + bi) = (φi : L2 d) x := by simpa [Function.comp_apply] using hx
    have hy' : fj (y + bj) = (φj : L2 d) y := by simpa [Function.comp_apply] using hy
    have hcent : bi - bj = G.L • (G.a i - G.a j) := by
      dsimp [bi, bj]
      rw [smul_sub]
    have hk : gagliardoKernel G.κ (x + bi) (y + bj) =
        multiWellCrossKernel G.κ (bi - bj) x y := by
      unfold gagliardoKernel multiWellCrossKernel
      congr 1
      abel
    change fi (x + bi) * fj (y + bj) *
        gagliardoKernel G.κ (x + bi) (y + bj) = _
    rw [hx', hy', hk, hcent]
  calc
    (∫ z : Eucl d × Eucl d,
        ((G.Φ φi i : formDomain G.κ G.Ω) : L2 d) z.1 *
          ((G.Φ φj j : formDomain G.κ G.Ω) : L2 d) z.2 *
            gagliardoKernel G.κ z.1 z.2
          ∂((volume : Measure (Eucl d)).prod volume)) =
        ∫ z : Eucl d × Eucl d, A z ∂(volume.prod volume) := by rfl
    _ = ∫ z : Eucl d × Eucl d, A (e z) ∂(volume.prod volume) :=
      (hmp.integral_comp' A).symm
    _ = ∫ z : Eucl d × Eucl d,
        (φi : L2 d) z.1 * (φj : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2
          ∂(volume.prod volume) := by exact integral_congr_ae htrans
    _ = G.crossPair i j (φi : L2 d) (φj : L2 d) := by
      simp [WellGeometry.crossPair, kernelCrossPairing]
private theorem test_polar_offdiag (c : ℝ) (φi φj : formDomain G.κ G.D)
    (i j : ι) (hij : i ≠ j) :
    QuadraticMap.polar (formQ c G.κ G.Ω)
        (G.Φ φi i : formDomain G.κ G.Ω)
        (G.Φ φj j : formDomain G.κ G.Ω) =
      -2 * c * G.crossPair i j (φi : L2 d) (φj : L2 d) := by
  let fi : L2 d := G.Φ φi i
  let fj : L2 d := G.Φ φj j
  let A : Eucl d × Eucl d → ℝ := fun z =>
    fi z.1 * fj z.2 * gagliardoKernel G.κ z.1 z.2
  let B : Eucl d × Eucl d → ℝ := fun z =>
    fi z.2 * fj z.1 * gagliardoKernel G.κ z.1 z.2
  have hfi := G.test_zero_off_region φi i
  have hfj := G.test_zero_off_region φj j
  have hdis := G.testRegion_disjoint i j hij
  have hzero : ∀ᵐ x ∂(volume : Measure (Eucl d)), fi x * fj x = 0 := by
    filter_upwards [hfi, hfj] with x hi hj
    by_cases hxi : x ∈ G.testRegion i
    · have hxj : x ∉ G.testRegion j := by
        intro hxj
        exact (Set.disjoint_left.mp hdis) hxi hxj
      have hj0 : fj x = 0 := by
        change ((G.Φ φj j : formDomain G.κ G.Ω) : L2 d) x = 0
        exact hj hxj
      simp [hj0]
    · have hi0 : fi x = 0 := by
        change ((G.Φ φi i : formDomain G.κ G.Ω) : L2 d) x = 0
        exact hi hxi
      simp [hi0]
  have hzfst := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae hzero
  have hzsnd := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae hzero
  have hdelta : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
      (fi z.1 - fi z.2) * (fj z.1 - fj z.2) =
        -(fi z.1 * fj z.2) - fi z.2 * fj z.1 := by
    filter_upwards [hzfst, hzsnd] with z hx hy
    calc
      (fi z.1 - fi z.2) * (fj z.1 - fj z.2) =
          fi z.1 * fj z.1 - fi z.1 * fj z.2 -
            fi z.2 * fj z.1 + fi z.2 * fj z.2 := by ring
      _ = -(fi z.1 * fj z.2) - fi z.2 * fj z.1 := by
        rw [hx, hy]
        ring
  have hdeltaK : (fun z : Eucl d × Eucl d =>
      (fi z.1 - fi z.2) * (fj z.1 - fj z.2) *
        gagliardoKernel G.κ z.1 z.2) =ᵐ[volume.prod volume]
      fun z => -A z - B z := by
    filter_upwards [hdelta] with z hz
    rw [hz]
    simp only [A, B]
    ring
  have hA : Integrable A (volume.prod volume) := by
    simpa [A, fi, fj] using G.testCross_integrable φi φj i j hij
  have hBAfun : ∀ z : Eucl d × Eucl d, B z = A z.swap := by
    intro z
    rcases z with ⟨x,y⟩
    simp only [A, B, Prod.swap, gagliardoKernel]
    rw [norm_sub_rev]
  have hB : Integrable B (volume.prod volume) := by
    have hAswap : Integrable (fun z : Eucl d × Eucl d => A z.swap)
        (volume.prod volume) := hA.swap
    apply hAswap.congr
    exact MeasureTheory.ae_of_all _ (fun z => (hBAfun z).symm)
  have hBswap : ∫ z : Eucl d × Eucl d, B z ∂(volume.prod volume) =
      ∫ z : Eucl d × Eucl d, A z.swap ∂(volume.prod volume) := by
    apply MeasureTheory.integral_congr_ae
    exact MeasureTheory.ae_of_all _ hBAfun
  have hswap : ∫ z : Eucl d × Eucl d, A z.swap ∂(volume.prod volume) =
      ∫ z : Eucl d × Eucl d, A z ∂(volume.prod volume) := by
    simpa using (MeasureTheory.integral_prod_swap
      (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d))) A)
  have hBA : ∫ z : Eucl d × Eucl d, B z ∂(volume.prod volume) =
      ∫ z : Eucl d × Eucl d, A z ∂(volume.prod volume) := hBswap.trans hswap
  have hsum : ∫ z : Eucl d × Eucl d, -A z - B z ∂(volume.prod volume) =
      -(∫ z : Eucl d × Eucl d, A z ∂(volume.prod volume) +
        ∫ z : Eucl d × Eucl d, B z ∂(volume.prod volume)) := by
    calc
      ∫ z : Eucl d × Eucl d, -A z - B z ∂(volume.prod volume) =
          ∫ z : Eucl d × Eucl d, -(A z + B z) ∂(volume.prod volume) := by
            apply MeasureTheory.integral_congr_ae
            exact MeasureTheory.ae_of_all _ (fun z => by ring)
      _ = -∫ z : Eucl d × Eucl d, A z + B z ∂(volume.prod volume) := by
            rw [MeasureTheory.integral_neg]
      _ = -(∫ z : Eucl d × Eucl d, A z ∂(volume.prod volume) +
            ∫ z : Eucl d × Eucl d, B z ∂(volume.prod volume)) := by
            rw [MeasureTheory.integral_add hA hB]
  have htrans : (∫ z : Eucl d × Eucl d, A z ∂(volume.prod volume)) =
      G.crossPair i j (φi : L2 d) (φj : L2 d) := by
    simpa [A, fi, fj] using G.test_translate_pairing φi φj i j
  calc
    QuadraticMap.polar (formQ c G.κ G.Ω)
        (G.Φ φi i : formDomain G.κ G.Ω)
        (G.Φ φj j : formDomain G.κ G.Ω) =
      c * ∫ z : Eucl d × Eucl d,
        (((G.Φ φi i : formDomain G.κ G.Ω) : L2 d) z.1 -
          ((G.Φ φi i : formDomain G.κ G.Ω) : L2 d) z.2) *
        (((G.Φ φj j : formDomain G.κ G.Ω) : L2 d) z.1 -
          ((G.Φ φj j : formDomain G.κ G.Ω) : L2 d) z.2) *
            gagliardoKernel G.κ z.1 z.2 ∂(volume.prod volume) :=
      formQ_polar c G.κ G.Ω _ _
    _ = c * ∫ z : Eucl d × Eucl d, -A z - B z ∂(volume.prod volume) := by
      congr 1
      exact MeasureTheory.integral_congr_ae hdeltaK
    _ = c * -(∫ z : Eucl d × Eucl d, A z ∂(volume.prod volume) +
        ∫ z : Eucl d × Eucl d, B z ∂(volume.prod volume)) := by rw [hsum]
    _ = -2 * c * G.crossPair i j (φi : L2 d) (φj : L2 d) := by
      rw [hBA, htrans]
      ring
/-- The exact block identity of Lemma 4.1 in the sense of closed forms. -/
theorem formQ_eq (c : ℝ) (ψ : formDomain G.κ G.Ω) :
    formQ c G.κ G.Ω ψ = G.Q0 c ψ + G.interaction c ψ ψ := by
  let f : ι → formDomain G.κ G.Ω := fun j => G.Φ (G.wellMap j ψ) j
  have hrec : ψ = ∑ j, f j := by
    exact sumPhi_eq G ψ
  have hq := q_sum_offdiag (formQ c G.κ G.Ω) f
    (fun x y => QuadraticMap.polar_comm _ x y) Finset.univ
  have hdiag : (∑ j, formQ c G.κ G.Ω (f j)) = G.Q0 c ψ := by
    simpa [f] using formQ_diag_eq G c ψ
  have hpair (i j : ι) (hij : i ≠ j) :
      QuadraticMap.polar (formQ c G.κ G.Ω) (f i) (f j) =
        -2 * c * G.crossPair i j
          (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (ψ : L2 d)) := by
    simpa [f] using
      G.test_polar_offdiag c (G.wellMap i ψ) (G.wellMap j ψ) i j hij
  have hsumPolar :
      (∑ i, ∑ j, (if i = j then (0 : ℝ) else
        QuadraticMap.polar (formQ c G.κ G.Ω) (f i) (f j))) =
        (-2 * c) * ∑ i, ∑ j, (if i = j then (0 : ℝ) else
          G.crossPair i j (G.pieceL2 i (ψ : L2 d))
            (G.pieceL2 j (ψ : L2 d))) := by
    calc
      (∑ i, ∑ j, (if i = j then (0 : ℝ) else
          QuadraticMap.polar (formQ c G.κ G.Ω) (f i) (f j))) =
        ∑ i, ∑ j, (-2 * c) *
          (if i = j then (0 : ℝ) else
            G.crossPair i j (G.pieceL2 i (ψ : L2 d))
              (G.pieceL2 j (ψ : L2 d))) := by
          apply Fintype.sum_congr
          intro i
          apply Fintype.sum_congr
          intro j
          by_cases hij : i = j
          · simp [hij]
          · simpa [hij] using hpair i j hij
      _ = (-2 * c) * ∑ i, ∑ j, (if i = j then (0 : ℝ) else
            G.crossPair i j (G.pieceL2 i (ψ : L2 d))
              (G.pieceL2 j (ψ : L2 d))) := by
          simp_rw [← Finset.mul_sum]
  have hinteraction :
      (1 / 2 : ℝ) * ∑ i, ∑ j, (if i = j then (0 : ℝ) else
        QuadraticMap.polar (formQ c G.κ G.Ω) (f i) (f j)) =
        G.interactionFun c ψ ψ := by
    rw [hsumPolar, WellGeometry.interactionFun]
    ring
  calc
    formQ c G.κ G.Ω ψ = formQ c G.κ G.Ω (∑ j, f j) := by rw [hrec]
    _ = G.Q0 c ψ + G.interaction c ψ ψ := by
      rw [hq, hdiag, G.interaction_apply, hinteraction]
theorem interaction_symm (c : ℝ) (ψ χ : formDomain G.κ G.Ω) :
    G.interaction c ψ χ = G.interaction c χ ψ := by
  rw [G.interaction_apply, G.interaction_apply]
  unfold interactionFun
  congr 1
  calc
    (∑ i, ∑ j, if i = j then (0 : ℝ) else
        G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))) =
      ∑ j, ∑ i, if i = j then (0 : ℝ) else
        G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d)) := by
          exact Finset.sum_comm
    _ = ∑ i, ∑ j, if i = j then (0 : ℝ) else
        G.crossPair i j (G.pieceL2 i (χ : L2 d)) (G.pieceL2 j (ψ : L2 d)) := by
      apply Fintype.sum_congr
      intro j
      apply Fintype.sum_congr
      intro i
      by_cases hij : i = j
      · simp [hij]
      · simp only [if_neg hij, if_neg (Ne.symm hij)]
        exact crossPair_swap G i j
          (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))
end WellGeometry
end Tunneling
===END FILE===
