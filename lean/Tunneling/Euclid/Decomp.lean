import Tunneling.Euclid.Translate
import Tunneling.MultiWell

/-!
# Exact multi-well reduction (paper Lemma 4.2 (`lem:multi-block`))

For `N` translates `D + L a_j` with `L |a_i - a_j| ≥ 4R` and `D ⊆ B_R(0)`,
every `ψ ∈ H^s_0(Ω_{a,L})` splits into the pieces
`u_j(x) = ψ(x + L a_j) 1_D(x) ∈ H^s_0(D)`, and

  `Q_Ω[ψ] = Σ_j Q_D[u_j] + w(ψ, ψ)`,
  `w(ψ, χ) = -c Σ_{i ≠ j} ∬ u_i(x) v_j(y) |L(a_i - a_j) + x - y|^{-κ} dx dy`,

which is the form version of `A_Ω ≅ 𝒜₀ + 𝒱_L`.  The interaction obeys
`|w(ψ, χ)| ≤ γ_L ‖ψ‖ ‖χ‖` with `γ_L = c 2^κ |D| Σ_κ(a) L^{-κ}`
(equation `eq:gamma-L`).
-/

namespace Tunneling
open MeasureTheory
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The multi-well domain `Ω_{a,L} = ⋃_j (D + L a_j)` of equation
`eq:multi-domain`. -/
def multiWellDomain (D : Set (Eucl d)) (a : ι → Eucl d) (L : ℝ) : Set (Eucl d) := {x | ∃ j, x - L • a j ∈ D}
/-- Geometric data of paper Lemma 4.2 (`lem:multi-block`): a measurable `D ⊆ B_R(0)` and
translation sites with `L |a_i - a_j| ≥ 4R` for `i ≠ j`. -/
structure WellGeometry (d : ℕ) (ι : Type*) [Fintype ι] where
  κ : ℝ
  hκ : 0 < κ
  R : ℝ
  hR : 0 < R
  D : Set (Eucl d)
  hDm : MeasurableSet D
  hDR : D ⊆ Metric.ball 0 R
  a : ι → Eucl d
  L : ℝ
  hL : 0 < L
  hsep : ∀ i j, i ≠ j → 4 * R ≤ L * ‖a i - a j‖
namespace WellGeometry
variable (G : WellGeometry d ι)
/-- The domain `Ω_{a,L}`. -/
def Ω : Set (Eucl d) := multiWellDomain G.D G.a G.L
private def wellRegion (j : ι) : Set (Eucl d) := {x | x - G.L • G.a j ∈ G.D}
/-- The `j`-th piece `u_j = 1_D · τ_{-L a_j} ψ`, i.e. `u_j(x) = ψ(x + L a_j)`
for `x ∈ D`. -/
noncomputable def pieceL2 (j : ι) : L2 d →ₗ[ℝ] L2 d :=
  (indicatorL2 G.D G.hDm).comp (translateL2 (-(G.L • G.a j))).toLinearMap
private theorem wellRegion_measurable (j : ι) : MeasurableSet (G.wellRegion j) := by
  apply G.hDm.preimage
  exact (continuous_id.sub continuous_const).measurable
private theorem Ω_eq_iUnion : G.Ω = ⋃ j, G.wellRegion j := by
  ext x
  simp [Ω, multiWellDomain, wellRegion]
private theorem wellRegion_closedBall (j : ι) :
    G.wellRegion j ⊆ Metric.closedBall (G.L • G.a j) G.R := by
  intro x hx
  apply Metric.mem_closedBall.mpr
  rw [dist_eq_norm]
  have hh := G.hDR hx
  have hlt : ‖x - G.L • G.a j‖ < G.R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hh
  exact hlt.le
private theorem wellRegion_dist (i j : ι) (hij : i ≠ j)
    {x y : Eucl d} (hx : x ∈ G.wellRegion i) (hy : y ∈ G.wellRegion j) :
    2 * G.R ≤ dist x y := by
  let bi : Eucl d := G.L • G.a i
  let bj : Eucl d := G.L • G.a j
  have hxR : dist x bi < G.R := by
    have h := G.hDR hx
    simpa [Metric.mem_ball, dist_eq_norm, bi] using h
  have hyR : dist y bj < G.R := by
    have h := G.hDR hy
    simpa [Metric.mem_ball, dist_eq_norm, bj] using h
  have hcent : 4 * G.R ≤ dist bi bj := by
    rw [dist_eq_norm]
    dsimp [bi, bj]
    rw [show G.L • G.a i - G.L • G.a j = G.L • (G.a i - G.a j) by rw [smul_sub]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos G.hL]
    exact G.hsep i j hij
  have htri := dist_triangle bi x bj
  have htri2 := dist_triangle x y bj
  have hineq : dist bi bj ≤ dist bi x + dist x y + dist y bj := by nlinarith [htri, htri2]
  have hdistx : dist bi x = dist x bi := dist_comm _ _
  nlinarith [hineq, hxR, hyR, hcent]
private theorem wellRegion_pairwise : Pairwise (fun i j =>
    Disjoint (G.wellRegion i) (G.wellRegion j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hd := G.wellRegion_dist i j hij hxi hxj
  rw [dist_self] at hd
  have hp : 0 < 2 * G.R := by nlinarith [G.hR]
  linarith
private theorem kernel_le_of_dist {x y : Eucl d} (hxy : 2 * G.R ≤ dist x y) :
    gagliardoKernel G.κ x y ≤ (2 * G.R) ^ (-G.κ) := by
  have hpos : 0 < 2 * G.R := by nlinarith [G.hR]
  have hnorm : 2 * G.R ≤ ‖x - y‖ := by simpa [dist_eq_norm] using hxy
  have hexp : -G.κ ≤ 0 := by linarith [G.hκ]
  have hp := Real.rpow_le_rpow_of_nonpos hpos hnorm hexp
  change ‖x - y‖ ^ (-G.κ) ≤ _
  exact hp
private theorem formDomain_mono {κ : ℝ} {A B : Set (Eucl d)} (hAB : A ⊆ B)
    {f : L2 d} (hf : f ∈ formDomain κ A) : f ∈ formDomain κ B := by
  rw [mem_formDomain_iff] at hf ⊢
  exact ⟨by
    filter_upwards [hf.1] with x hx
    intro hnot
    apply hx
    intro hA
    exact hnot (hAB hA), hf.2⟩
private theorem Ω_measure_lt_top : (volume : Measure (Eucl d)) G.Ω < ⊤ := by
  have hsub : G.Ω ⊆ ⋃ j, Metric.closedBall (G.L • G.a j) G.R := by
    rw [G.Ω_eq_iUnion]
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j,hj⟩
    exact Set.mem_iUnion.mpr ⟨j,G.wellRegion_closedBall j hj⟩
  calc
    volume G.Ω ≤ volume (⋃ j, Metric.closedBall (G.L • G.a j) G.R) := measure_mono hsub
    _ ≤ ∑ j, volume (Metric.closedBall (G.L • G.a j) G.R) := measure_iUnion_fintype_le _ _
    _ < ⊤ := by
      simp only [ENNReal.sum_lt_top]
      intro j hj
      exact measure_closedBall_lt_top (μ := (volume : Measure (Eucl d)))
private theorem region_cut_mem (j : ι) (ψ : formDomain G.κ G.Ω) :
    indicatorL2 (G.wellRegion j) (G.wellRegion_measurable j) (ψ : L2 d) ∈
      formDomain G.κ (G.wellRegion j) := by
  let cut : L2 d := indicatorL2 (G.wellRegion j) (G.wellRegion_measurable j) (ψ : L2 d)
  let f : Eucl d → ℝ := fun x => (ψ : L2 d) x
  let g : Eucl d → ℝ := (G.wellRegion j).indicator f
  let I : Eucl d → ℝ := G.Ω.indicator (fun _ => (1 : ℝ))
  let C : ℝ := (2 * G.R) ^ (-G.κ)
  have hψmem := (mem_formDomain_iff G.κ G.Ω (ψ : L2 d)).mp ψ.property
  have hψfst : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume), z.1 ∉ G.Ω → f z.1 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae hψmem.1
  have hψsnd : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume), z.2 ∉ G.Ω → f z.2 = 0 :=
    Measure.quasiMeasurePreserving_snd.ae hψmem.1
  have hcutAE : (cut : L2 d) =ᵐ[volume] g := by
    dsimp [cut, g, f]
    exact indicatorL2_ae (G.wellRegion j) (G.wellRegion_measurable j) (ψ : L2 d)
  have hcutfst : (fun z : Eucl d × Eucl d => (cut : L2 d) z.1) =ᵐ[volume.prod volume]
      fun z => g z.1 := Measure.quasiMeasurePreserving_fst.ae_eq_comp hcutAE
  have hcutsnd : (fun z : Eucl d × Eucl d => (cut : L2 d) z.2) =ᵐ[volume.prod volume]
      fun z => g z.2 := Measure.quasiMeasurePreserving_snd.ae_eq_comp hcutAE
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg (by nlinarith [G.hR]) _
  have hI : ∀ x, 0 ≤ I x := by
    intro x
    by_cases hx : x ∈ G.Ω <;> simp [I, Set.indicator, hx]
  have hcor : ∀ x y, 0 ≤ C * (f x ^ 2 * I y) + C * (f y ^ 2 * I x) := by
    intro x y
    exact add_nonneg
      (mul_nonneg hC (mul_nonneg (sq_nonneg _) (hI y)))
      (mul_nonneg hC (mul_nonneg (sq_nonneg _) (hI x)))
  have hpoint : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
      gagliardoIntegrand G.κ g z ≤ gagliardoIntegrand G.κ f z +
        (C * (f z.1 ^ 2 * I z.2) + C * (f z.2 ^ 2 * I z.1)) := by
    filter_upwards [hψfst, hψsnd] with z hxψ hyψ
    rcases z with ⟨x,y⟩
    by_cases hx : x ∈ G.wellRegion j
    · by_cases hy : y ∈ G.wellRegion j
      · have hxg : g x = f x := by simp [g, Set.indicator, hx]
        have hyg : g y = f y := by simp [g, Set.indicator, hy]
        rw [gagliardoIntegrand, gagliardoIntegrand, hxg, hyg]
        exact le_add_of_nonneg_right (hcor x y)
      · by_cases hyΩ : y ∈ G.Ω
        · obtain ⟨k, hyk⟩ : ∃ k, y ∈ G.wellRegion k := by
            rw [G.Ω_eq_iUnion] at hyΩ
            exact Set.mem_iUnion.mp hyΩ
          have hjk : j ≠ k := by
            intro h
            subst k
            exact hy hyk
          have hdist := G.wellRegion_dist j k hjk hx hyk
          have hk := G.kernel_le_of_dist hdist
          have hxg : g x = f x := by simp [g, Set.indicator, hx]
          have hyg : g y = 0 := by simp [g, Set.indicator, hy]
          have hIy : I y = 1 := by simp [I, Set.indicator, hyΩ]
          have hΩx : x ∈ G.Ω := ⟨j, by simpa [wellRegion] using hx⟩
          have hIx : I x = 1 := by simp [I, Set.indicator, hΩx]
          have hleft : gagliardoIntegrand G.κ g (x,y) ≤ C * (f x ^ 2 * I y) := by
            calc
              gagliardoIntegrand G.κ g (x,y) =
                  f x ^ 2 * gagliardoKernel G.κ x y := by
                    simp [gagliardoIntegrand, hxg, hyg]
              _ ≤ f x ^ 2 * C := mul_le_mul_of_nonneg_left hk (sq_nonneg _)
              _ = C * (f x ^ 2 * I y) := by rw [hIy]; ring
          have hbase : C * (f x ^ 2 * I y) ≤
              gagliardoIntegrand G.κ f (x,y) +
                (C * (f x ^ 2 * I y) + C * (f y ^ 2 * I x)) := by
            have henergy := gagliardoIntegrand_nonneg G.κ f (x,y)
            have hsecond : 0 ≤ C * (f y ^ 2 * I x) :=
              mul_nonneg hC (mul_nonneg (sq_nonneg (f y)) (hI x))
            nlinarith
          exact hleft.trans hbase
        · have hyzero : f y = 0 := hyψ hyΩ
          have hxg : g x = f x := by simp [g, Set.indicator, hx]
          have hyg : g y = f y := by simp [g, Set.indicator, hy, hyzero]
          rw [gagliardoIntegrand, gagliardoIntegrand, hxg, hyg]
          exact le_add_of_nonneg_right (hcor x y)
    · by_cases hy : y ∈ G.wellRegion j
      · by_cases hxΩ : x ∈ G.Ω
        · obtain ⟨k, hxk⟩ : ∃ k, x ∈ G.wellRegion k := by
            rw [G.Ω_eq_iUnion] at hxΩ
            exact Set.mem_iUnion.mp hxΩ
          have hkj : k ≠ j := by
            intro h
            subst k
            exact hx hxk
          have hdist := G.wellRegion_dist k j hkj hxk hy
          have hk := G.kernel_le_of_dist hdist
          have hxg : g x = 0 := by simp [g, Set.indicator, hx]
          have hyg : g y = f y := by simp [g, Set.indicator, hy]
          have hIx : I x = 1 := by simp [I, Set.indicator, hxΩ]
          have hΩy : y ∈ G.Ω := ⟨j, by simpa [wellRegion] using hy⟩
          have hIy : I y = 1 := by simp [I, Set.indicator, hΩy]
          have hleft : gagliardoIntegrand G.κ g (x,y) ≤ C * (f y ^ 2 * I x) := by
            calc
              gagliardoIntegrand G.κ g (x,y) =
                  f y ^ 2 * gagliardoKernel G.κ x y := by
                    simp [gagliardoIntegrand, hxg, hyg, neg_sq]
              _ ≤ f y ^ 2 * C := mul_le_mul_of_nonneg_left hk (sq_nonneg _)
              _ = C * (f y ^ 2 * I x) := by rw [hIx]; ring
          have hbase : C * (f y ^ 2 * I x) ≤
              gagliardoIntegrand G.κ f (x,y) +
                (C * (f x ^ 2 * I y) + C * (f y ^ 2 * I x)) := by
            have henergy := gagliardoIntegrand_nonneg G.κ f (x,y)
            have hfirst : 0 ≤ C * (f x ^ 2 * I y) :=
              mul_nonneg hC (mul_nonneg (sq_nonneg (f x)) (hI y))
            nlinarith
          exact hleft.trans hbase
        · have hxzero : f x = 0 := hxψ hxΩ
          have hxg : g x = f x := by simp [g, Set.indicator, hx, hxzero]
          have hyg : g y = f y := by simp [g, Set.indicator, hy]
          rw [gagliardoIntegrand, gagliardoIntegrand, hxg, hyg]
          exact le_add_of_nonneg_right (hcor x y)
      · have hxg : g x = 0 := by simp [g, Set.indicator, hx]
        have hyg : g y = 0 := by simp [g, Set.indicator, hy]
        rw [gagliardoIntegrand, gagliardoIntegrand, hxg, hyg]
        simpa [gagliardoIntegrand, gagliardoKernel] using
          add_nonneg (gagliardoIntegrand_nonneg G.κ f (x,y)) (hcor x y)
  have hsq : Integrable (fun x : Eucl d => f x ^ 2) (volume : Measure (Eucl d)) := by
    change Integrable (fun x => ((ψ : L2 d) x) ^ 2) _
    exact (Lp.memLp (ψ : L2 d)).integrable_sq
  have hΩvol : volume G.Ω < ⊤ := G.Ω_measure_lt_top
  have hΩm : MeasurableSet G.Ω := by
    rw [G.Ω_eq_iUnion]
    exact MeasurableSet.iUnion fun k => G.wellRegion_measurable k
  let μΩ : Measure (Eucl d) := volume.restrict G.Ω
  haveI : IsFiniteMeasure μΩ := isFiniteMeasure_restrict.mpr hΩvol.ne
  have hind : Integrable I (volume : Measure (Eucl d)) := by
    have hc : Integrable (fun _ : Eucl d => (1 : ℝ)) μΩ := integrable_const 1
    exact (integrable_indicator_iff hΩm).2 hc
  have hprod1 : Integrable (fun z : Eucl d × Eucl d => f z.1 ^ 2 * I z.2)
      (volume.prod volume) := hsq.mul_prod hind
  have hprod2 : Integrable (fun z : Eucl d × Eucl d => f z.2 ^ 2 * I z.1)
      (volume.prod volume) := by
    simpa [mul_comm] using hind.mul_prod hsq
  have hupper : Integrable (fun z : Eucl d × Eucl d => gagliardoIntegrand G.κ f z +
        (C * (f z.1 ^ 2 * I z.2) + C * (f z.2 ^ 2 * I z.1))) (volume.prod volume) :=
    hψmem.2.add ((hprod1.const_mul C).add (hprod2.const_mul C))
  have hK := gagliardoKernel_aestronglyMeasurable G.κ (volume : Measure (Eucl d))
  have hmeas := gagliardoIntegrand_aestronglyMeasurable G.κ (volume : Measure (Eucl d)) hK
    (Lp.aestronglyMeasurable cut)
  have hcutbound : (fun z : Eucl d × Eucl d => gagliardoIntegrand G.κ (cut : L2 d) z) ≤ᵐ[volume.prod volume]
      fun z => gagliardoIntegrand G.κ f z +
        (C * (f z.1 ^ 2 * I z.2) + C * (f z.2 ^ 2 * I z.1)) := by
    filter_upwards [hcutfst, hcutsnd, hpoint] with z hz₁ hz₂ hz
    rw [gagliardoIntegrand, hz₁, hz₂]
    exact hz
  have hnonneg : 0 ≤ᵐ[volume.prod volume]
      (fun z : Eucl d × Eucl d => gagliardoIntegrand G.κ (cut : L2 d) z) :=
    MeasureTheory.ae_of_all _ (fun z => gagliardoIntegrand_nonneg G.κ _ z)
  have henergy := hupper.mono_nonneg hmeas hnonneg hcutbound
  rw [mem_formDomain_iff]
  constructor
  · filter_upwards [indicatorL2_ae (G.wellRegion j) (G.wellRegion_measurable j) (ψ : L2 d)] with x hx
    intro hout
    change (cut : L2 d) x = 0
    simpa [cut, Set.indicator, hout] using hx
  · exact henergy

/-- The pieces of a finite-energy function on `Ω` have finite energy on `D`
(the cross-well kernel is bounded by positive separation). -/
theorem pieceL2_mem (j : ι) (ψ : formDomain G.κ G.Ω) :
    G.pieceL2 j (ψ : L2 d) ∈ formDomain G.κ G.D := by
  let b : Eucl d := G.L • G.a j
  let cut : L2 d := indicatorL2 (G.wellRegion j) (G.wellRegion_measurable j) (ψ : L2 d)
  have hcut := G.region_cut_mem j ψ
  have htr := translateL2_mem_formDomain G.κ (-b) hcut
  have hset : {x : Eucl d | x - (-b) ∈ G.wellRegion j} = G.D := by
    ext x
    simp [wellRegion, b, sub_eq_add_neg, add_assoc]
  have htr' : translateL2 (-b) cut ∈ formDomain G.κ G.D := by
    change translateL2 (-b) cut ∈
      formDomain G.κ {x : Eucl d | x - (-b) ∈ G.wellRegion j} at htr
    rw [hset] at htr
    exact htr
  have hcutAE : (cut : L2 d) =ᵐ[volume]
      (G.wellRegion j).indicator (fun x => (ψ : L2 d) x) := by
    dsimp [cut]
    exact indicatorL2_ae (G.wellRegion j) (G.wellRegion_measurable j) (ψ : L2 d)
  have hcutComp : (fun x : Eucl d => (cut : L2 d) (x + b)) =ᵐ[volume]
      fun x => (G.wellRegion j).indicator (fun x => (ψ : L2 d) x) (x + b) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      ((measurePreserving_sub_right (volume : Measure (Eucl d)) (-b))
        |>.quasiMeasurePreserving.ae_eq_comp hcutAE)
  have hpiece : ((G.pieceL2 j (ψ : L2 d) : L2 d) : Eucl d → ℝ) =ᵐ[volume]
      G.D.indicator (fun x => (translateL2 (-b) (ψ : L2 d) : L2 d) x) := by
    exact indicatorL2_ae G.D G.hDm _
  have htrfun := translateL2_ae (-b) cut
  have hshift : ∀ x, x + b ∈ G.wellRegion j ↔ x ∈ G.D := by
    intro x
    simp [wellRegion, b, sub_eq_add_neg, add_assoc]
  have heq : translateL2 (-b) cut = G.pieceL2 j (ψ : L2 d) := by
    apply Lp.ext
    filter_upwards [htrfun, hcutComp, hpiece, translateL2_ae (-b) (ψ : L2 d)] with x htrfun hcc hp hψ
    by_cases hx : x ∈ G.D
    · have hreg : x + b ∈ G.wellRegion j := (hshift x).2 hx
      calc
        (translateL2 (-b) cut : L2 d) x = (cut : L2 d) (x + b) := by
          have hh : x - (-b) = x + b := by abel
          rw [← hh]
          exact htrfun
        _ = (G.wellRegion j).indicator (fun y => (ψ : L2 d) y) (x + b) := hcc
        _ = (ψ : L2 d) (x + b) := by simp [Set.indicator, hreg]
        _ = (translateL2 (-b) (ψ : L2 d) : L2 d) x := by
          have hh : x - (-b) = x + b := by abel
          rw [← hh]
          exact hψ.symm
        _ = (G.pieceL2 j (ψ : L2 d) : L2 d) x := by
          rw [hp]
          simp [Set.indicator, hx]
    · have hreg : x + b ∉ G.wellRegion j := fun hh => hx ((hshift x).1 hh)
      calc
        (translateL2 (-b) cut : L2 d) x = (cut : L2 d) (x + b) := by
          have hh : x - (-b) = x + b := by abel
          rw [← hh]
          exact htrfun
        _ = (G.wellRegion j).indicator (fun y => (ψ : L2 d) y) (x + b) := hcc
        _ = 0 := by simp [Set.indicator, hreg]
        _ = (G.pieceL2 j (ψ : L2 d) : L2 d) x := by
          rw [hp]
          simp [Set.indicator, hx]
  rw [← heq]
  exact htr'



/-- The restriction map `ψ ↦ u_j`. -/
noncomputable def wellMap (j : ι) :
    formDomain G.κ G.Ω →ₗ[ℝ] formDomain G.κ G.D where
  toFun ψ := ⟨G.pieceL2 j (ψ : L2 d), G.pieceL2_mem j ψ⟩
  map_add' ψ χ := Subtype.ext (by simp)
  map_smul' t ψ := Subtype.ext (by simp)

@[simp] theorem wellMap_coe (j : ι) (ψ : formDomain G.κ G.Ω) :
    ((G.wellMap j ψ : formDomain G.κ G.D) : L2 d) = G.pieceL2 j (ψ : L2 d) :=
  rfl

/-- The decoupled form `Q₀[ψ] = Σ_j Q_D[u_j]`, i.e. the form of `𝒜₀`. -/
noncomputable def Q0 (c : ℝ) : QuadraticMap ℝ (formDomain G.κ G.Ω) ℝ :=
  ∑ j, (formQ c G.κ G.D).comp (G.wellMap j)

private theorem pieceInner_eq (j : ι) (ψ χ : formDomain G.κ G.Ω) :
    inner ℝ (G.pieceL2 j (ψ : L2 d)) (G.pieceL2 j (χ : L2 d)) =
      ∫ x in G.wellRegion j, ((ψ : L2 d) x) * ((χ : L2 d) x) := by
  let b : Eucl d := G.L • G.a j
  let u : Eucl d → ℝ := fun x => (ψ : L2 d) x
  let v : Eucl d → ℝ := fun x => (χ : L2 d) x
  let f : Eucl d → ℝ := fun x => u x * v x
  let h : Eucl d → ℝ := G.D.indicator (fun y => u (y+b) * v (y+b))
  have hψpiece : ((G.pieceL2 j (ψ : L2 d) : L2 d) : Eucl d → ℝ) =ᵐ[volume]
      G.D.indicator (fun x => (translateL2 (-b) (ψ : L2 d) : L2 d) x) := by
    exact indicatorL2_ae G.D G.hDm _
  have hχpiece : ((G.pieceL2 j (χ : L2 d) : L2 d) : Eucl d → ℝ) =ᵐ[volume]
      G.D.indicator (fun x => (translateL2 (-b) (χ : L2 d) : L2 d) x) := by
    exact indicatorL2_ae G.D G.hDm _
  have hψtr := translateL2_ae (-b) (ψ : L2 d)
  have hχtr := translateL2_ae (-b) (χ : L2 d)
  have hprod : (fun x : Eucl d =>
      (G.pieceL2 j (ψ : L2 d) : L2 d) x * (G.pieceL2 j (χ : L2 d) : L2 d) x) =ᵐ[volume] h := by
    filter_upwards [hψpiece, hχpiece, hψtr, hχtr] with x hp hq ht hu
    have hh : x - (-b) = x + b := by abel
    have ht' : (translateL2 (-b) (ψ : L2 d) : L2 d) x = u (x+b) := by
      rw [← hh]
      exact ht
    have hu' : (translateL2 (-b) (χ : L2 d) : L2 d) x = v (x+b) := by
      rw [← hh]
      exact hu
    by_cases hx : x ∈ G.D
    · have hp' : (G.pieceL2 j (ψ : L2 d) : L2 d) x = u (x+b) := by
        calc
          _ = G.D.indicator (fun z => (translateL2 (-b) (ψ : L2 d) : L2 d) z) x := hp
          _ = (translateL2 (-b) (ψ : L2 d) : L2 d) x := by simp [Set.indicator, hx]
          _ = u (x+b) := ht'
      have hq' : (G.pieceL2 j (χ : L2 d) : L2 d) x = v (x+b) := by
        calc
          _ = G.D.indicator (fun z => (translateL2 (-b) (χ : L2 d) : L2 d) z) x := hq
          _ = (translateL2 (-b) (χ : L2 d) : L2 d) x := by simp [Set.indicator, hx]
          _ = v (x+b) := hu'
      simp [h, Set.indicator, hx, hp', hq']
    · have hp' : (G.pieceL2 j (ψ : L2 d) : L2 d) x = 0 := by
        calc
          _ = G.D.indicator (fun z => (translateL2 (-b) (ψ : L2 d) : L2 d) z) x := hp
          _ = 0 := by simp [Set.indicator, hx]
      have hq' : (G.pieceL2 j (χ : L2 d) : L2 d) x = 0 := by
        calc
          _ = G.D.indicator (fun z => (translateL2 (-b) (χ : L2 d) : L2 d) z) x := hq
          _ = 0 := by simp [Set.indicator, hx]
      simp [h, Set.indicator, hx, hp', hq']
  have hmp := measurePreserving_sub_right (volume : Measure (Eucl d)) b
  have heq : (fun y : Eucl d => h (y - b)) =ᵐ[volume]
      fun y => (G.wellRegion j).indicator f y := by
    filter_upwards [] with y
    by_cases hy : y ∈ G.wellRegion j
    · have hyD : y - b ∈ G.D := by simpa [wellRegion, b] using hy
      simp [h, f, u, v, Set.indicator, hy, hyD, b, add_sub_cancel_right]
    · have hyD : y - b ∉ G.D := by
        simpa [wellRegion, b] using hy
      simp [h, f, u, v, Set.indicator, hy, hyD, b, add_sub_cancel_right]
  calc
    inner ℝ (G.pieceL2 j (ψ : L2 d)) (G.pieceL2 j (χ : L2 d)) =
        ∫ x, (G.pieceL2 j (ψ : L2 d) : L2 d) x *
          (G.pieceL2 j (χ : L2 d) : L2 d) x := by
          rw [MeasureTheory.L2.inner_def]
          simp only [Real.inner_apply]
    _ = ∫ x, h x := integral_congr_ae hprod
    _ = ∫ y, h (y - b) := by
          symm
          exact hmp.integral_comp' (f := MeasurableEquiv.subRight b) h
    _ = ∫ y, (G.wellRegion j).indicator f y := integral_congr_ae heq
    _ = ∫ y in G.wellRegion j, f y := integral_indicator (G.wellRegion_measurable j)
    _ = ∫ x in G.wellRegion j, ((ψ : L2 d) x) * ((χ : L2 d) x) := by rfl

/-- The identification `L²(Ω) ≅ ⊕_j L²(D)` is unitary. -/
theorem inner_eq_sum (ψ χ : formDomain G.κ G.Ω) :
    inner ℝ (ψ : L2 d) (χ : L2 d) =
      ∑ j, inner ℝ (G.pieceL2 j (ψ : L2 d)) (G.pieceL2 j (χ : L2 d)) := by
  let f : Eucl d → ℝ := fun x => ((ψ : L2 d) x) * ((χ : L2 d) x)
  have hf : Integrable f (volume : Measure (Eucl d)) := by
    have hi : Integrable
        (fun x : Eucl d => inner ℝ ((ψ : L2 d) x) ((χ : L2 d) x))
        (volume : Measure (Eucl d)) :=
      MeasureTheory.L2.integrable_inner (ψ : L2 d) (χ : L2 d)
    simpa [f, Real.inner_apply, mul_comm] using hi
  have hψmem := (mem_formDomain_iff G.κ G.Ω (ψ : L2 d)).mp ψ.property
  have hindicator : G.Ω.indicator f =ᵐ[volume] f := by
    filter_upwards [hψmem.1] with x hx
    by_cases hxΩ : x ∈ G.Ω
    · simp [Set.indicator, hxΩ]
    · simp [f, Set.indicator, hxΩ, hx hxΩ]
  have hΩm : MeasurableSet G.Ω := by
    rw [G.Ω_eq_iUnion]
    exact MeasurableSet.iUnion fun j => G.wellRegion_measurable j
  calc
    inner ℝ (ψ : L2 d) (χ : L2 d) = ∫ x, f x := by
      rw [MeasureTheory.L2.inner_def]
      simp only [Real.inner_apply]
      rfl
    _ = ∫ x, G.Ω.indicator f x := integral_congr_ae hindicator.symm
    _ = ∫ x in G.Ω, f x := integral_indicator hΩm
    _ = ∑ j, ∫ x in G.wellRegion j, f x := by
      rw [G.Ω_eq_iUnion]
      exact integral_iUnion_fintype
        (fun j => G.wellRegion_measurable j) G.wellRegion_pairwise
        (fun j => hf.integrableOn)
    _ = ∑ j, inner ℝ (G.pieceL2 j (ψ : L2 d)) (G.pieceL2 j (χ : L2 d)) := by
      apply Fintype.sum_congr
      intro j
      exact (G.pieceInner_eq j ψ χ).symm


theorem translate_mem_Ω (φ : formDomain G.κ G.D) (j : ι) :
    translateL2 (G.L • G.a j) (φ : L2 d) ∈ formDomain G.κ G.Ω := by
  have htrans := translateL2_mem_formDomain G.κ (G.L • G.a j) φ.property
  apply formDomain_mono (κ := G.κ) (A := {x | x - G.L • G.a j ∈ G.D})
    (B := G.Ω) ?_ htrans
  intro x hx
  exact ⟨j, hx⟩

/-- The translated ground-state vectors `Φ_j = τ_{L a_j} φ`. -/
noncomputable def Φ (φ : formDomain G.κ G.D) (j : ι) : formDomain G.κ G.Ω :=
  ⟨translateL2 (G.L • G.a j) (φ : L2 d), G.translate_mem_Ω φ j⟩

theorem pieceL2_Φ (φ : formDomain G.κ G.D) (i j : ι) :
    G.pieceL2 i ((G.Φ φ j : formDomain G.κ G.Ω) : L2 d) =
      if i = j then (φ : L2 d) else 0 := by
  classical
  let bi : Eucl d := G.L • G.a i
  let bj : Eucl d := G.L • G.a j
  let q : L2 d := translateL2 (-bi) (translateL2 bj (φ : L2 d))
  have hqae : (q : L2 d) =ᵐ[volume]
      fun x => (φ : L2 d) (x - (bj - bi)) := by
    have houter := translateL2_ae (-bi) (translateL2 bj (φ : L2 d))
    have hinner : (fun x : Eucl d => (translateL2 bj (φ : L2 d) : L2 d) (x - (-bi))) =ᵐ[volume]
        fun x => (φ : L2 d) ((x - (-bi)) - bj) := by
      simpa [Function.comp_def] using
        ((measurePreserving_sub_right (volume : Measure (Eucl d)) (-bi))
          |>.quasiMeasurePreserving.ae_eq_comp (translateL2_ae bj (φ : L2 d)))
    filter_upwards [houter, hinner] with x h1 h2
    have harg : (x - (-bi)) - bj = x - (bj - bi) := by abel
    calc
      (q : L2 d) x = (translateL2 bj (φ : L2 d) : L2 d) (x - (-bi)) := h1
      _ = (φ : L2 d) ((x - (-bi)) - bj) := h2
      _ = (φ : L2 d) (x - (bj - bi)) := by rw [harg]
  by_cases hij : i = j
  · subst j
    have hq : q = (φ : L2 d) := by
      dsimp [q, bi, bj]
      exact translateL2_neg_translateL2 (G.L • G.a i) (φ : L2 d)
    have hvanish : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → (φ : L2 d) x = 0 :=
      φ.property.1
    have hpiece : G.pieceL2 i ((G.Φ φ i : formDomain G.κ G.Ω) : L2 d) =
        indicatorL2 G.D G.hDm q := by
      rfl
    rw [hpiece, hq]
    simpa using indicatorL2_of_ae_zero G.D G.hDm (φ : L2 d) hvanish
  · have hphi : ∀ᵐ y ∂(volume : Measure (Eucl d)),
      y ∉ G.D → (φ : L2 d) y = 0 := φ.property.1
    have hpull : ∀ᵐ x ∂(volume : Measure (Eucl d)),
        x - (bj - bi) ∉ G.D → (φ : L2 d) (x - (bj - bi)) = 0 :=
      (measurePreserving_sub_right (volume : Measure (Eucl d)) (bj-bi))
        |>.quasiMeasurePreserving.ae hphi
    have hzero : ∀ᵐ x ∂(volume : Measure (Eucl d)),
        x ∈ G.D → (q : L2 d) x = 0 := by
      filter_upwards [hpull, hqae] with x hp hq
      intro hx
      have harg : x - (bj - bi) ∉ G.D := by
        intro hy
        have hxR : ‖x‖ < G.R := by
          have h := G.hDR hx
          simpa [Metric.mem_ball, dist_eq_norm] using h
        have hyR : ‖x - (bj - bi)‖ < G.R := by
          have h := G.hDR hy
          simpa [Metric.mem_ball, dist_eq_norm] using h
        have hcenter : 4 * G.R ≤ ‖bj - bi‖ := by
          dsimp [bj, bi]
          rw [show G.L • G.a j - G.L • G.a i = G.L • (G.a j - G.a i) by rw [smul_sub]]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos G.hL]
          exact G.hsep j i (Ne.symm hij)
        have hxy : ‖x - (x - (bj - bi))‖ ≤ ‖x‖ + ‖x - (bj - bi)‖ :=
          norm_sub_le _ _
        have hdist : ‖bj - bi‖ ≤ ‖x‖ + ‖x - (bj - bi)‖ := by
          calc
            ‖bj - bi‖ = ‖x - (x - (bj - bi))‖ := by congr 1 <;> abel
            _ ≤ ‖x‖ + ‖x - (bj - bi)‖ := norm_sub_le _ _
        nlinarith [hcenter, hxR, hyR, G.hR]
      rw [hq]
      exact hp harg
    have hpiece : G.pieceL2 i ((G.Φ φ j : formDomain G.κ G.Ω) : L2 d) =
        indicatorL2 G.D G.hDm q := by
      rfl
    simp only [if_neg hij]
    rw [hpiece]
    apply Lp.ext
    filter_upwards [indicatorL2_ae G.D G.hDm q, hzero] with x hp hz
    rw [hp]
    by_cases hx : x ∈ G.D
    · simp [Set.indicator, hx, hz hx]
    · simp [Set.indicator, hx]


/-- The kernel pairing between wells `i` and `j`:
`∬ u(x) v(y) |L(a_i - a_j) + x - y|^{-κ} dx dy`. -/
noncomputable def crossPair (i j : ι) (u v : L2 d) : ℝ :=
  kernelCrossPairing (multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)))
    (volume : Measure (Eucl d)) (u : Eucl d → ℝ) (v : Eucl d → ℝ)


private theorem l1_of_supported_closedBall (f : L2 d) (center : Eucl d) (r : ℝ)
    (hsupp : ∀ᵐ x ∂(volume : Measure (Eucl d)),
      x ∉ Metric.closedBall center r → f x = 0) :
    Integrable (fun x : Eucl d => f x) (volume : Measure (Eucl d)) := by
  let E : Set (Eucl d) := Metric.closedBall center r
  have hmem : MemLp (fun x : Eucl d => f x) 2 ((volume : Measure (Eucl d)).restrict E) :=
    (Lp.memLp f).restrict E
  have hfin : (volume : Measure (Eucl d)) E ≠ ⊤ := by
    simpa [E] using
      (measure_closedBall_lt_top (μ := (volume : Measure (Eucl d)))
        (x := center) (r := r)).ne
  letI : IsFiniteMeasure ((volume : Measure (Eucl d)).restrict E) :=
    isFiniteMeasure_restrict.mpr hfin
  have hint : Integrable (fun x : Eucl d => f x)
      ((volume : Measure (Eucl d)).restrict E) :=
    MemLp.integrable (by norm_num) hmem
  have hind : Integrable (E.indicator (fun x : Eucl d => f x))
      (volume : Measure (Eucl d)) :=
    (integrable_indicator_iff
      (show MeasurableSet E from Metric.isClosed_closedBall.measurableSet)).2 hint
  have heq : E.indicator (fun x : Eucl d => f x) =ᵐ[volume] fun x => f x := by
    filter_upwards [hsupp] with x hx
    by_cases hxe : x ∈ E
    · simp [Set.indicator, hxe]
    · simp [Set.indicator, hxe, hx hxe]
  exact hind.congr heq

private theorem crossKernel_aestronglyMeasurable (i j : ι) :
    AEStronglyMeasurable
      (fun z : Eucl d × Eucl d =>
        multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2)
      ((volume : Measure (Eucl d)).prod volume) := by
  let c : Eucl d := G.L • (G.a i - G.a j)
  have hmap : Measurable (fun z : Eucl d × Eucl d => (c + z.1, z.2)) := by fun_prop
  have hm := (measurable_gagliardoKernel G.κ).comp hmap
  have heq : (fun z : Eucl d × Eucl d =>
      multiWellCrossKernel G.κ c z.1 z.2) =
      (fun z => gagliardoKernel G.κ (c + z.1) z.2) := by
    funext z
    simp [multiWellCrossKernel, gagliardoKernel]
  rw [heq]
  exact hm.aestronglyMeasurable

private theorem crossKernel_bound (i j : ι) (hij : i ≠ j)
    {x y : Eucl d} (hx : x ∈ G.D) (hy : y ∈ G.D) :
    |multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) x y| ≤
      (2 * G.R) ^ (-G.κ) := by
  let bi : Eucl d := G.L • G.a i
  let bj : Eucl d := G.L • G.a j
  have hxi : x + bi ∈ G.wellRegion i := by
    change x + bi - G.L • G.a i ∈ G.D
    simpa [bi] using hx
  have hyj : y + bj ∈ G.wellRegion j := by
    change y + bj - G.L • G.a j ∈ G.D
    simpa [bj] using hy
  have hdist := G.wellRegion_dist i j hij hxi hyj
  have hk := G.kernel_le_of_dist hdist
  have hcenter : G.L • (G.a i - G.a j) = bi - bj := by
    dsimp [bi, bj]
    rw [smul_sub]
  have heq : multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) x y =
      gagliardoKernel G.κ (x + bi) (y + bj) := by
    unfold multiWellCrossKernel gagliardoKernel
    rw [hcenter]
    congr 1
    abel
  calc
    |multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) x y| =
        |gagliardoKernel G.κ (x + bi) (y + bj)| := by rw [heq]
    _ = gagliardoKernel G.κ (x + bi) (y + bj) :=
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    _ ≤ (2 * G.R) ^ (-G.κ) := hk

private theorem crossPair_integrable_supported (i j : ι) (hij : i ≠ j)
    (u v : L2 d)
    (hu : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → u x = 0)
    (hv : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → v x = 0) :
    Integrable
      (fun z : Eucl d × Eucl d =>
        (u : Eucl d → ℝ) z.1 * (v : Eucl d → ℝ) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2)
      ((volume : Measure (Eucl d)).prod volume) := by
  let C : ℝ := (2 * G.R) ^ (-G.κ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg (by nlinarith [G.hR]) _
  have huL1 : Integrable (fun x : Eucl d => (u : L2 d) x) (volume : Measure (Eucl d)) :=
    l1_of_supported_closedBall u 0 G.R (by
      filter_upwards [hu] with x hx
      intro hball
      apply hx
      intro hD
      exact hball (Metric.ball_subset_closedBall (G.hDR hD)))
  have hvL1 : Integrable (fun x : Eucl d => (v : L2 d) x) (volume : Measure (Eucl d)) :=
    l1_of_supported_closedBall v 0 G.R (by
      filter_upwards [hv] with x hx
      intro hball
      apply hx
      intro hD
      exact hball (Metric.ball_subset_closedBall (G.hDR hD)))
  have hprod := huL1.abs.mul_prod hvL1.abs
  have hufst := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae hu
  have hvsnd := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae hv
  have hbound : ∀ᵐ z : Eucl d × Eucl d ∂(volume.prod volume),
      ‖(u : Eucl d → ℝ) z.1 * (v : Eucl d → ℝ) z.2 *
        multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2‖ ≤
          C * (|(u : Eucl d → ℝ) z.1| * |(v : Eucl d → ℝ) z.2|) := by
    filter_upwards [hufst, hvsnd] with z hu' hv'
    rcases z with ⟨x,y⟩
    by_cases hx : x ∈ G.D
    · by_cases hy : y ∈ G.D
      · have hk := G.crossKernel_bound i j hij hx hy
        have hfac : 0 ≤ |(u : L2 d) x| * |(v : L2 d) y| :=
          mul_nonneg (abs_nonneg ((u : L2 d) x)) (abs_nonneg ((v : L2 d) y))
        have hmul := mul_le_mul_of_nonneg_left hk hfac
        calc
          ‖(u : L2 d) x * (v : L2 d) y *
              multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) x y‖ =
              |(u : L2 d) x| * |(v : L2 d) y| *
                |multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) x y| := by
                  simp [Real.norm_eq_abs, abs_mul]
          _ ≤ (|(u : L2 d) x| * |(v : L2 d) y|) * C := by simpa [C] using hmul
          _ = C * (|(u : L2 d) x| * |(v : L2 d) y|) := by ring
      · have hv0 := hv' hy
        simp [hv0, C]
    · have hu0 := hu' hx
      simp [hu0, C]
  have hmeasu : AEStronglyMeasurable (fun z : Eucl d × Eucl d => (u : L2 d) z.1)
      (volume.prod volume) := (Lp.aestronglyMeasurable u).comp_fst
  have hmeasv : AEStronglyMeasurable (fun z : Eucl d × Eucl d => (v : L2 d) z.2)
      (volume.prod volume) := (Lp.aestronglyMeasurable v).comp_snd
  have hK := G.crossKernel_aestronglyMeasurable i j
  have hmeas := (hmeasu.mul hmeasv).mul hK
  have hint := (hprod.const_mul C).mono' hmeas hbound
  change Integrable
    (fun z : Eucl d × Eucl d =>
      (u : L2 d) z.1 * (v : L2 d) z.2 *
        multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2)
    (volume.prod volume) at hint
  exact hint


private theorem crossPair_add_right_supported (i j : ι) (hij : i ≠ j)
    (u v v' : L2 d)
    (hu : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → u x = 0)
    (hv : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → v x = 0)
    (hv' : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → v' x = 0) :
    G.crossPair i j u (v + v') =
      G.crossPair i j u v + G.crossPair i j u v' := by
  have hsum : ∀ᵐ x ∂(volume : Measure (Eucl d)),
      x ∉ G.D → (v + v') x = 0 := by
    filter_upwards [Lp.coeFn_add v v', hv, hv'] with x hadd h1 h2
    intro hx
    rw [hadd]
    change v x + v' x = 0
    rw [h1 hx, h2 hx]
    ring
  have h1 := G.crossPair_integrable_supported i j hij u v hu hv
  have h2 := G.crossPair_integrable_supported i j hij u v' hu hv'
  have hrep0 := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae_eq_comp
      (Lp.coeFn_add v v')
  have hrep : (fun z : Eucl d × Eucl d => (v + v') z.2) =ᵐ[volume.prod volume]
      fun z => v z.2 + v' z.2 := by
    filter_upwards [hrep0] with z hz
    simpa only [Function.comp_apply, Pi.add_apply] using hz
  simp only [crossPair, kernelCrossPairing]
  calc
    (∫ z : Eucl d × Eucl d,
        (u : L2 d) z.1 * (v + v' : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2
          ∂(volume.prod volume)) =
      ∫ z : Eucl d × Eucl d,
        (u : L2 d) z.1 * (v z.2 + v' z.2) *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2
          ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards [hrep] with z hz
        rw [hz]
    _ = ∫ z : Eucl d × Eucl d,
        ((u : L2 d) z.1 * v z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2) +
        ((u : L2 d) z.1 * v' z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2)
          ∂(volume.prod volume) := by
        apply integral_congr_ae
        exact MeasureTheory.ae_of_all _ (fun z => by ring)
    _ = _ := MeasureTheory.integral_add h1 h2

private theorem crossPair_smul_left (i j : ι) (t : ℝ) (u v : L2 d) :
    G.crossPair i j (t • u) v = t * G.crossPair i j u v := by
  have hrep0 := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae_eq_comp
      (Lp.coeFn_smul t u)
  have hrep : (fun z : Eucl d × Eucl d => (t • u) z.1) =ᵐ[volume.prod volume]
      fun z => t * u z.1 := by
    filter_upwards [hrep0] with z hz
    simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hz
  simp only [crossPair, kernelCrossPairing]
  calc
    (∫ z : Eucl d × Eucl d,
        (t • u : L2 d) z.1 * (v : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2
          ∂(volume.prod volume)) =
      ∫ z : Eucl d × Eucl d,
        t * (u z.1 * (v : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2)
          ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards [hrep] with z hz
        rw [hz]
        ring
    _ = t * ∫ z : Eucl d × Eucl d,
        u z.1 * (v : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2
          ∂(volume.prod volume) := MeasureTheory.integral_const_mul t _

private theorem crossPair_smul_right (i j : ι) (t : ℝ) (u v : L2 d) :
    G.crossPair i j u (t • v) = t * G.crossPair i j u v := by
  have hrep0 := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae_eq_comp
      (Lp.coeFn_smul t v)
  have hrep : (fun z : Eucl d × Eucl d => (t • v) z.2) =ᵐ[volume.prod volume]
      fun z => t * v z.2 := by
    filter_upwards [hrep0] with z hz
    simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hz
  simp only [crossPair, kernelCrossPairing]
  calc
    (∫ z : Eucl d × Eucl d,
        (u : L2 d) z.1 * (t • v : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2
          ∂(volume.prod volume)) =
      ∫ z : Eucl d × Eucl d,
        t * ((u : L2 d) z.1 * v z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2)
          ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards [hrep] with z hz
        rw [hz]
        ring
    _ = t * ∫ z : Eucl d × Eucl d,
        (u : L2 d) z.1 * v z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2
          ∂(volume.prod volume) := MeasureTheory.integral_const_mul t _

private theorem crossPair_add_left_supported (i j : ι) (hij : i ≠ j)
    (u u' v : L2 d)
    (hu : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → u x = 0)
    (hu' : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → u' x = 0)
    (hv : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D → v x = 0) :
    G.crossPair i j (u + u') v =
      G.crossPair i j u v + G.crossPair i j u' v := by
  have hsum : ∀ᵐ x ∂(volume : Measure (Eucl d)),
      x ∉ G.D → (u + u') x = 0 := by
    filter_upwards [Lp.coeFn_add u u', hu, hu'] with x hadd h1 h2
    intro hx
    rw [hadd]
    change (u x + u' x) = 0
    rw [h1 hx, h2 hx]
    ring
  have h1 := G.crossPair_integrable_supported i j hij u v hu hv
  have h2 := G.crossPair_integrable_supported i j hij u' v hu' hv
  have hrep0 := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae_eq_comp
      (Lp.coeFn_add u u')
  have hrep : (fun z : Eucl d × Eucl d => (u + u') z.1) =ᵐ[volume.prod volume]
      fun z => u z.1 + u' z.1 := by
    filter_upwards [hrep0] with z hz
    simpa only [Function.comp_apply, Pi.add_apply] using hz
  simp only [crossPair, kernelCrossPairing]
  calc
    (∫ z : Eucl d × Eucl d,
        (u + u' : L2 d) z.1 * (v : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2
          ∂(volume.prod volume)) =
      ∫ z : Eucl d × Eucl d,
        (u z.1 + u' z.1) * (v : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2
          ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards [hrep] with z hz
        rw [hz]
    _ = ∫ z : Eucl d × Eucl d,
        (u z.1 * (v : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2) +
        (u' z.1 * (v : L2 d) z.2 *
          multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)) z.1 z.2)
          ∂(volume.prod volume) := by
        apply integral_congr_ae
        exact MeasureTheory.ae_of_all _ (fun z => by ring)
    _ = _ := MeasureTheory.integral_add h1 h2

/-- The scalar interaction `w(ψ, χ)` before bilinearity is recorded. -/
noncomputable def interactionFun (c : ℝ) (ψ χ : formDomain G.κ G.Ω) : ℝ :=
  -c * ∑ i, ∑ j, if i = j then (0 : ℝ) else
    G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))

private theorem pieceL2_supported (i : ι) (f : L2 d) :
    ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ G.D →
      (G.pieceL2 i f : Eucl d → ℝ) x = 0 := by
  filter_upwards [indicatorL2_ae G.D G.hDm
    (translateL2 (-(G.L • G.a i)) f)] with x hx
  intro hnot
  change (indicatorL2 G.D G.hDm (translateL2 (-(G.L • G.a i)) f) : L2 d) x = 0
  simpa [Set.indicator, hnot] using hx

private theorem pieceL2_add (i : ι) (ψ ψ' : formDomain G.κ G.Ω) :
    G.pieceL2 i ((ψ + ψ' : formDomain G.κ G.Ω) : L2 d) =
      G.pieceL2 i (ψ : L2 d) + G.pieceL2 i (ψ' : L2 d) := by
  change G.pieceL2 i ((ψ : L2 d) + (ψ' : L2 d)) = _
  exact map_add (G.pieceL2 i) _ _

theorem interactionFun_add_left (c : ℝ) (ψ ψ' χ : formDomain G.κ G.Ω) :
    G.interactionFun c (ψ + ψ') χ =
      G.interactionFun c ψ χ + G.interactionFun c ψ' χ := by
  let A (ξ η : formDomain G.κ G.Ω) (i j : ι) : ℝ :=
    if i = j then 0 else
      G.crossPair i j (G.pieceL2 i (ξ : L2 d)) (G.pieceL2 j (η : L2 d))
  have hterm (i j : ι) :
      A (ψ + ψ') χ i j = A ψ χ i j + A ψ' χ i j := by
    by_cases hij : i = j
    · simp [A, hij]
    · simp only [A, if_neg hij]
      rw [G.pieceL2_add]
      exact G.crossPair_add_left_supported i j hij
        (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 i (ψ' : L2 d))
        (G.pieceL2 j (χ : L2 d))
        (G.pieceL2_supported i (ψ : L2 d))
        (G.pieceL2_supported i (ψ' : L2 d))
        (G.pieceL2_supported j (χ : L2 d))
  have hsum :
      (∑ i, ∑ j, A (ψ + ψ') χ i j) =
        (∑ i, ∑ j, A ψ χ i j) + (∑ i, ∑ j, A ψ' χ i j) := by
    calc
      (∑ i, ∑ j, A (ψ + ψ') χ i j) =
          ∑ i, ∑ j, (A ψ χ i j + A ψ' χ i j) := by
        apply Fintype.sum_congr
        intro i
        apply Fintype.sum_congr
        intro j
        exact hterm i j
      _ = _ := by simp_rw [Finset.sum_add_distrib]
  unfold interactionFun
  change -c * (∑ i, ∑ j, A (ψ + ψ') χ i j) =
    (-c * (∑ i, ∑ j, A ψ χ i j)) + (-c * (∑ i, ∑ j, A ψ' χ i j))
  rw [hsum]
  ring



private theorem pieceL2_smul (i : ι) (t : ℝ) (ψ : formDomain G.κ G.Ω) :
    G.pieceL2 i ((t • ψ : formDomain G.κ G.Ω) : L2 d) =
      t • G.pieceL2 i (ψ : L2 d) := by
  change G.pieceL2 i (t • (ψ : L2 d)) = _
  exact map_smul (G.pieceL2 i) t (ψ : L2 d)

theorem interactionFun_smul_left (c : ℝ) (t : ℝ) (ψ χ : formDomain G.κ G.Ω) :
    G.interactionFun c (t • ψ) χ = t • G.interactionFun c ψ χ := by
  let A (ξ η : formDomain G.κ G.Ω) (i j : ι) : ℝ :=
    if i = j then 0 else
      G.crossPair i j (G.pieceL2 i (ξ : L2 d)) (G.pieceL2 j (η : L2 d))
  have hterm (i j : ι) :
      A (t • ψ) χ i j = t * A ψ χ i j := by
    by_cases hij : i = j
    · simp [A, hij]
    · simp only [A, if_neg hij]
      rw [G.pieceL2_smul]
      exact G.crossPair_smul_left i j t
        (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))
  have hsum :
      (∑ i, ∑ j, A (t • ψ) χ i j) =
        t * (∑ i, ∑ j, A ψ χ i j) := by
    calc
      (∑ i, ∑ j, A (t • ψ) χ i j) =
          ∑ i, ∑ j, t * A ψ χ i j := by
        apply Fintype.sum_congr
        intro i
        apply Fintype.sum_congr
        intro j
        exact hterm i j
      _ = t * (∑ i, ∑ j, A ψ χ i j) := by
        simp_rw [← Finset.mul_sum]
  simp only [interactionFun, smul_eq_mul]
  change -c * (∑ i, ∑ j, A (t • ψ) χ i j) =
    t * (-c * (∑ i, ∑ j, A ψ χ i j))
  rw [hsum]
  ring

theorem interactionFun_add_right (c : ℝ) (ψ χ χ' : formDomain G.κ G.Ω) :
    G.interactionFun c ψ (χ + χ') =
      G.interactionFun c ψ χ + G.interactionFun c ψ χ' := by
  let A (ξ η : formDomain G.κ G.Ω) (i j : ι) : ℝ :=
    if i = j then 0 else
      G.crossPair i j (G.pieceL2 i (ξ : L2 d)) (G.pieceL2 j (η : L2 d))
  have hterm (i j : ι) :
      A ψ (χ + χ') i j = A ψ χ i j + A ψ χ' i j := by
    by_cases hij : i = j
    · simp [A, hij]
    · simp only [A, if_neg hij]
      rw [G.pieceL2_add]
      exact G.crossPair_add_right_supported i j hij
        (G.pieceL2 i (ψ : L2 d))
        (G.pieceL2 j (χ : L2 d)) (G.pieceL2 j (χ' : L2 d))
        (G.pieceL2_supported i (ψ : L2 d))
        (G.pieceL2_supported j (χ : L2 d))
        (G.pieceL2_supported j (χ' : L2 d))
  have hsum :
      (∑ i, ∑ j, A ψ (χ + χ') i j) =
        (∑ i, ∑ j, A ψ χ i j) + (∑ i, ∑ j, A ψ χ' i j) := by
    calc
      (∑ i, ∑ j, A ψ (χ + χ') i j) =
          ∑ i, ∑ j, (A ψ χ i j + A ψ χ' i j) := by
        apply Fintype.sum_congr
        intro i
        apply Fintype.sum_congr
        intro j
        exact hterm i j
      _ = _ := by simp_rw [Finset.sum_add_distrib]
  unfold interactionFun
  change -c * (∑ i, ∑ j, A ψ (χ + χ') i j) =
    -c * (∑ i, ∑ j, A ψ χ i j) + -c * (∑ i, ∑ j, A ψ χ' i j)
  rw [hsum]
  ring

theorem interactionFun_smul_right (c : ℝ) (t : ℝ) (ψ χ : formDomain G.κ G.Ω) :
    G.interactionFun c ψ (t • χ) = t • G.interactionFun c ψ χ := by
  let A (ξ η : formDomain G.κ G.Ω) (i j : ι) : ℝ :=
    if i = j then 0 else
      G.crossPair i j (G.pieceL2 i (ξ : L2 d)) (G.pieceL2 j (η : L2 d))
  have hterm (i j : ι) :
      A ψ (t • χ) i j = t * A ψ χ i j := by
    by_cases hij : i = j
    · simp [A, hij]
    · simp only [A, if_neg hij]
      rw [G.pieceL2_smul]
      exact G.crossPair_smul_right i j t
        (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))
  have hsum :
      (∑ i, ∑ j, A ψ (t • χ) i j) =
        t * (∑ i, ∑ j, A ψ χ i j) := by
    calc
      (∑ i, ∑ j, A ψ (t • χ) i j) =
          ∑ i, ∑ j, t * A ψ χ i j := by
        apply Fintype.sum_congr
        intro i
        apply Fintype.sum_congr
        intro j
        exact hterm i j
      _ = t * (∑ i, ∑ j, A ψ χ i j) := by
        simp_rw [← Finset.mul_sum]
  simp only [interactionFun, smul_eq_mul]
  change -c * (∑ i, ∑ j, A ψ (t • χ) i j) =
    t * (-c * (∑ i, ∑ j, A ψ χ i j))
  rw [hsum]
  ring


noncomputable def interaction (c : ℝ) :
    LinearMap.BilinForm ℝ (formDomain G.κ G.Ω) :=
  LinearMap.mk₂ ℝ (G.interactionFun c) (G.interactionFun_add_left c)
    (G.interactionFun_smul_left c) (G.interactionFun_add_right c)
    (G.interactionFun_smul_right c)

theorem interaction_apply (c : ℝ) (ψ χ : formDomain G.κ G.Ω) :
    G.interaction c ψ χ = G.interactionFun c ψ χ :=
  rfl

theorem isOpen_Ω (hDo : IsOpen G.D) : IsOpen G.Ω := by
  rw [G.Ω_eq_iUnion]
  exact isOpen_iUnion fun j => hDo.preimage (continuous_id.sub continuous_const)

theorem Ω_nonempty [Nonempty ι] (hDne : G.D.Nonempty) : G.Ω.Nonempty := by
  obtain ⟨x, hx⟩ := hDne
  let j : ι := Classical.choice ‹Nonempty ι›
  refine ⟨x + G.L • G.a j, ?_⟩
  refine ⟨j, ?_⟩
  simpa using hx

end WellGeometry
end Tunneling

