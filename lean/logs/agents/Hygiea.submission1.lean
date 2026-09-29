import Tunneling.Euclid.CellAverage

/-!
# Compactness of the form embedding on bounded sets

For a bounded set `D ⊆ ℝ^d`, bounded subsets of `H^s_0(D)` are relatively
compact in `L²(ℝ^d)`.  This replaces the citation
[DiNezzaPalatucciValdinoci2012, Theorem 7.1] in paper Section 2 and is proved
by averaging over cubes of side `ε`: on a cube `Q` of diameter `√d ε`,

  `∫_Q |u - ⨍_Q u|² = (2|Q|)⁻¹ ∬_{Q×Q} |u(x)-u(y)|²
                     ≤ (√d ε)^κ (2 ε^d)⁻¹ ∬_{Q×Q} |u(x)-u(y)|² |x-y|^{-κ}`,

so the cube-average projection, whose range is finite dimensional on
functions supported in a bounded set, approximates `u` within
`C ε^s [u]`.  Lower semicontinuity of the Gagliardo energy follows from Fatou's
lemma along an a.e. convergent subsequence.
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- Energy-bounded subsets of `H^s_0(D)` are totally bounded in `L²`. -/
theorem totallyBounded_energySublevel (s : ℝ) (hs : 0 < s ∧ s < 1)
    (R : ℝ) (D : Set (Eucl d)) (hDR : D ⊆ Metric.closedBall 0 R) (M : ℝ) :
    TotallyBounded {f : L2 d | f ∈ formDomain ((d : ℝ) + 2 * s) D ∧ ‖f‖ ≤ 1 ∧
      gagliardoSeminormSq ((d : ℝ) + 2 * s) (volume : Measure (Eucl d))
        (f : Eucl d → ℝ) ≤ M} := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨S, hSfin, happrox⟩ :=
    exists_finiteDimensional_approx s hs R D hDR M (ε / 2) (by linarith)
  let K : Set (L2 d) := {p | p ∈ S ∧ ‖p‖ ≤ 1}
  have hK_eq : K = ((fun q : S => (q : L2 d)) '' Metric.closedBall (0 : S) 1) := by
    ext p
    constructor
    · rintro ⟨hpS, hpnorm⟩
      refine ⟨⟨p, hpS⟩, ?_, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hpnorm
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.property, ?_⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hq
  have hKcompact : IsCompact K := by
    letI : FiniteDimensional ℝ S := hSfin
    rw [hK_eq]
    exact (isCompact_closedBall (0 : S) 1).image continuous_subtype_val
  obtain ⟨t, htfin, htcover⟩ :=
    Metric.totallyBounded_iff.mp hKcompact.totallyBounded (ε / 2) (by linarith)
  refine ⟨t, htfin, ?_⟩
  intro f hf
  obtain ⟨p, hpS, hpnorm, hfp⟩ := happrox f hf.1 hf.2.1 hf.2.2
  have hpK : p ∈ K := ⟨hpS, hpnorm⟩
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (htcover hpK)
  obtain ⟨hct, hball⟩ := Set.mem_iUnion.mp hc
  refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hct, ?_⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have htri : dist f c ≤ dist f p + dist p c := dist_triangle f p c
  rw [dist_eq_norm] at htri hfp
  have hpball : dist p c < ε / 2 := Metric.mem_ball.mp hball
  linarith

/-- Every energy-bounded sequence in `H^s_0(D)` has an `L²`-convergent
subsequence. -/
theorem exists_tendsto_subseq (s : ℝ) (hs : 0 < s ∧ s < 1)
    (R : ℝ) (D : Set (Eucl d)) (hDR : D ⊆ Metric.closedBall 0 R)
    (f : ℕ → L2 d) (hf : ∀ n, f n ∈ formDomain ((d : ℝ) + 2 * s) D)
    (hnorm : ∀ n, ‖f n‖ ≤ 1) (M : ℝ)
    (hM : ∀ n, gagliardoSeminormSq ((d : ℝ) + 2 * s) (volume : Measure (Eucl d))
      (f n : Eucl d → ℝ) ≤ M) :
    ∃ g : L2 d, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => f (φ n)) Filter.atTop (nhds g) := by
  let A : Set (L2 d) := {u | u ∈ formDomain ((d : ℝ) + 2 * s) D ∧ ‖u‖ ≤ 1 ∧
    gagliardoSeminormSq ((d : ℝ) + 2 * s) (volume : Measure (Eucl d))
      (u : Eucl d → ℝ) ≤ M}
  have hA : TotallyBounded A := totallyBounded_energySublevel s hs R D hDR M
  have hcl : IsCompact (closure A) :=
    (totallyBounded_closure.mpr hA).isCompact_of_isClosed isClosed_closure
  have hfA : ∀ n, f n ∈ closure A := fun n => subset_closure ⟨hf n, hnorm n, hM n⟩
  obtain ⟨g, -, φ, hφ, hconv⟩ := hcl.tendsto_subseq hfA
  exact ⟨g, φ, hφ, hconv⟩

/-- Lower semicontinuity of the Gagliardo energy and closedness of the
zero-exterior condition under `L²` convergence. -/
theorem mem_formDomain_of_tendsto (κ : ℝ) (D : Set (Eucl d))
    (f : ℕ → L2 d) (g : L2 d) (hf : ∀ n, f n ∈ formDomain κ D)
    (hlim : Filter.Tendsto f Filter.atTop (nhds g)) (a : ℝ)
    (ha : ∀ᶠ n in Filter.atTop,
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f n : Eucl d → ℝ) ≤ a) :
    g ∈ formDomain κ D ∧
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (g : Eucl d → ℝ) ≤ a := by
  classical
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have hmeasure : TendstoInMeasure (volume : Measure (Eucl d))
      (fun n => (f n : Eucl d → ℝ)) Filter.atTop (g : Eucl d → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp hlim
  obtain ⟨ψ, hψmono, hψae⟩ := hmeasure.exists_seq_tendsto_ae
  have hzeros : ∀ᵐ x ∂(volume : Measure (Eucl d)), ∀ n,
      x ∉ D → (f (ψ n) : Eucl d → ℝ) x = 0 := by
    apply ae_all_iff.2
    intro n
    exact (mem_formDomain_iff κ D (f (ψ n))).mp (hf (ψ n)) |>.1
  have hzeroG : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ D → (g : Eucl d → ℝ) x = 0 := by
    filter_upwards [hzeros, hψae] with x hxzero hxlim
    intro hxD
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
    have hseqzero : (fun n => (f (ψ n) : Eucl d → ℝ) x) = fun _ => (0 : ℝ) := by
      funext n
      exact hxzero n hxD
    rw [hseqzero] at hxlim
    exact tendsto_nhds_unique hxlim hconst
  let F : ℕ → Eucl d × Eucl d → ENNReal := fun n z =>
    ENNReal.ofReal (gagliardoIntegrand κ (f (ψ n) : Eucl d → ℝ) z)
  let G : Eucl d × Eucl d → ENNReal := fun z =>
    ENNReal.ofReal (gagliardoIntegrand κ (g : Eucl d → ℝ) z)
  have hK : AEStronglyMeasurable
      (fun z : Eucl d × Eucl d => gagliardoKernel κ z.1 z.2)
      ((volume : Measure (Eucl d)).prod volume) :=
    gagliardoKernel_aestronglyMeasurable κ (volume : Measure (Eucl d))
  have hFmeas : ∀ n, AEMeasurable (F n) ((volume : Measure (Eucl d)).prod volume) := by
    intro n
    dsimp [F]
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (gagliardoIntegrand_aestronglyMeasurable κ (volume : Measure (Eucl d)) hK
        (Lp.aestronglyMeasurable _)).aemeasurable
  have hGmeas : AEMeasurable G ((volume : Measure (Eucl d)).prod volume) := by
    dsimp [G]
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (gagliardoIntegrand_aestronglyMeasurable κ (volume : Measure (Eucl d)) hK
        (Lp.aestronglyMeasurable _)).aemeasurable
  have hfst : ∀ᵐ z : Eucl d × Eucl d ∂(volume : Measure (Eucl d)).prod volume,
      Tendsto (fun i => (f (ψ i) : Eucl d → ℝ) z.1) Filter.atTop (nhds ((g : Eucl d → ℝ) z.1)) :=
    (MeasureTheory.quasiMeasurePreserving_fst (μ := (volume : Measure (Eucl d)))
      (ν := (volume : Measure (Eucl d)))).preimage_ae_eq hψae
  have hsnd : ∀ᵐ z : Eucl d × Eucl d ∂(volume : Measure (Eucl d)).prod volume,
      Tendsto (fun i => (f (ψ i) : Eucl d → ℝ) z.2) Filter.atTop (nhds ((g : Eucl d → ℝ) z.2)) :=
    (MeasureTheory.quasiMeasurePreserving_snd (μ := (volume : Measure (Eucl d)))
      (ν := (volume : Measure (Eucl d)))).preimage_ae_eq hψae
  have hpoint : ∀ᵐ z : Eucl d × Eucl d ∂(volume : Measure (Eucl d)).prod volume,
      Filter.liminf (fun n => F n z) Filter.atTop = G z := by
    filter_upwards [hfst, hsnd] with z hx hy
    have hreal : Tendsto
        (fun n => gagliardoIntegrand κ (f (ψ n) : Eucl d → ℝ) z)
        Filter.atTop (nhds (gagliardoIntegrand κ (g : Eucl d → ℝ) z)) := by
      dsimp [gagliardoIntegrand]
      change Tendsto
        (fun n => (((f (ψ n) : Eucl d → ℝ) z.1 - (f (ψ n) : Eucl d → ℝ) z.2) ^ 2) *
          gagliardoKernel κ z.1 z.2)
        Filter.atTop
        (nhds (((((g : Eucl d → ℝ) z.1 - (g : Eucl d → ℝ) z.2) ^ 2) *
          gagliardoKernel κ z.1 z.2))
      exact ((hx.sub hy).pow 2).mul tendsto_const_nhds
    have henn : Tendsto (fun n => F n z) Filter.atTop (nhds (G z)) := by
      dsimp [F, G]
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto _).comp hreal
    exact henn.liminf_eq
  have hFatou : (∫⁻ z, Filter.liminf (fun n => F n z) Filter.atTop ∂((volume : Measure (Eucl d)).prod volume)) ≤
      Filter.liminf (fun n => ∫⁻ z, F n z ∂((volume : Measure (Eucl d)).prod volume)) Filter.atTop :=
    lintegral_liminf_le' hFmeas
  have hFatouG : (∫⁻ z, G z ∂((volume : Measure (Eucl d)).prod volume)) ≤
      Filter.liminf (fun n => ∫⁻ z, F n z ∂((volume : Measure (Eucl d)).prod volume)) Filter.atTop := by
    calc
      _ = ∫⁻ z, Filter.liminf (fun n => F n z) Filter.atTop ∂((volume : Measure (Eucl d)).prod volume) := by
        apply lintegral_congr_ae
        exact hpoint.symm
      _ ≤ _ := hFatou
  have ha0 : 0 ≤ a := by
    obtain ⟨n, hn⟩ := ha.exists
    exact (gagliardoSeminormSq_nonneg κ (volume : Measure (Eucl d)) (f n : Eucl d → ℝ)).trans hn
  have hFbound : ∀ᶠ n in Filter.atTop,
      (∫⁻ z, F n z ∂((volume : Measure (Eucl d)).prod volume)) ≤ ENNReal.ofReal a := by
    filter_upwards [ha.comp hψmono.tendsto_atTop] with n hn
    have hInt : Integrable
        (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f (ψ n) : Eucl d → ℝ) z)
        ((volume : Measure (Eucl d)).prod volume) :=
      (mem_formDomain_iff κ D (f (ψ n))).mp (hf (ψ n)) |>.2
    have hnn : 0 ≤ᵐ[((volume : Measure (Eucl d)).prod volume)]
        (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f (ψ n) : Eucl d → ℝ) z) :=
      ae_of_all _ fun z => gagliardoIntegrand_nonneg κ _ z
    have hmeas : AEStronglyMeasurable
        (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (f (ψ n) : Eucl d → ℝ) z)
        ((volume : Measure (Eucl d)).prod volume) :=
      gagliardoIntegrand_aestronglyMeasurable κ (volume : Measure (Eucl d)) hK
        (Lp.aestronglyMeasurable _)
    have hEq : (∫⁻ z, F n z ∂((volume : Measure (Eucl d)).prod volume)) =
        ENNReal.ofReal (gagliardoSeminormSq κ (volume : Measure (Eucl d))
          (f (ψ n) : Eucl d → ℝ)) := by
      dsimp [F]
      rw [← ENNReal.ofReal_toReal (hInt.lintegral_lt_top.ne)]
      rw [← integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    rw [hEq]
    exact ENNReal.ofReal_le_ofReal hn
  have hliminfBound :
      Filter.liminf (fun n => ∫⁻ z, F n z ∂((volume : Measure (Eucl d)).prod volume)) Filter.atTop ≤
        ENNReal.ofReal a :=
    Filter.liminf_le_of_frequently_le hFbound.frequently
  have hGbound : ∫⁻ z, G z ∂((volume : Measure (Eucl d)).prod volume) ≤ ENNReal.ofReal a :=
    hFatouG.trans hliminfBound
  have hGnonneg : 0 ≤ᵐ[((volume : Measure (Eucl d)).prod volume)]
      (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (g : Eucl d → ℝ) z) :=
    ae_of_all _ fun z => gagliardoIntegrand_nonneg κ _ z
  have hGInt : Integrable
      (fun z : Eucl d × Eucl d => gagliardoIntegrand κ (g : Eucl d → ℝ) z)
      ((volume : Measure (Eucl d)).prod volume) := by
    apply (ENNReal.lintegral_ofReal_ne_top_iff_integrable hGmeas hGnonneg).mp
    apply ne_of_lt
    exact lt_of_le_of_lt hGbound ENNReal.ofReal_lt_top
  have hGEq : gagliardoSeminormSq κ (volume : Measure (Eucl d)) (g : Eucl d → ℝ) =
      ENNReal.toReal (∫⁻ z, G z ∂((volume : Measure (Eucl d)).prod volume)) := by
    dsimp [G, gagliardoSeminormSq]
    exact integral_eq_lintegral_of_nonneg_ae hGnonneg
      (gagliardoIntegrand_aestronglyMeasurable κ (volume : Measure (Eucl d)) hK
        (Lp.aestronglyMeasurable _))
  have hEg : gagliardoSeminormSq κ (volume : Measure (Eucl d)) (g : Eucl d → ℝ) ≤ a := by
    rw [hGEq]
    exact ENNReal.toReal_le_of_le_ofReal ha0 hGbound
  exact ⟨⟨hzeroG, hGInt⟩, hEg⟩

end Tunneling
