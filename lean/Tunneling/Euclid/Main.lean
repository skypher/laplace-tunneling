import Tunneling.Euclid.GroundState
import Tunneling.Euclid.Decomp
import Tunneling.Euclid.Compression
import Tunneling.Spectral.Cluster
import Tunneling.Final
import Tunneling.Euclid.MainAux
import Tunneling.Euclid.DecompForm
import Tunneling.Euclid.DecompBound

/-!
# The main theorems for the restricted fractional Laplacian on `ℝ^d`

All objects are the concrete ones of the paper:

* `eigenvalue c κ G k` is the `(k+1)`-st eigenvalue of the restricted
  fractional Laplacian `A_G` (Courant--Fischer level of the closed form
  `eq:form` on `H^s_0(G)`), with `κ = d + 2s`;
* `μ₁ = eigenvalue c κ D 0`, `μ₂ = eigenvalue c κ D 1`, `g = μ₂ - μ₁`;
* `φ` is the normalized nonnegative ground state of `A_D` and
  `m₁ = ∫ φ`.

`multiWell_main` is paper Theorem 4.3 (`thm:multi-well`) and `twoWell_main`
is paper Theorem 3.3 (`thm:two-well`).
-/

namespace Tunneling

open MeasureTheory
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}


private noncomputable def positiveGroundRepresentative (D : Set (Eucl d)) (φ : L2 d) : Eucl d → ℝ :=
  D.indicator (fun x => max (φ x) 0)

private theorem positiveGroundRepresentative_data (s c R : ℝ) (D : Set (Eucl d))
    (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ) :
    (∀ x, positiveGroundRepresentative D φ x ≠ 0 → ‖x‖ ≤ R) ∧
      Integrable (positiveGroundRepresentative D φ) ∧
      (∫ x, positiveGroundRepresentative D φ x = ∫ x, φ x) ∧
      (∀ x, 0 ≤ positiveGroundRepresentative D φ x) ∧
      positiveGroundRepresentative D φ =ᵐ[volume] (φ : Eucl d → ℝ) := by
  classical
  let u := positiveGroundRepresentative D φ
  have hsuppAE : ∀ᵐ x ∂(volume : Measure (Eucl d)), x ∉ D → φ x = 0 :=
    (mem_formDomain_iff _ D φ).mp hφ.mem |>.1
  have hu_ae : u =ᵐ[volume] (φ : Eucl d → ℝ) := by
    filter_upwards [hsuppAE, hφ.nonneg] with x hx hnonneg
    by_cases hD : x ∈ D
    · have hu : u x = max (φ x) 0 := by simp [u, positiveGroundRepresentative, hD]
      calc
        u x = max (φ x) 0 := hu
        _ = φ x := max_eq_left hnonneg
    · have hu : u x = 0 := by simp [u, positiveGroundRepresentative, hD]
      rw [hu, hx hD]
  have hint : Integrable u := (hφ.integrable s c R D hDR).congr hu_ae.symm
  have hmass : ∫ x, u x = ∫ x, φ x := MeasureTheory.integral_congr_ae hu_ae
  have hnonneg : ∀ x, 0 ≤ u x := by
    intro x
    by_cases hD : x ∈ D
    · have hu : u x = max (φ x) 0 := by simp [u, positiveGroundRepresentative, hD]
      rw [hu]
      exact le_max_right _ _
    · simp [u, positiveGroundRepresentative, hD]
  have hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ R := by
    intro x hx
    by_contra hR'
    have hnot : x ∉ D := by
      intro hDx
      have hb := hDR hDx
      have hb' : ‖x‖ < R := by simpa using hb
      exact hR' hb'.le
    have hu : u x = 0 := by simp [u, positiveGroundRepresentative, hnot]
    exact hx hu
  exact ⟨hsupp, hint, hmass, hnonneg, hu_ae⟩

private theorem kernelCrossPairing_congr_ae_self (K : Eucl d → Eucl d → ℝ)
    (u v : Eucl d → ℝ) (h : u =ᵐ[volume] v) :
    kernelCrossPairing K (volume : Measure (Eucl d)) u u =
      kernelCrossPairing K (volume : Measure (Eucl d)) v v := by
  unfold kernelCrossPairing
  have hf := (MeasureTheory.Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae_eq_comp h
  have hs := (MeasureTheory.Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Eucl d))) (ν := (volume : Measure (Eucl d)))).ae_eq_comp h
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hf, hs] with z hz₁ hz₂
  have hz₁' : u z.1 = v z.1 := by simpa only [Function.comp_apply] using hz₁
  have hz₂' : u z.2 = v z.2 := by simpa only [Function.comp_apply] using hz₂
  rw [hz₁', hz₂']

private theorem multiWellCompressionMatrix_congr_ae
    {ι : Type*} [Fintype ι] [DecidableEq ι] (κ c : ℝ) (a : ι → Eucl d) (L : ℝ)
    (u v : Eucl d → ℝ) (h : u =ᵐ[volume] v) :
    multiWellCompressionMatrix (volume : Measure (Eucl d)) κ c u a L =
      multiWellCompressionMatrix (volume : Measure (Eucl d)) κ c v a L := by
  classical
  ext i j
  by_cases hij : i = j
  · simp [multiWellCompressionMatrix, hij]
  · simp only [multiWellCompressionMatrix_apply, if_neg hij]
    have hk := kernelCrossPairing_congr_ae_self
      (multiWellCrossKernel κ ((L : ℝ) • (a i - a j))) u v h
    rw [hk]

private theorem quadraticMap_polar_sum {α M : Type*} [AddCommGroup M] [Module ℝ M]
    (f : α → QuadraticMap ℝ M ℝ) (s : Finset α) (x y : M) :
    QuadraticMap.polar (s.sum f : QuadraticMap ℝ M ℝ) x y =
      s.sum (fun i => QuadraticMap.polar (f i) x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [QuadraticMap.polar]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, FunLike.coe_add, QuadraticMap.polar_add, ih,
        Finset.sum_insert hi]
private theorem quadraticMap_polar_comp_linear {M N : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (Q : QuadraticMap ℝ N ℝ) (f : M →ₗ[ℝ] N) (x y : M) :
    QuadraticMap.polar (Q.comp f) x y =
      QuadraticMap.polar Q (f x) (f y) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply]
  rw [f.map_add]
private theorem wellMap_ground_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : WellGeometry d ι) (φ : formDomain G.κ G.D) (i : ι)
    (v : formDomain G.κ G.Ω) :
    inner ℝ (φ : L2 d) (G.wellMap i v : L2 d) =
      inner ℝ (G.Φ φ i : L2 d) (v : L2 d) := by
  rw [G.wellMap_coe]
  have hs := G.inner_eq_sum (G.Φ φ i) v
  simp_rw [G.pieceL2_Φ φ] at hs
  rw [Finset.sum_eq_single i] at hs
  · simpa using hs.symm
  · intro j hj hji
    simp [hji]
  · simp


section MultiWell

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The exact cluster comparison `eq:exact-cluster-comparison` together with
the cluster-edge bounds, for the eigenvalues of `A_{Ω_{a,L}}` and the ordered
eigenvalues `τ_k(L)` of the exact compression matrix `T_L`. -/
theorem multiWell_cluster (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (a : ι → Eucl d) (L : ℝ) (hL : 0 < L)
    (hsep : ∀ i j : ι, i ≠ j → 4 * R ≤ L * ‖a i - a j‖)
    (hsmall : multiWellGamma (oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ) a L ≤
      (oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ).gap / 4) :
    let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
    let hT := multiWellCompressionMatrix_isHermitian (volume : Measure (Eucl d))
      A.kappa A.c (φ : Eucl d → ℝ) a L
    (∀ k : Fin (Fintype.card ι),
      -(2 * multiWellGamma A a L ^ 2 / A.gap) ≤
          eigenvalue A.c A.kappa (multiWellDomain D a L) k.val -
            (A.mu1 + hT.eigenvalues₀ (Fin.rev k)) ∧
        eigenvalue A.c A.kappa (multiWellDomain D a L) k.val -
            (A.mu1 + hT.eigenvalues₀ (Fin.rev k)) ≤ 0) ∧
      (∀ k : Fin (Fintype.card ι), |hT.eigenvalues₀ k| ≤ multiWellGamma A a L) ∧
      A.mu1 + A.gap - multiWellGamma A a L ≤
        eigenvalue A.c A.kappa (multiWellDomain D a L) (Fintype.card ι) := by
  classical
  let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
  let G : WellGeometry d ι :=
    { κ := (d : ℝ) + 2 * s, hκ := by linarith [hs.1], R := R, hR := hR,
      D := D, hDm := hDo.measurableSet, hDR := hDR, a := a, L := L, hL := hL,
      hsep := hsep }
  let φhat : formDomain G.κ G.D := ⟨φ, hφ.mem⟩
  let Ψ : ι → formDomain G.κ G.Ω := fun i => G.Φ φhat i
  let T := multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c
      (φ : Eucl d → ℝ) a L
  have hwsymm : ∀ x y : formDomain G.κ G.Ω,
      (G.interaction c) x y = (G.interaction c) y x := by
    intro x y
    exact G.interaction_symm c x y
  have hgamma : multiWellGamma A a L =
      c * 2 ^ G.κ * (volume G.D).toReal * sigmaKappa G.a G.κ * G.L ^ (-G.κ) := by
    simp [multiWellGamma, A, oneWellConstants, G]
  have hwb : ∀ x y : formDomain G.κ G.Ω,
      |(G.interaction c) x y| ≤ multiWellGamma A a L * ‖x‖ * ‖y‖ := by
    intro x y
    rw [hgamma]
    exact G.abs_interaction_le c hc.le x y
  have hQ : ∀ v : formDomain G.κ G.Ω,
      formQ c G.κ G.Ω v = (G.Q0 c) v + (G.interaction c) v v := by
    intro v
    exact G.formQ_eq c v
  have horth : Orthonormal ℝ Ψ := by
    refine ⟨?_, ?_⟩
    · intro i
      change ‖translateL2 (G.L • G.a i) (φ : L2 d)‖ = 1
      simp [hφ.norm_eq_one]
    · intro i j hij
      change inner ℝ (Ψ i : L2 d) (Ψ j : L2 d) = 0
      rw [G.inner_eq_sum (Ψ i) (Ψ j)]
      simp_rw [Ψ, G.pieceL2_Φ φhat]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hki : k = i
      · subst k
        simp [hij]
      · by_cases hkj : k = j
        · subst k
          simp [Ne.symm hij]
        · simp [hki, hkj]
  have hgapAll : ∀ v : formDomain G.κ G.Ω,
      (∀ i, inner ℝ (Ψ i : L2 d) (v : L2 d) = 0) →
        (A.mu1 + A.gap) * ‖(v : L2 d)‖ ^ 2 ≤ (G.Q0 c) v := by
    intro v hperp
    have hpieces : ∀ i, inner ℝ (φhat : L2 d) (G.wellMap i v : L2 d) = 0 := by
      intro i
      have heq := wellMap_ground_inner G φhat i v
      rw [heq]
      exact hperp i
    have hpiece : ∀ i,
        A.mu2 * ‖(G.wellMap i v : L2 d)‖ ^ 2 ≤
          formQ c G.κ G.D (G.wellMap i v) := by
      intro i
      have hi := hφ.gap hd s hs c hc R D hDo hDne hDR
        (G.wellMap i v) (hpieces i)
      simpa [A, oneWellConstants, G] using hi
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpiece i)
    have hnormsum : (∑ i : ι, ‖(G.wellMap i v : L2 d)‖ ^ 2) =
        ‖(v : L2 d)‖ ^ 2 := by
      simpa [real_inner_self_eq_norm_sq, G.wellMap_coe] using (G.inner_eq_sum v v).symm
    have hsumQ : (∑ i : ι, formQ c G.κ G.D (G.wellMap i v)) = (G.Q0 c) v := by
      simp [WellGeometry.Q0, QuadraticMap.comp_apply]
    have hsumCoeff :
        (∑ i : ι, A.mu2 * ‖(G.wellMap i v : L2 d)‖ ^ 2) =
          A.mu2 * ‖(v : L2 d)‖ ^ 2 := by
      rw [← Finset.mul_sum, hnormsum]
    have hmu2 : A.mu1 + A.gap = A.mu2 := by
      simp [A, oneWellConstants, TwoWellConstants.gap]
    rw [hsumCoeff, hsumQ, ← hmu2] at hsum
    exact hsum
  have heig : ∀ i (v : formDomain G.κ G.Ω),
      QuadraticMap.polar (G.Q0 c) (Ψ i) v =
        2 * A.mu1 * inner ℝ (Ψ i : L2 d) (v : L2 d) := by
    intro i v
    rw [WellGeometry.Q0, quadraticMap_polar_sum]
    have hsum :
        (∑ k : ι,
          QuadraticMap.polar ((formQ c G.κ G.D).comp (G.wellMap k)) (Ψ i) v) =
          QuadraticMap.polar (formQ c G.κ G.D) φhat (G.wellMap i v) := by
      rw [Finset.sum_eq_single i]
      · rw [quadraticMap_polar_comp_linear]
        have hwi : G.wellMap i (Ψ i) = φhat := by
          apply Subtype.ext
          rw [G.wellMap_coe]
          simp [Ψ, G.pieceL2_Φ]
        rw [hwi]
      · intro k hk hki
        rw [quadraticMap_polar_comp_linear]
        have hwzero : G.wellMap k (Ψ i) = 0 := by
          apply Subtype.ext
          rw [G.wellMap_coe]
          simp [Ψ, G.pieceL2_Φ, hki]
        rw [hwzero]
        simp
      · simp
    rw [hsum]
    have hp := IsPositiveGroundState.polar_eq hd s hs c hc R D hDo hDne hDR hφ
      (G.wellMap i v)
    have hin := wellMap_ground_inner G φhat i v
    rw [hin] at hp
    simpa [A, oneWellConstants, G, Ψ] using hp
  have hdim : ∃ W : Submodule ℝ (formDomain G.κ G.Ω),
      Module.finrank ℝ W = Fintype.card ι + 1 := by
    simpa [G] using exists_finrank_formDomain hd s hs G.Ω
      (G.isOpen_Ω hDo) (G.Ω_nonempty hDne) (Fintype.card ι + 1)
  have hTw : ∀ i j, T i j = (G.interaction c) (Ψ i) (Ψ j) := by
    intro i j
    exact (G.interaction_Φ c φhat i j).symm
  have hT : T.IsHermitian := by
    simpa [T] using multiWellCompressionMatrix_isHermitian
      (volume : Measure (Eucl d)) A.kappa A.c (φ : Eucl d → ℝ) a L
  have hb0 : 0 ≤ multiWellGamma A a L := by
    unfold multiWellGamma
    have hsig := sigmaKappa_nonneg a A.kappa
    have hvol := A.hvolumeD.le
    have hpow : 0 ≤ (2 : ℝ) ^ A.kappa := Real.rpow_nonneg (by norm_num) _
    have hLpow : 0 ≤ L ^ (-A.kappa) := Real.rpow_nonneg hL.le _
    positivity
  have hsmall' : multiWellGamma A a L ≤ A.gap / 4 := hsmall
  have hg : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  have hclusterLevel := MinMax.cluster_levels (G.Q0 c) (formQ c G.κ G.Ω)
    (G.interaction c) hwsymm (multiWellGamma A a L) hwb hQ Ψ horth A.mu1 A.gap
    hg hb0 hsmall' heig hgapAll hdim T hTw hT
  have hlevEq : ∀ n, MinMax.level (formQ c G.κ G.Ω) n =
      eigenvalue A.c A.kappa (multiWellDomain D a L) n := by
    intro n
    rfl
  rcases hclusterLevel with ⟨hcl, hEig, hnext⟩
  refine ⟨?_, hEig, ?_⟩
  · intro k
    have hk := hcl k
    rw [hlevEq] at hk
    have hkl : -(2 * multiWellGamma A a L ^ 2 / A.gap) ≤
        eigenvalue A.c A.kappa (multiWellDomain D a L) k.val -
          (A.mu1 + (hT).eigenvalues₀ (Fin.rev k)) := by
      simpa [A, oneWellConstants] using hk.1
    have hku : eigenvalue A.c A.kappa (multiWellDomain D a L) k.val -
        (A.mu1 + (hT).eigenvalues₀ (Fin.rev k)) ≤ 0 := by
      simpa [A, oneWellConstants] using hk.2
    exact ⟨hkl, hku⟩
  · have hn : A.mu1 + A.gap - multiWellGamma A a L ≤
        eigenvalue A.c A.kappa (multiWellDomain D a L) (Fintype.card ι) := by
      rw [← hlevEq]
      exact hnext
    exact hn


/-- **Paper Theorem 4.3** (`thm:multi-well`): finite multi-well effective
interaction matrix.  For a bounded open `D ⊆ B_R(0)`, distinct sites `a`, the
eigenvalues of the restricted fractional Laplacian on
`Ω_{a,L} = ⋃_j (D + L a_j)` satisfy, whenever `L δ_a ≥ 4R` and `γ_L ≤ g/4`,

* `|λ_k(Ω) - (μ₁ + L^{-κ} θ_k)| ≤ ε_L + 2γ_L²/g` for `1 ≤ k ≤ N`,
* `λ_N(Ω) ≤ μ₁ + γ_L`, `λ_{N+1}(Ω) ≥ μ₁ + g - γ_L`,
  `λ_{N+1}(Ω) - λ_N(Ω) ≥ g - 2γ_L`,

and `L^{d+2s} (λ_k(Ω) - μ₁) → θ_k` as `L → ∞`, where `θ_1 ≤ ... ≤ θ_N` are
the eigenvalues of the effective matrix `M_a` of equation
`eq:effective-matrix`. -/
theorem multiWell_main (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (a : ι → Eucl d) (ha : ∀ i j : ι, i ≠ j → a i ≠ a j) :
    let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
    multiWellStatement A a (effectiveInteractionTheta a A.c A.phiMass A.kappa)
      (fun L k => eigenvalue A.c A.kappa (multiWellDomain D a L) k) := by

  classical
  let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
  let u := positiveGroundRepresentative D φ
  let T : ℝ → Matrix ι ι ℝ :=
    fun L => multiWellCompressionMatrix (volume : Measure (Eucl d)) A.kappa A.c
      (φ : Eucl d → ℝ) a L
  let lambda : ℝ → ℕ → ℝ :=
    fun L n => eigenvalue A.c A.kappa (multiWellDomain D a L) n
  obtain ⟨hsupp, hint, hmass, hnonneg, hu_ae⟩ :=
    positiveGroundRepresentative_data s c R D hDR φ hφ
  have hmassA : ∀ L : ℝ, (∫ x, u x) = A.phiMass := by
    intro L
    simpa [A, oneWellConstants] using hmass
  have hT : ∀ L : ℝ, (T L).IsHermitian := by
    intro L
    simpa [T] using multiWellCompressionMatrix_isHermitian
      (volume : Measure (Eucl d)) A.kappa A.c (φ : Eucl d → ℝ) a L
  have hnorm : ∀ L : ℝ, 0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      ‖T L - L ^ (-A.kappa) •
        effectiveInteractionMatrix a A.c A.phiMass A.kappa‖ ≤
        multiWellEpsilon A a L := by
    intro L hL hsep hsmall
    have hnormU := compression_norm_le_euclid A a u L hL hsep hsupp hint
      (hmassA L) hnonneg
    have hmatrix := multiWellCompressionMatrix_congr_ae A.kappa A.c a L
      u (φ : Eucl d → ℝ) hu_ae
    rw [hmatrix] at hnormU
    simpa [T] using hnormU
  have hcluster : ∀ L : ℝ, 0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      ∀ k : Fin (Fintype.card ι),
        -(2 * multiWellGamma A a L ^ 2 / A.gap) ≤
          lambda L k.val -
            (A.mu1 + (hT L).eigenvalues₀ (Fin.rev k)) ∧
          lambda L k.val -
            (A.mu1 + (hT L).eigenvalues₀ (Fin.rev k)) ≤ 0 := by
    intro L hL hsep hsmall k
    have hcL := multiWell_cluster hd s hs c hc R hR D hDo hDne hDR φ hφ
      a L hL hsep hsmall
    rcases hcL with ⟨hbounds, _, _⟩
    simpa [lambda, T] using hbounds k
  have hupper : ∀ L : ℝ, 0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      lambda L (Fintype.card ι - 1) ≤ A.mu1 + multiWellGamma A a L := by
    intro L hL hsep hsmall
    have hcL := multiWell_cluster hd s hs c hc R hR D hDo hDne hDR φ hφ
      a L hL hsep hsmall
    rcases hcL with ⟨hbounds, habs, _⟩
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    let k : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
    have hkrev : Fin.rev k = 0 := by
      apply Fin.ext
      have hr : (Fin.rev k).val = Fintype.card ι - (k.val + 1) := rfl
      rw [hr]
      simp [k]
      omega
    have hEdge :
        lambda L (Fintype.card ι - 1) -
          (A.mu1 + (hT L).eigenvalues₀ 0) ≤ 0 := by
      simpa [lambda, T, k, hkrev] using (hbounds k).2
    have hEig : |(hT L).eigenvalues₀ 0| ≤ multiWellGamma A a L := by
      simpa [T] using habs 0
    have hEig' : (hT L).eigenvalues₀ 0 ≤ multiWellGamma A a L :=
      (abs_le.mp hEig).2
    linarith
  have hnext : ∀ L : ℝ, 0 < L →
      (∀ i j : ι, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖) →
      multiWellGamma A a L ≤ A.gap / 4 →
      A.mu1 + A.gap - multiWellGamma A a L ≤ lambda L (Fintype.card ι) := by
    intro L hL hsep hsmall
    have hcL := multiWell_cluster hd s hs c hc R hR D hDo hDne hDR φ hφ
      a L hL hsep hsmall
    rcases hcL with ⟨_, _, hn⟩
    simpa [lambda] using hn
  have hfinal := FinalTheoremMultiWell A a lambda T ha hT hnorm hcluster hupper hnext
  change multiWellStatement A a
    (fun k => (effectiveInteractionMatrix_isHermitian
      a A.c A.phiMass A.kappa).eigenvalues₀ (Fin.rev k))
    (fun L k => eigenvalue A.c A.kappa (multiWellDomain D a L) k)
  exact hfinal


end MultiWell

section TwoWell


private theorem twoWellSites_dist (e : Eucl d) (he : ‖e‖ = 1)
    (i j : Fin 2) (hij : i ≠ j) :
    ‖twoWellSites e i - twoWellSites e j‖ = 1 := by
  have h01 : ‖twoWellSites e 0 - twoWellSites e 1‖ = 1 := by
    have hv : twoWellSites e 0 - twoWellSites e 1 = -e := by
      simp [twoWellSites]
      module
    rw [hv, norm_neg, he]
  have h10 : ‖twoWellSites e 1 - twoWellSites e 0‖ = 1 := by
    simpa [norm_sub_rev] using h01
  fin_cases i <;> fin_cases j <;> simp_all [h01, h10]

private theorem twoWellSites_sigma (e : Eucl d) (he : ‖e‖ = 1) (q : ℝ) :
    sigmaKappa (twoWellSites e) q = 1 := by
  have h01 : ‖twoWellSites e 0 - twoWellSites e 1‖ = 1 := by
    have hv : twoWellSites e 0 - twoWellSites e 1 = -e := by
      simp [twoWellSites]
      module
    rw [hv, norm_neg, he]
  have h10 : ‖twoWellSites e 1 - twoWellSites e 0‖ = 1 := by
    simpa [norm_sub_rev] using h01
  have hrow : ∀ i : Fin 2,
      ∑ j : Fin 2, (if i = j then (0 : ℝ)
        else ‖twoWellSites e i - twoWellSites e j‖ ^ (-q)) = 1 := by
    intro i
    fin_cases i <;> simp [Fin.sum_univ_two, h01, h10]
  unfold sigmaKappa
  apply le_antisymm
  · apply ciSup_le
    intro i
    rw [hrow i]
  · calc
      1 = ∑ j : Fin 2, (if (0 : Fin 2) = j then (0 : ℝ)
          else ‖twoWellSites e 0 - twoWellSites e j‖ ^ (-q)) := (hrow 0).symm
      _ ≤ ⨆ i : Fin 2, ∑ j : Fin 2, (if i = j then (0 : ℝ)
          else ‖twoWellSites e i - twoWellSites e j‖ ^ (-q)) :=
        le_ciSup (f := fun i : Fin 2 => ∑ j : Fin 2,
          (if i = j then (0 : ℝ) else ‖twoWellSites e i - twoWellSites e j‖ ^ (-q)))
          (Set.finite_range _).bddAbove 0

private theorem twoWellTheta_values (e : Eucl d) (he : ‖e‖ = 1)
    (c m κ : ℝ) (hc : 0 ≤ c) :
    effectiveInteractionTheta (twoWellSites e) c m κ
        (⟨0, by simp⟩ : Fin (Fintype.card (Fin 2))) = -c * m ^ 2 ∧
      effectiveInteractionTheta (twoWellSites e) c m κ
        (⟨1, by simp⟩ : Fin (Fintype.card (Fin 2))) = c * m ^ 2 := by
  let M := effectiveInteractionMatrix (twoWellSites e) c m κ
  let hM : M.IsHermitian := effectiveInteractionMatrix_isHermitian
      (twoWellSites e) c m κ
  have h00 : M 0 0 = 0 := by simp [M, effectiveInteractionMatrix]
  have h11 : M 1 1 = 0 := by simp [M, effectiveInteractionMatrix]
  have h01dist := twoWellSites_dist e he 0 1 (by decide)
  have h01 : M 0 1 = -c * m ^ 2 := by
    simp [M, effectiveInteractionMatrix, h01dist]
  have habs : |M 0 1| = c * m ^ 2 := by
    rw [h01, show -c * m ^ 2 = -(c * m ^ 2) by ring, abs_neg]
    exact abs_of_nonneg (mul_nonneg hc (sq_nonneg m))
  let i0 : Fin (Fintype.card (Fin 2)) := ⟨0, by simp⟩
  let i1 : Fin (Fintype.card (Fin 2)) := ⟨1, by simp⟩
  have hidx0 : i0 = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hidx1 : i1 = (1 : Fin 2) := by
    apply Fin.ext
    rfl
  have hrev0 : Fin.rev i0 =
      Fin.rev (0 : Fin (Fintype.card (Fin 2))) := by
    apply Fin.ext
    simp [Fin.rev, i0]
  have hrev1 : Fin.rev i1 =
      Fin.rev (1 : Fin (Fintype.card (Fin 2))) := by
    apply Fin.ext
    simp [Fin.rev, i1]
  have hM_eq :
      effectiveInteractionMatrix_isHermitian (twoWellSites e) c m κ = hM :=
    Subsingleton.elim _ _
  have heig := eigenvalues₀_fin_two_of_zero_diag M hM h00 h11
  constructor
  · simp only [effectiveInteractionTheta]
    rw [hM_eq]
    change hM.eigenvalues₀ (Fin.rev i0) = -c * m ^ 2
    rw [hrev0, heig.1, habs]
    ring
  · simp only [effectiveInteractionTheta]
    rw [hM_eq]
    change hM.eigenvalues₀ (Fin.rev i1) = c * m ^ 2
    rw [hrev1, heig.2, habs]

/-- **Paper Theorem 3.3** (`thm:two-well`): two-well algebraic splitting.  For
a bounded open `D ⊆ B_R(0)`, a unit vector `e`, and `L ≥ L₀`
(equation `eq:explicit-L0`), the eigenvalues of the restricted fractional
Laplacian on `Ω_L` satisfy `eq:lambda1`, `eq:lambda2`,
`eq:two-well-third-level`, the limit `eq:gap-limit`, and the first two
eigenvalues are simple: `λ₁(Ω_L) < λ₂(Ω_L) < λ₃(Ω_L)`.  Central symmetry of
`D` is not needed for these conclusions (compare paper Corollaries 4.4
and 4.6). -/
theorem twoWell_main (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (e : Eucl d) (he : ‖e‖ = 1) :
    let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
    A.twoWellStatement (fun L k => eigenvalue A.c A.kappa (twoWellDomain D e L) k) ∧
      ∀ L : ℝ, A.L0 ≤ L →
        eigenvalue A.c A.kappa (twoWellDomain D e L) 0 <
            eigenvalue A.c A.kappa (twoWellDomain D e L) 1 ∧
          eigenvalue A.c A.kappa (twoWellDomain D e L) 1 <
            eigenvalue A.c A.kappa (twoWellDomain D e L) 2 := by

  classical
  let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
  let a := twoWellSites e
  let lambdaM : ℝ → ℕ → ℝ :=
    fun L n => eigenvalue A.c A.kappa (multiWellDomain D a L) n
  let lambdaT : ℝ → ℕ → ℝ :=
    fun L n => eigenvalue A.c A.kappa (twoWellDomain D e L) n
  have hdist : ∀ i j : Fin 2, i ≠ j → ‖a i - a j‖ = 1 := by
    intro i j hij
    exact twoWellSites_dist e he i j hij
  have hsiteNe : ∀ i j : Fin 2, i ≠ j → a i ≠ a j := by
    intro i j hij heq
    have hdij := hdist i j hij
    have hzero : a i - a j = 0 := sub_eq_zero.mpr heq
    rw [hzero] at hdij
    simp at hdij
  have hmulti : multiWellStatement A a
      (effectiveInteractionTheta a A.c A.phiMass A.kappa) lambdaM := by
    simpa [A, a, lambdaM] using
      (multiWell_main hd s hs c hc R hR D hDo hDne hDR φ hφ a hsiteNe)
  have hgamma : ∀ L, multiWellGamma A a L = A.beta L := by
    intro L
    simp [multiWellGamma, TwoWellConstants.beta, a, twoWellSites_sigma e he]
  have hepsilon : ∀ L,
      multiWellEpsilon A a L =
        A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) := by
    intro L
    simp [multiWellEpsilon, a, twoWellSites_sigma e he]
  have hrem : ∀ L,
      multiWellEpsilon A a L + 2 * multiWellGamma A a L ^ 2 / A.gap =
        A.remainder L := by
    intro L
    rw [hepsilon L, hgamma L]
    simp [TwoWellConstants.remainder]
  have htheta := twoWellTheta_values e he A.c A.phiMass A.kappa A.hc.le
  let i0 : Fin (Fintype.card (Fin 2)) := ⟨0, by simp⟩
  let i1 : Fin (Fintype.card (Fin 2)) := ⟨1, by simp⟩
  have htheta0 : effectiveInteractionTheta a A.c A.phiMass A.kappa i0 =
      -A.c * A.phiMass ^ 2 := by
    simpa [a, i0] using htheta.1
  have htheta1 : effectiveInteractionTheta a A.c A.phiMass A.kappa i1 =
      A.c * A.phiMass ^ 2 := by
    simpa [a, i1] using htheta.2
  have htwoConclusion : ∀ L : ℝ, A.L0 ≤ L →
      A.twoWellConclusion (lambdaT L) L := by
    intro L hL
    have h4L0 : 4 * A.R ≤ A.L0 := le_max_left _ _
    have h4L : 4 * A.R ≤ L := h4L0.trans hL
    have hLpos : 0 < L := by
      have h4R : 0 < 4 * A.R := mul_pos (by norm_num) A.hR
      exact lt_of_lt_of_le h4R h4L
    have hsep : ∀ i j : Fin 2, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖ := by
      intro i j hij
      rw [hdist i j hij, mul_one]
      exact h4L
    have hsmall : multiWellGamma A a L ≤ A.gap / 4 := by
      rw [hgamma L]
      exact TwoWellConstants.beta_small A hL
    have hconcl := hmulti.1 L hLpos hsep hsmall
    rcases hconcl with ⟨herr, hupper, hnext, hgap⟩
    have h0 := herr i0
    rw [htheta0] at h0
    have hcenter0 :
        A.mu1 + L ^ (-A.kappa) * (-A.c * A.phiMass ^ 2) =
          A.mu1 - A.c * A.phiMass ^ 2 * L ^ (-A.kappa) := by ring
    rw [hcenter0, hrem L] at h0
    have hbranch0 :
        |lambdaT L 0 - (A.mu1 - A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤
          A.remainder L := by
      simpa [lambdaM, lambdaT, a, i0, twoWellDomain_eq] using h0
    have h1 := herr i1
    rw [htheta1] at h1
    have hcenter1 :
        A.mu1 + L ^ (-A.kappa) * (A.c * A.phiMass ^ 2) =
          A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa) := by ring
    rw [hcenter1, hrem L] at h1
    have hbranch1 :
        |lambdaT L 1 - (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤
          A.remainder L := by
      simpa [lambdaM, lambdaT, a, i1, twoWellDomain_eq] using h1
    have hnext' : A.mu1 + A.gap - A.beta L ≤ lambdaM L 2 := by
      rw [hgamma L] at hnext
      simpa [lambdaM, Fintype.card_fin] using hnext
    have hbetaSmall : A.beta L ≤ A.gap / 4 := by
      simpa [hgamma L] using hsmall
    have hthirdM : A.mu1 + 3 * A.gap / 4 ≤ lambdaM L 2 := by
      linarith
    have hthird : A.mu1 + 3 * A.gap / 4 ≤ lambdaT L 2 := by
      simpa [lambdaM, lambdaT, a, twoWellDomain_eq] using hthirdM
    have hgap' : A.gap - 2 * A.beta L ≤ lambdaM L 2 - lambdaM L 1 := by
      rw [hgamma L] at hgap
      simpa [lambdaM, Fintype.card_fin] using hgap
    have hgapHalfM : A.gap / 2 ≤ lambdaM L 2 - lambdaM L 1 := by
      linarith [hbetaSmall]
    have hgapHalf : A.gap / 2 ≤ lambdaT L 2 - lambdaT L 1 := by
      simpa [lambdaM, lambdaT, a, twoWellDomain_eq] using hgapHalfM
    unfold TwoWellConstants.twoWellConclusion
    exact ⟨hbranch0, hbranch1, hthird, hgapHalf⟩
  have hlim0 := hmulti.2 i0
  have hlim1 := hmulti.2 i1
  have hlim0' : Filter.Tendsto
      (fun L : ℝ => L ^ A.kappa * (lambdaM L 0 - A.mu1))
      Filter.atTop (nhds (effectiveInteractionTheta a A.c A.phiMass A.kappa i0)) := by
    simpa [i0] using hlim0
  have hlim1' : Filter.Tendsto
      (fun L : ℝ => L ^ A.kappa * (lambdaM L 1 - A.mu1))
      Filter.atTop (nhds (effectiveInteractionTheta a A.c A.phiMass A.kappa i1)) := by
    simpa [i1] using hlim1
  have hthetaDiff :
      effectiveInteractionTheta a A.c A.phiMass A.kappa i1 -
        effectiveInteractionTheta a A.c A.phiMass A.kappa i0 =
          2 * A.c * A.phiMass ^ 2 := by
    rw [htheta1, htheta0]
    ring
  have hlimM : Filter.Tendsto
      (fun L : ℝ => L ^ A.kappa * (lambdaM L 1 - lambdaM L 0))
      Filter.atTop (nhds (2 * A.c * A.phiMass ^ 2)) := by
    have hsub := hlim1'.sub hlim0'
    have hsub' : Filter.Tendsto
        (fun L : ℝ => L ^ A.kappa * (lambdaM L 1 - A.mu1) -
          L ^ A.kappa * (lambdaM L 0 - A.mu1))
        Filter.atTop (nhds (2 * A.c * A.phiMass ^ 2)) := by
      simpa only [hthetaDiff] using hsub
    have hfun :
        (fun L : ℝ => L ^ A.kappa * (lambdaM L 1 - lambdaM L 0)) =
          (fun L => L ^ A.kappa * (lambdaM L 1 - A.mu1) -
            L ^ A.kappa * (lambdaM L 0 - A.mu1)) := by
      funext L
      ring
    rw [hfun]
    exact hsub'
  have hlimT : Filter.Tendsto
      (fun L : ℝ => L ^ A.kappa * (lambdaT L 1 - lambdaT L 0))
      Filter.atTop (nhds (2 * A.c * A.phiMass ^ 2)) := by
    simpa [lambdaM, lambdaT, a, twoWellDomain_eq] using hlimM
  refine ⟨⟨htwoConclusion, hlimT⟩, ?_⟩
  intro L hL
  have h4L0 : 4 * A.R ≤ A.L0 := le_max_left _ _
  have h4L : 4 * A.R ≤ L := h4L0.trans hL
  have hLpos : 0 < L := by
    have h4R : 0 < 4 * A.R := mul_pos (by norm_num) A.hR
    exact lt_of_lt_of_le h4R h4L
  have hsep : ∀ i j : Fin 2, i ≠ j → 4 * A.R ≤ L * ‖a i - a j‖ := by
    intro i j hij
    rw [hdist i j hij, mul_one]
    exact h4L
  have h01M : lambdaM L 0 < lambdaM L 1 := by
    have hR' : 0 < R + L / 2 := by linarith
    have hsiteNorm : ∀ i : Fin 2, ‖a i‖ = 1 / 2 := by
      intro i
      fin_cases i <;> simp [a, twoWellSites, norm_smul, he]
    have hball : multiWellDomain D a L ⊆ Metric.ball 0 (R + L / 2) := by
      intro x hx
      rcases hx with ⟨i, hi⟩
      have hxi : ‖x - L • a i‖ < R := by
        simpa [Metric.mem_ball, dist_eq_norm] using hDR hi
      have hcenter : ‖L • a i‖ = L / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hLpos, hsiteNorm i]
        ring
      have hnorm : ‖x‖ ≤ ‖x - L • a i‖ + ‖L • a i‖ := by
        calc
          ‖x‖ = ‖(x - L • a i) + L • a i‖ := by congr 1 <;> abel
          _ ≤ ‖x - L • a i‖ + ‖L • a i‖ := norm_add_le _ _
      have hstrict : ‖x‖ < R + L / 2 := by
        rw [hcenter] at hnorm
        linarith
      simpa [Metric.mem_ball, dist_eq_norm] using hstrict
    let G : WellGeometry d (Fin 2) :=
      { κ := (d : ℝ) + 2 * s
        hκ := by linarith [hs.1]
        R := R
        hR := hR
        D := D
        hDm := hDo.measurableSet
        hDR := hDR
        a := a
        L := L
        hL := hLpos
        hsep := hsep }
    have hopen : IsOpen (multiWellDomain D a L) := by
      change IsOpen G.Ω
      exact G.isOpen_Ω hDo
    have hne : (multiWellDomain D a L).Nonempty := by
      change G.Ω.Nonempty
      exact G.Ω_nonempty hDne
    have hsimple := eigenvalue_zero_lt_one hd s hs c hc (R + L / 2)
      (multiWellDomain D a L) hopen hne hball
    simpa [lambdaM, A, oneWellConstants] using hsimple
  have h01 : lambdaT L 0 < lambdaT L 1 := by
    simpa [lambdaT, lambdaM, a, twoWellDomain_eq, A, oneWellConstants] using h01M
  have h12 : lambdaT L 1 < lambdaT L 2 := by
    have hgapHalf := (htwoConclusion L hL).2.2.2
    have hg : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
    linarith
  exact ⟨h01, h12⟩


/-- Paper Theorem 3.3 with its exact hypothesis list: `D` is additionally
centrally symmetric (`D = -D`). -/
theorem twoWell_main_centrallySymmetric (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (_hDsymm : ∀ x, x ∈ D ↔ -x ∈ D)
    (φ : L2 d) (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (e : Eucl d) (he : ‖e‖ = 1) :
    let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
    A.twoWellStatement (fun L k => eigenvalue A.c A.kappa (twoWellDomain D e L) k) ∧
      ∀ L : ℝ, A.L0 ≤ L →
        eigenvalue A.c A.kappa (twoWellDomain D e L) 0 <
            eigenvalue A.c A.kappa (twoWellDomain D e L) 1 ∧
          eigenvalue A.c A.kappa (twoWellDomain D e L) 1 <
            eigenvalue A.c A.kappa (twoWellDomain D e L) 2 :=
  twoWell_main hd s hs c hc R hR D hDo hDne hDR φ hφ e he

end TwoWell

end Tunneling

