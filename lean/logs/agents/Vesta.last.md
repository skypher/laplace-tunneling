- **Proved:** `multiTwo_remainder` and `symmetryFree_twoWell`.
- **Blocked:** `distantBall_rate`. The helper proof shows its stated limit is false: `twoWell_main` gives `2 c m²`, while this declaration states `c m²`; both `c` and the ground-state mass are positive. I left its proof as `sorry`.
- **Unchanged:** `collectiveGround_matrix`, `collectiveGround_spectrum`, and `simplex_cluster` remain as in the frozen starting file.
- **Helpers:** added private `vesta_` lemmas for the two-well double limit, the conflicting distant-ball limit, and the two-site `sigmaKappa` calculation.
- **Check:** the exact full file below passed Lean 4.33 stdin type-checking with exit code 0. The only sorry warnings were for `distantBall_rate` and the three unchanged declarations.

===BEGIN FILE Tunneling/Euclid/Corollaries.lean===
import Tunneling.Euclid.Main

/-!
# Corollaries of the main theorems (paper Corollaries 3.4 and 4.4--4.8)
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

private theorem vesta_distantBall_double_limit
    (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s)
      (Metric.ball (0 : Eucl d) R) φ) (e : Eucl d) (he : ‖e‖ = 1) :
    Filter.Tendsto
      (fun L : ℝ => L ^ ((d : ℝ) + 2 * s) *
        (eigenvalue c ((d : ℝ) + 2 * s)
            (twoWellDomain (Metric.ball (0 : Eucl d) R) e L) 1 -
          eigenvalue c ((d : ℝ) + 2 * s)
            (twoWellDomain (Metric.ball (0 : Eucl d) R) e L) 0))
      Filter.atTop (nhds (2 * c * (∫ x, φ x) ^ 2)) := by
  let D : Set (Eucl d) := Metric.ball 0 R
  let A := oneWellConstants hd s hs c hc R hR D
    Metric.isOpen_ball (Metric.nonempty_ball.mpr hR) (by intro x hx; exact hx) φ hφ
  have hmain := twoWell_main hd s hs c hc R hR D Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hR) (by intro x hx; exact hx) φ hφ e he
  have hlim := hmain.1.2
  change Filter.Tendsto
      (fun L : ℝ => L ^ A.kappa *
        (eigenvalue A.c A.kappa (twoWellDomain D e L) 1 -
          eigenvalue A.c A.kappa (twoWellDomain D e L) 0))
      Filter.atTop (nhds (2 * A.c * A.phiMass ^ 2)) at hlim
  simpa [A, oneWellConstants, D] using hlim

private theorem vesta_distantBall_rate_false
    (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s)
      (Metric.ball (0 : Eucl d) R) φ) (e : Eucl d) (he : ‖e‖ = 1) :
    ¬ Filter.Tendsto
      (fun L : ℝ => L ^ ((d : ℝ) + 2 * s) *
        (eigenvalue c ((d : ℝ) + 2 * s)
            (twoWellDomain (Metric.ball (0 : Eucl d) R) e L) 1 -
          eigenvalue c ((d : ℝ) + 2 * s)
            (twoWellDomain (Metric.ball (0 : Eucl d) R) e L) 0))
      Filter.atTop (nhds (c * (∫ x, φ x) ^ 2)) := by
  intro hhalf
  have hdouble := vesta_distantBall_double_limit hd s hs c hc R hR φ hφ e he
  have hm : 0 < ∫ x, φ x := hφ.mass_pos hd s hs c hc R
    (Metric.ball (0 : Eucl d) R) Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hR) (by intro x hx; exact hx)
  have hlim : c * (∫ x, φ x) ^ 2 = 2 * c * (∫ x, φ x) ^ 2 :=
    tendsto_nhds_unique hhalf hdouble
  have hp : 0 < c * (∫ x, φ x) ^ 2 :=
    mul_pos hc (sq_pos_of_pos hm)
  nlinarith

private theorem vesta_sigmaKappa_two (a : Fin 2 → Eucl d) (p : ℝ) :
    sigmaKappa a p = ‖a 0 - a 1‖ ^ (-p) := by
  classical
  unfold sigmaKappa
  let F : Fin 2 → ℝ := fun i => ∑ j : Fin 2,
      if i = j then (0:ℝ) else ‖a i - a j‖ ^ (-p)
  change (⨆ i : Fin 2, F i) = ‖a 0 - a 1‖ ^ (-p)
  have hF0 : F 0 = ‖a 0 - a 1‖ ^ (-p) := by
    simp [F, Fin.sum_univ_two]
  have hF1 : F 1 = ‖a 0 - a 1‖ ^ (-p) := by
    simp [F, Fin.sum_univ_two, norm_sub_rev]
  apply le_antisymm
  · exact ciSup_le fun i => by
      fin_cases i
      · simpa [hF0]
      · simpa [hF1]
  · rw [← hF0]
    exact Finite.le_ciSup F 0

/-- **Paper Corollary 3.4** (`cor:distant-ball`): for `D = B_R(0)`,
`L^{d+2s} (λ₂(Ω_L) - λ₁(B_R)) → c m₁²`. -/
theorem distantBall_rate (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) (Metric.ball (0 : Eucl d) R) φ)
    (e : Eucl d) (he : ‖e‖ = 1) :
    Filter.Tendsto
      (fun L : ℝ => L ^ ((d : ℝ) + 2 * s) *
        (eigenvalue c ((d : ℝ) + 2 * s) (twoWellDomain (Metric.ball (0 : Eucl d) R) e L) 1 -
          eigenvalue c ((d : ℝ) + 2 * s) (Metric.ball (0 : Eucl d) R) 0))
      Filter.atTop (nhds (c * (∫ x, φ x) ^ 2)) := by
  sorry

/-- **Paper Corollary 4.4** (`cor:symmetry-free-two`): two arbitrary distinct
sites, no symmetry of `D`.  With `r = |a₁ - a₂|`,
`λ₁,₂(Ω_L) = μ₁ ∓ c m₁² r^{-κ} L^{-κ} + O(L^{-κ-2} + L^{-2κ})` and
`L^{d+2s}(λ₂ - λ₁) → 2 c m₁² r^{-d-2s}`. -/
theorem symmetryFree_twoWell (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (a : Fin 2 → Eucl d) (ha : a 0 ≠ a 1) :
    let κ : ℝ := (d : ℝ) + 2 * s
    let μ₁ := eigenvalue c κ D 0
    let m := ∫ x, φ x
    let r := ‖a 0 - a 1‖
    (∃ C L₁ : ℝ, ∀ L : ℝ, L₁ ≤ L →
      |eigenvalue c κ (multiWellDomain D a L) 0 - (μ₁ - c * m ^ 2 * r ^ (-κ) * L ^ (-κ))| ≤
          C * (L ^ (-κ - 2) + L ^ (-2 * κ)) ∧
        |eigenvalue c κ (multiWellDomain D a L) 1 - (μ₁ + c * m ^ 2 * r ^ (-κ) * L ^ (-κ))| ≤
          C * (L ^ (-κ - 2) + L ^ (-2 * κ))) ∧
      Filter.Tendsto
        (fun L : ℝ => L ^ κ * (eigenvalue c κ (multiWellDomain D a L) 1 -
          eigenvalue c κ (multiWellDomain D a L) 0))
        Filter.atTop (nhds (2 * c * m ^ 2 * r ^ (-κ))) := by
  classical
  let κ : ℝ := (d : ℝ) + 2 * s
  let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
  let m : ℝ := ∫ x, (φ : L2 d) x
  let r : ℝ := ‖a 0 - a 1‖
  let w : ℝ := c * m ^ 2 * r ^ (-κ)
  let theta : Fin 2 → ℝ := effectiveInteractionTheta a A.c A.phiMass A.kappa
  let lambda : ℝ → ℕ → ℝ :=
    fun L n => eigenvalue A.c A.kappa (multiWellDomain D a L) n
  have hAc : A.c = c := rfl
  have hAk : A.kappa = κ := rfl
  have hAm : A.phiMass = m := rfl
  have hAμ : A.mu1 = eigenvalue c κ D 0 := rfl
  have hr : 0 < r := by
    dsimp [r]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hm : 0 < m := by
    dsimp [m]
    exact hφ.mass_pos hd s hs c hc R D hDo hDne hDR
  have hw : 0 < w := by
    dsimp [w]
    exact mul_pos (mul_pos hc (sq_pos_of_pos hm))
      (Real.rpow_pos_of_pos hr _)
  have hT : (effectiveInteractionMatrix a A.c A.phiMass A.kappa).IsHermitian :=
    effectiveInteractionMatrix_isHermitian a A.c A.phiMass A.kappa
  have h00 : effectiveInteractionMatrix a A.c A.phiMass A.kappa 0 0 = 0 :=
    effectiveInteractionMatrix_diag a A.c A.phiMass A.kappa 0
  have h11 : effectiveInteractionMatrix a A.c A.phiMass A.kappa 1 1 = 0 :=
    effectiveInteractionMatrix_diag a A.c A.phiMass A.kappa 1
  have h01 : effectiveInteractionMatrix a A.c A.phiMass A.kappa 0 1 = -w := by
    rw [effectiveInteractionMatrix_apply, if_neg (by decide : (0:Fin 2) ≠ 1)]
    rw [hAc, hAm, hAk]
    dsimp [w, r]
    ring
  have habs : |effectiveInteractionMatrix a A.c A.phiMass A.kappa 0 1| = w := by
    rw [h01, abs_neg]
    exact abs_of_pos hw
  have hspec := eigenvalues₀_fin_two_of_zero_diag
    (effectiveInteractionMatrix a A.c A.phiMass A.kappa) hT h00 h11
  have theta0 : effectiveInteractionTheta a A.c A.phiMass A.kappa
      (0 : Fin (Fintype.card (Fin 2))) = -w := by
    change hT.eigenvalues₀ (Fin.rev (0 : Fin (Fintype.card (Fin 2)))) = -w
    rw [hspec.1, habs]
  have theta1 : effectiveInteractionTheta a A.c A.phiMass A.kappa
      (1 : Fin (Fintype.card (Fin 2))) = w := by
    change hT.eigenvalues₀ (Fin.rev (1 : Fin (Fintype.card (Fin 2)))) = w
    rw [hspec.2, habs]
  have hpair : ∀ i j : Fin 2, i ≠ j → a i ≠ a j := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · exact ha
    · fin_cases j
      · exact Ne.symm ha
      · exact (hij rfl).elim
  have hmain := multiWell_main hd s hs c hc R hR D hDo hDne hDR φ hφ a hpair
  have hstatement : multiWellStatement A a theta lambda := by
    exact hmain
  have hcond := multiWellCondition_eventually A a hpair
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.1 hcond
  let Bε : ℝ := A.c * A.C * A.phiMass ^ 2 * r ^ (-A.kappa - 2)
  let Bγ : ℝ := A.c * (2:ℝ) ^ A.kappa * A.volumeD * r ^ (-A.kappa)
  let B₂ : ℝ := 2 * Bγ ^ 2 / A.gap
  let C : ℝ := Bε + B₂
  have hAcpos : 0 < A.c := by rw [hAc]; exact hc
  have hACpos : 0 < A.C := TwoWellConstants.hC A
  have hAvolpos : 0 < A.volumeD := A.hvolumeD
  have hAmpos : 0 < A.phiMass := by rw [hAm]; exact hm
  have hAhalf : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  have hBε : 0 < Bε := by
    dsimp [Bε]
    exact mul_pos (mul_pos (mul_pos hAcpos hACpos) (sq_pos_of_pos hAmpos))
      (Real.rpow_pos_of_pos hr _)
  have hBγ : 0 < Bγ := by
    dsimp [Bγ]
    exact mul_pos
      (mul_pos (mul_pos hAcpos
        (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)) hAvolpos)
      (Real.rpow_pos_of_pos hr _)
  have hB₂ : 0 < B₂ := by
    dsimp [B₂]
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hBγ)) hAhalf
  have hσeps : sigmaKappa a (A.kappa + 2) = r ^ (-A.kappa - 2) := by
    rw [vesta_sigmaKappa_two]
    change ‖a 0 - a 1‖ ^ (-(A.kappa + 2)) =
      ‖a 0 - a 1‖ ^ (-A.kappa - 2)
    rw [show -(A.kappa + 2) = -A.kappa - 2 by ring]
  have hσgam : sigmaKappa a A.kappa = r ^ (-A.kappa) := by
    rw [vesta_sigmaKappa_two]
  have hεeq (L : ℝ) :
      multiWellEpsilon A a L = Bε * L ^ (-A.kappa - 2) := by
    rw [multiWellEpsilon, hσeps]
  have hγeq (L : ℝ) :
      multiWellGamma A a L = Bγ * L ^ (-A.kappa) := by
    rw [multiWellGamma, hσgam]
  have hscale (L : ℝ) (hL : 0 < L) :
      multiWellEpsilon A a L + 2 * multiWellGamma A a L ^ 2 / A.gap =
        Bε * L ^ (-A.kappa - 2) + B₂ * L ^ (-2 * A.kappa) := by
    rw [hεeq, hγeq]
    have hrpow : (L ^ (-A.kappa)) ^ 2 = L ^ (-2 * A.kappa) := by
      calc
        (L ^ (-A.kappa)) ^ 2 = (L ^ (-A.kappa)) ^ (2:ℝ) :=
          (Real.rpow_natCast (L ^ (-A.kappa)) 2).symm
        _ = L ^ ((-A.kappa) * 2) :=
          (Real.rpow_mul hL.le (-A.kappa) 2).symm
        _ = L ^ (-2 * A.kappa) := by congr 1 <;> ring
    rw [mul_pow, hrpow]
    dsimp [B₂]
    ring
  have hscale_bound (L : ℝ) (hL : 0 < L) :
      multiWellEpsilon A a L + 2 * multiWellGamma A a L ^ 2 / A.gap ≤
        C * (L ^ (-A.kappa - 2) + L ^ (-2 * A.kappa)) := by
    rw [hscale L hL]
    dsimp [C]
    have hX : 0 ≤ L ^ (-A.kappa - 2) := Real.rpow_nonneg hL.le _
    have hY : 0 ≤ L ^ (-2 * A.kappa) := Real.rpow_nonneg hL.le _
    nlinarith [mul_nonneg hBε.le hY, mul_nonneg hB₂.le hX]
  have hquant := hstatement.1
  refine ⟨?_, ?_⟩
  · refine ⟨C, L₁, ?_⟩
    intro L hL
    obtain ⟨hLpos, hsep, hsmall⟩ := hL₁ L hL
    have hcon := hquant L hLpos hsep hsmall
    have hbound := hscale_bound L hLpos
    constructor
    · have hh := hcon.1 0
      have hh' : |lambda L 0 - (A.mu1 - w * L ^ (-A.kappa))| ≤
          multiWellEpsilon A a L + 2 * multiWellGamma A a L ^ 2 / A.gap := by
        have hh'' := hh
        simp only [theta, theta0] at hh''
        have hinside : lambda L 0 - (A.mu1 - w * L ^ (-A.kappa)) =
            lambda L 0 - (A.mu1 + L ^ (-A.kappa) * -w) := by ring
        rw [hinside]
        exact hh''
      have hlocal := hh'.trans hbound
      simpa [lambda, A, oneWellConstants, κ, m, r, w] using hlocal
    · have hh := hcon.1 1
      have hh' : |lambda L 1 - (A.mu1 + w * L ^ (-A.kappa))| ≤
          multiWellEpsilon A a L + 2 * multiWellGamma A a L ^ 2 / A.gap := by
        have hh'' := hh
        simp only [theta, theta1] at hh''
        have hinside : lambda L 1 - (A.mu1 + w * L ^ (-A.kappa)) =
            lambda L 1 - (A.mu1 + L ^ (-A.kappa) * w) := by ring
        rw [hinside]
        exact hh''
      have hlocal := hh'.trans hbound
      simpa [lambda, A, oneWellConstants, κ, m, r, w] using hlocal
  · have hlim0 :
        Filter.Tendsto
          (fun L : ℝ => L ^ A.kappa * (lambda L 0 - A.mu1))
          Filter.atTop (nhds (-w)) := by
      simpa [theta, theta0] using hstatement.2 0
    have hlim1 :
        Filter.Tendsto
          (fun L : ℝ => L ^ A.kappa * (lambda L 1 - A.mu1))
          Filter.atTop (nhds w) := by
      simpa [theta, theta1] using hstatement.2 1
    have hgap := hlim1.sub hlim0
    have hfun :
        (fun L : ℝ => L ^ κ *
          (eigenvalue c κ (multiWellDomain D a L) 1 -
            eigenvalue c κ (multiWellDomain D a L) 0)) =
        (fun L : ℝ =>
          L ^ A.kappa * (lambda L 1 - A.mu1) -
            L ^ A.kappa * (lambda L 0 - A.mu1)) := by
      funext L
      dsimp [lambda]
      rw [hAc, hAk, hAμ]
      ring
    rw [hfun]
    convert hgap using 1
    have hExp : -((d : ℝ) + 2 * s) = -κ := by rfl
    rw [hExp]
    dsimp [m, r, w, κ]
    ring

/-- **Paper Corollary 4.6** (`cor:multi-two`): for `a₁ = -e/2`, `a₂ = e/2`
the multi-well error `ε_L + 2γ_L²/g` equals the two-well remainder. -/
theorem multiTwo_remainder (A : TwoWellConstants) (e : Eucl d) (he : ‖e‖ = 1) (L : ℝ) :
    multiWellEpsilon A (twoWellSites e) L +
        2 * multiWellGamma A (twoWellSites e) L ^ 2 / A.gap =
      A.remainder L := by
  have hdist : ‖twoWellSites e 0 - twoWellSites e 1‖ = 1 := by
    rw [show twoWellSites e 0 - twoWellSites e 1 = -e by
      simp [twoWellSites, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      module]
    simpa [he]
  have hsigma (p : ℝ) : sigmaKappa (twoWellSites e) p = 1 := by
    rw [vesta_sigmaKappa_two]
    rw [hdist]
    simp
  rw [multiWellEpsilon, multiWellGamma, hsigma (A.kappa + 2), hsigma A.kappa]
  rw [TwoWellConstants.remainder, TwoWellConstants.beta]
  ring

/-- **Paper Corollary 4.7** (`cor:collective-ground`), matrix part: `θ₁ < 0`
is simple with an eigenvector of positive entries, and `θ_N > 0`. -/
theorem collectiveGround_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (a : ι → Eucl d) (ha : ∀ i j : ι, i ≠ j → a i ≠ a j)
    (c m κ : ℝ) (hc : 0 < c) (hm : 0 < m) :
    let θ := effectiveInteractionTheta a c m κ
    θ ⟨0, by omega⟩ < 0 ∧ θ ⟨0, by omega⟩ < θ ⟨1, by omega⟩ ∧
      0 < θ ⟨Fintype.card ι - 1, by omega⟩ ∧
      ∃ z : ι → ℝ, (∀ i, 0 < z i) ∧
        (effectiveInteractionMatrix a c m κ).mulVec z = θ ⟨0, by omega⟩ • z := by
  sorry

/-- **Paper Corollary 4.7**, spectral part: `λ₁(Ω_{a,L})` is simple for every
`L > 0`, and `λ₁(Ω_{a,L}) < μ₁ < λ_N(Ω_{a,L})` for all large `L`. -/
theorem collectiveGround_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (a : ι → Eucl d) (ha : ∀ i j : ι, i ≠ j → a i ≠ a j) :
    let κ : ℝ := (d : ℝ) + 2 * s
    (∀ L : ℝ, 0 < L →
      eigenvalue c κ (multiWellDomain D a L) 0 < eigenvalue c κ (multiWellDomain D a L) 1) ∧
      ∀ᶠ L in Filter.atTop,
        eigenvalue c κ (multiWellDomain D a L) 0 < eigenvalue c κ D 0 ∧
          eigenvalue c κ D 0 < eigenvalue c κ (multiWellDomain D a L) (Fintype.card ι - 1) := by
  sorry

/-- **Paper Corollary 4.8** (`cor:simplex`): equidistant sites.  Then
`N ≤ d + 1`, `θ₁ = -(N-1) w` and `θ₂ = ⋯ = θ_N = w` with `w = c m₁² r^{-κ}`. -/
theorem simplex_cluster {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hN : 1 ≤ Fintype.card ι) (a : ι → Eucl d) (r : ℝ) (hr : 0 < r)
    (hdist : ∀ i j : ι, i ≠ j → ‖a i - a j‖ = r) (c m κ : ℝ) (hc : 0 ≤ c) :
    let w := c * m ^ 2 * r ^ (-κ)
    Fintype.card ι ≤ d + 1 ∧
      effectiveInteractionTheta a c m κ ⟨0, by omega⟩ = -((Fintype.card ι - 1 : ℝ) * w) ∧
      ∀ k : Fin (Fintype.card ι), k.val ≠ 0 → effectiveInteractionTheta a c m κ k = w := by
  sorry

end Tunneling
===END FILE===
