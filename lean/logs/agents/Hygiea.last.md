- `collectiveGround_matrix`: proved using `ground_simple_of_neg_offdiag` and the extreme-sign theorem.
- `collectiveGround_spectrum`: proved using `eigenvalue_zero_lt_one` and the limit from `multiWell_main`.
- Preserved unchanged: `distantBall_rate`, `symmetryFree_twoWell`, `multiTwo_remainder`, and `simplex_cluster`; their `sorry`s are outside this focused assignment.
- Added private helpers `hygiea_multiWellDomain_open` and `hygiea_multiWellDomain_subset_ball`, plus the Perron–Frobenius import. The style option suppresses only the `haveI` linter suggestions.
- Type-checked the complete delivered file with Lean 4.33 via `lean --stdin`. No errors; the only warnings were the four preserved `sorry`s.

===BEGIN FILE Tunneling/Euclid/Corollaries.lean===
import Tunneling.Euclid.Main
import Tunneling.Spectral.PerronFrobenius

/-!
# Corollaries of the main theorems (paper Corollaries 3.4 and 4.4--4.8)
-/

set_option linter.style.haveILetI false

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

private theorem hygiea_multiWellDomain_open {ι : Type*} [Fintype ι]
    (D : Set (Eucl d)) (a : ι → Eucl d) (L : ℝ) (hDo : IsOpen D) :
    IsOpen (multiWellDomain D a L) := by
  unfold multiWellDomain
  rw [Set.ofPred_exists]
  exact isOpen_iUnion fun j => hDo.preimage (continuous_id.sub continuous_const)

private theorem hygiea_multiWellDomain_subset_ball {ι : Type*} [Fintype ι]
    (R L : ℝ) (hL : 0 < L) (D : Set (Eucl d)) (hDR : D ⊆ Metric.ball 0 R)
    (a : ι → Eucl d) :
    multiWellDomain D a L ⊆ Metric.ball 0 (R + L * ∑ j : ι, ‖a j‖ + 1) := by
  intro x hx
  rcases hx with ⟨j, hj⟩
  have hy : ‖x - L • a j‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hDR hj
  have hsum : ‖a j‖ ≤ ∑ i : ι, ‖a i‖ := by
    exact Finset.single_le_sum (s := Finset.univ) (f := fun i => ‖a i‖)
      (fun i hi => norm_nonneg _) (Finset.mem_univ j)
  have hmul : L * ‖a j‖ ≤ L * ∑ i : ι, ‖a i‖ := mul_le_mul_of_nonneg_left hsum hL.le
  have hsmul : ‖L • a j‖ = L * ‖a j‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have hxadd : x = (x - L • a j) + L • a j := by abel
  have hnorm : ‖x‖ < R + L * ∑ i : ι, ‖a i‖ + 1 := by
    rw [hxadd]
    calc
      ‖(x - L • a j) + L • a j‖ ≤ ‖x - L • a j‖ + ‖L • a j‖ := norm_add_le _ _
      _ < R + L * ∑ i : ι, ‖a i‖ + 1 := by rw [hsmul]; nlinarith
  have hdist : dist x 0 < R + L * ∑ i : ι, ‖a i‖ + 1 := by simpa [dist_eq_norm] using hnorm
  simpa [Metric.mem_ball] using hdist

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
  sorry

/-- **Paper Corollary 4.6** (`cor:multi-two`): for `a₁ = -e/2`, `a₂ = e/2`
the multi-well error `ε_L + 2γ_L²/g` equals the two-well remainder. -/
theorem multiTwo_remainder (A : TwoWellConstants) (e : Eucl d) (he : ‖e‖ = 1) (L : ℝ) :
    multiWellEpsilon A (twoWellSites e) L +
        2 * multiWellGamma A (twoWellSites e) L ^ 2 / A.gap =
      A.remainder L := by
  sorry

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
  classical
  dsimp
  haveI : NeZero (Fintype.card ι) := ⟨by omega⟩
  let A := effectiveInteractionMatrix a c m κ
  have hA : A.IsHermitian := by
    simpa [A] using effectiveInteractionMatrix_isHermitian a c m κ
  have hoff : ∀ i j, i ≠ j → A i j < 0 := by
    intro i j hij
    have hnorm : 0 < ‖a i - a j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (ha i j hij))
    have hpow : 0 < ‖a i - a j‖ ^ (-κ) := Real.rpow_pos_of_pos hnorm _
    have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
    have hprod : -c * m ^ 2 * ‖a i - a j‖ ^ (-κ) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hm2) hpow
    simpa [A, effectiveInteractionMatrix_apply, hij] using hprod
  have hpf := ground_simple_of_neg_offdiag A hA hN hoff
  let i : ι := Classical.choice (Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι))
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι) i
  have hsign := effectiveInteractionTheta_extreme_signs_of_distinct
    a c m κ i j (Ne.symm hji) (ha i j (Ne.symm hji)) hc.ne' hm.ne'
  have hrev0 : Fin.rev (⟨0, by omega⟩ : Fin (Fintype.card ι)) = ⊤ := by
    apply Fin.ext
    simp [Fin.rev]
  have hlast : (⟨Fintype.card ι - 1, by omega⟩ : Fin (Fintype.card ι)) = ⊤ := by
    apply Fin.ext
    simp
  have hrevLast : Fin.rev (⟨Fintype.card ι - 1, by omega⟩ : Fin (Fintype.card ι)) = ⊥ := by
    rw [hlast]
    exact Fin.rev_top
  have htopneg : (effectiveInteractionMatrix_isHermitian a c m κ).eigenvalues₀ ⊤ < 0 := by
    simpa [effectiveInteractionTheta] using hsign.1
  have hbotpos : 0 < (effectiveInteractionMatrix_isHermitian a c m κ).eigenvalues₀ ⊥ := by
    simpa [effectiveInteractionTheta] using hsign.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (effectiveInteractionMatrix_isHermitian a c m κ).eigenvalues₀
      (Fin.rev (⟨0, by omega⟩ : Fin (Fintype.card ι))) < 0
    rw [hrev0]
    exact htopneg
  · simpa [effectiveInteractionTheta] using hpf.1
  · change 0 < (effectiveInteractionMatrix_isHermitian a c m κ).eigenvalues₀
      (Fin.rev (⟨Fintype.card ι - 1, by omega⟩ : Fin (Fintype.card ι)))
    rw [hrevLast]
    exact hbotpos
  · rcases hpf.2 with ⟨z, hz, hn, he⟩
    exact ⟨z, hz, by simpa [effectiveInteractionTheta] using he⟩

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
  classical
  dsimp
  let κ : ℝ := (d : ℝ) + 2 * s
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  refine ⟨?_, ?_⟩
  · intro L hL
    let B : ℝ := R + L * ∑ j : ι, ‖a j‖ + 1
    have hopen : IsOpen (multiWellDomain D a L) := hygiea_multiWellDomain_open D a L hDo
    have hne : (multiWellDomain D a L).Nonempty := by
      obtain ⟨x, hx⟩ := hDne
      let j : ι := Classical.choice (inferInstance : Nonempty ι)
      refine ⟨x + L • a j, ⟨j, ?_⟩⟩
      simpa using hx
    have hsub : multiWellDomain D a L ⊆ Metric.ball 0 B := by
      simpa [B] using hygiea_multiWellDomain_subset_ball R L hL D hDR a
    exact eigenvalue_zero_lt_one hd s hs c hc B (multiWellDomain D a L) hopen hne hsub
  · have hmass : 0 < (∫ x, φ x) := hφ.mass_pos hd s hs c hc R D hDo hDne hDR
    rcases collectiveGround_matrix hN a ha c (∫ x, φ x) ((d : ℝ) + 2 * s) hc hmass with
      ⟨hθneg, hθsimple, hθlast, hz⟩
    have hlimit : ∀ k : Fin (Fintype.card ι), Filter.Tendsto
        (fun L : ℝ => L ^ ((d : ℝ) + 2 * s) *
          (eigenvalue c ((d : ℝ) + 2 * s) (multiWellDomain D a L) k.val -
            eigenvalue c ((d : ℝ) + 2 * s) D 0))
        Filter.atTop (nhds (effectiveInteractionTheta a c (∫ x, φ x) ((d : ℝ) + 2 * s) k)) := by
      intro k
      simpa [oneWellConstants] using
        (multiWell_main hd s hs c hc R hR D hDo hDne hDR φ hφ a ha).2 k
    let k0 : Fin (Fintype.card ι) := ⟨0, by omega⟩
    let klast : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
    have hlim0 := hlimit k0
    have hlimlast := hlimit klast
    have hEv0 : ∀ᶠ L : ℝ in Filter.atTop,
        L ^ ((d : ℝ) + 2 * s) *
          (eigenvalue c ((d : ℝ) + 2 * s) (multiWellDomain D a L) 0 -
            eigenvalue c ((d : ℝ) + 2 * s) D 0) < 0 := by
      have hlt : Set.Iio (0 : ℝ) ∈ nhds (effectiveInteractionTheta a c (∫ x, φ x)
          ((d : ℝ) + 2 * s) k0) := Iio_mem_nhds hθneg
      filter_upwards [hlim0.eventually hlt] with L hL
      simpa [k0] using hL
    have hEvlast : ∀ᶠ L : ℝ in Filter.atTop,
        0 < L ^ ((d : ℝ) + 2 * s) *
          (eigenvalue c ((d : ℝ) + 2 * s) (multiWellDomain D a L) (Fintype.card ι - 1) -
            eigenvalue c ((d : ℝ) + 2 * s) D 0) := by
      have hgt : Set.Ioi (0 : ℝ) ∈ nhds (effectiveInteractionTheta a c (∫ x, φ x)
          ((d : ℝ) + 2 * s) klast) := Ioi_mem_nhds hθlast
      filter_upwards [hlimlast.eventually hgt] with L hL
      simpa [klast] using hL
    filter_upwards [hEv0, hEvlast, Filter.eventually_gt_atTop (0 : ℝ)] with L h0 hlast hL
    have hpow : 0 < L ^ ((d : ℝ) + 2 * s) := Real.rpow_pos_of_pos hL _
    have hdiff0 : eigenvalue c ((d : ℝ) + 2 * s) (multiWellDomain D a L) 0 -
        eigenvalue c ((d : ℝ) + 2 * s) D 0 < 0 := by
      apply (mul_lt_mul_iff_of_pos_left hpow).mp
      simpa using h0
    have hdiffLast : 0 < eigenvalue c ((d : ℝ) + 2 * s)
        (multiWellDomain D a L) (Fintype.card ι - 1) -
          eigenvalue c ((d : ℝ) + 2 * s) D 0 := by
      apply (mul_lt_mul_iff_of_pos_left hpow).mp
      simpa using hlast
    constructor <;> linarith

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
