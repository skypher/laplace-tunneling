import Tunneling.Euclid.GroundState
import Tunneling.Euclid.Decomp
import Tunneling.Final

/-!
# Auxiliary statements for the main theorems
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- A nonempty bounded open set has finite positive volume. -/
theorem volume_toReal_pos_of_isOpen (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) :
    0 < (volume D).toReal := by
  have hpos : 0 < (volume : Measure (Eucl d)) D := hDo.measure_pos _ hDne
  have hfin : (volume : Measure (Eucl d)) D < ⊤ :=
    (Metric.isBounded_ball.subset hDR).measure_lt_top
  exact ENNReal.toReal_pos hpos.ne' hfin.ne

/-- The fixed one-well data of paper Section 2 (`κ = d + 2s`, `|D|`, `μ₁`,
`μ₂`, `m₁ = ∫ φ₁`) packaged for the algebraic statements of
`Tunneling.Statements` and `Tunneling.MultiWell`. -/
noncomputable def oneWellConstants (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) (φ : L2 d)
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ) : TwoWellConstants where
  d := d
  s := s
  hs := hs
  kappa := (d : ℝ) + 2 * s
  hkappa := rfl
  c := c
  hc := hc
  R := R
  hR := hR
  volumeD := (volume D).toReal
  hvolumeD := volume_toReal_pos_of_isOpen R D hDo hDne hDR
  mu1 := eigenvalue c ((d : ℝ) + 2 * s) D 0
  mu2 := eigenvalue c ((d : ℝ) + 2 * s) D 1
  hgap := sub_pos.2 (eigenvalue_zero_lt_one hd s hs c hc R D hDo hDne hDR)
  phiMass := ∫ x, φ x
  hphiMass := hφ.mass_pos hd s hs c hc R D hDo hDne hDR

section TwoWellAux

/-- The two-well domain `Ω_L = (D - (L/2) e) ∪ (D + (L/2) e)` of paper
Section 2. -/
def twoWellDomain (D : Set (Eucl d)) (e : Eucl d) (L : ℝ) : Set (Eucl d) :=
  {x | x + (L / 2) • e ∈ D ∨ x - (L / 2) • e ∈ D}

/-- The two sites `a₁ = -e/2`, `a₂ = e/2`. -/
noncomputable def twoWellSites (e : Eucl d) : Fin 2 → Eucl d :=
  ![-((1 / 2 : ℝ) • e), (1 / 2 : ℝ) • e]

theorem twoWellDomain_eq (D : Set (Eucl d)) (e : Eucl d) (L : ℝ) :
    twoWellDomain D e L = multiWellDomain D (twoWellSites e) L := by
  ext x
  constructor
  · intro hx
    change x + (L / 2) • e ∈ D ∨ x - (L / 2) • e ∈ D at hx
    change ∃ j : Fin 2, x - L • twoWellSites e j ∈ D
    rcases hx with hx | hx
    · refine ⟨0, ?_⟩
      simpa [twoWellSites, Matrix.cons_val_zero, smul_smul, smul_neg, div_eq_mul_inv,
        mul_comm] using hx
    · refine ⟨1, ?_⟩
      simpa [twoWellSites, Matrix.cons_val_one, Matrix.head_cons, smul_smul, div_eq_mul_inv, mul_comm] using hx
  · intro hx
    change ∃ j : Fin 2, x - L • twoWellSites e j ∈ D at hx
    change x + (L / 2) • e ∈ D ∨ x - (L / 2) • e ∈ D
    rcases hx with ⟨j, hj⟩
    fin_cases j
    · left
      simpa [twoWellSites, Matrix.cons_val_zero, smul_smul, smul_neg, div_eq_mul_inv,
        mul_comm] using hj
    · right
      simpa [twoWellSites, Matrix.cons_val_one, Matrix.head_cons, smul_smul, div_eq_mul_inv, mul_comm] using hj

/-- Ordered eigenvalues of a real symmetric `2 × 2` matrix with zero
diagonal. -/
theorem eigenvalues₀_fin_two_of_zero_diag (T : Matrix (Fin 2) (Fin 2) ℝ)
    (hT : T.IsHermitian) (h00 : T 0 0 = 0) (h11 : T 1 1 = 0) :
    hT.eigenvalues₀ (Fin.rev 0) = -|T 0 1| ∧ hT.eigenvalues₀ (Fin.rev 1) = |T 0 1| := by
  have hsym : T 1 0 = T 0 1 := by simpa using hT.apply 0 1
  let e : Fin 2 ≃ Fin (Fintype.card (Fin 2)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  have heig : ∀ i : Fin 2, hT.eigenvalues i = hT.eigenvalues₀ (e i) := fun i => rfl
  have hsumEquiv : (∑ i : Fin 2, (hT.eigenvalues i : ℝ)) =
      ∑ j : Fin (Fintype.card (Fin 2)), hT.eigenvalues₀ j := by
    calc
      _ = ∑ i : Fin 2, hT.eigenvalues₀ (e i) := by simp only [heig]
      _ = _ := Equiv.sum_comp e hT.eigenvalues₀
  have htrace := hT.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at htrace
  have hsum2 : (∑ j : Fin (Fintype.card (Fin 2)), hT.eigenvalues₀ j) =
      hT.eigenvalues₀ 0 + hT.eigenvalues₀ 1 := Fin.sum_univ_two _
  rw [hsumEquiv, hsum2] at htrace
  have htrace0 : T.trace = 0 := by
    rw [Matrix.trace_fin_two, h00, h11]
    ring
  rw [htrace0] at htrace
  have hsum : hT.eigenvalues₀ 0 + hT.eigenvalues₀ 1 = 0 := htrace.symm
  have hprodEquiv : (∏ i : Fin 2, (hT.eigenvalues i : ℝ)) =
      ∏ j : Fin (Fintype.card (Fin 2)), hT.eigenvalues₀ j := by
    calc
      _ = ∏ i : Fin 2, hT.eigenvalues₀ (e i) := by simp only [heig]
      _ = _ := Equiv.prod_comp e hT.eigenvalues₀
  have hdet := hT.det_eq_prod_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hdet
  have hprod2 : (∏ j : Fin (Fintype.card (Fin 2)), hT.eigenvalues₀ j) =
      hT.eigenvalues₀ 0 * hT.eigenvalues₀ 1 := Fin.prod_univ_two _
  rw [hprodEquiv, hprod2] at hdet
  have hdet0 : T.det = -(T 0 1)^2 := by
    rw [Matrix.det_fin_two, h00, h11, hsym]
    ring
  rw [hdet0] at hdet
  have hprod : hT.eigenvalues₀ 0 * hT.eigenvalues₀ 1 = -(T 0 1)^2 := hdet.symm
  have horder : hT.eigenvalues₀ 1 ≤ hT.eigenvalues₀ 0 :=
    hT.eigenvalues₀_antitone (by norm_num)
  have hu_nonneg : 0 ≤ hT.eigenvalues₀ 0 := by nlinarith
  have hu_sq : (hT.eigenvalues₀ 0)^2 = (T 0 1)^2 := by nlinarith
  have hu_abs : |hT.eigenvalues₀ 0| = |T 0 1| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp hu_sq
  have hu : hT.eigenvalues₀ 0 = |T 0 1| := by
    rw [← abs_of_nonneg hu_nonneg]
    exact hu_abs
  have hv : hT.eigenvalues₀ 1 = -|T 0 1| := by nlinarith [hsum, hu]
  have hrev0 : Fin.rev (0 : Fin (Fintype.card (Fin 2))) = 1 := by decide
  have hrev1 : Fin.rev (1 : Fin (Fintype.card (Fin 2))) = 0 := by decide
  constructor
  · rw [hrev0]; exact hv
  · rw [hrev1]; exact hu

/-- The strict second inequality in `eq:L0-conditions`:
`2 c m₁² (L + 2R)^{-κ} > 4 β_L² / g`. -/
theorem L0_simplicity_condition (A : TwoWellConstants) (L : ℝ) (hL : A.L0 ≤ L) :
    4 * A.beta L ^ 2 / A.gap < 2 * A.c * A.phiMass ^ 2 * (L + 2 * A.R) ^ (-A.kappa) := by
  have hk : 0 < A.kappa := A.kappa_pos
  have hg : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  have hLfirst : 4 * A.R ≤ L := by
    have hfirst : 4 * A.R ≤ A.L0 := by
      unfold TwoWellConstants.L0
      exact le_max_left _ _
    exact hfirst.trans hL
  let B : ℝ := 2 * A.c * (4:ℝ)^A.kappa * A.volumeD^2 /
    (A.gap * A.phiMass^2)
  have hLthreshold : 2 * B^(1/A.kappa) ≤ L := by
    have hthird : 2 * B^(1/A.kappa) ≤ A.L0 := by
      unfold TwoWellConstants.L0
      dsimp [B]
      exact (le_max_right _ _).trans (le_max_right _ _)
    exact hthird.trans hL
  have hLpos : 0 < L := by
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0:ℝ)<4) A.hR) hLfirst
  have hBpos : 0 < B := by
    dsimp [B]
    refine div_pos ?_ (mul_pos hg (sq_pos_of_pos A.hphiMass))
    have hc := A.hc
    have hV := A.hvolumeD
    positivity
  have hrootpos : 0 < B^(1/A.kappa) := Real.rpow_pos_of_pos hBpos _
  have hrootpow : (B^(1/A.kappa))^A.kappa = B := by
    rw [← Real.rpow_mul hBpos.le, one_div_mul_cancel hk.ne', Real.rpow_one]
  have hpowerlower : (2 * B^(1/A.kappa))^A.kappa ≤ L^A.kappa :=
    Real.rpow_le_rpow (mul_nonneg (by norm_num) hrootpos.le) hLthreshold hk.le
  have hexp : (2 * B^(1/A.kappa))^A.kappa = (2:ℝ)^A.kappa * B := by
    rw [Real.mul_rpow (by norm_num) hrootpos.le, hrootpow]
  have hpowerlower' : (2:ℝ)^A.kappa * B ≤ L^A.kappa := by
    rw [← hexp]
    exact hpowerlower
  have hcompare : ((3:ℝ)/2)^A.kappa < (2:ℝ)^A.kappa :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hk
  let p : ℝ := ((3:ℝ)/2)^A.kappa
  let q : ℝ := L^A.kappa
  have hp : 0 < p := Real.rpow_pos_of_pos (by norm_num) _
  have hq : 0 < q := Real.rpow_pos_of_pos hLpos _
  have hBQ : p * B < q := by
    dsimp [p, q]
    calc
      ((3:ℝ)/2)^A.kappa * B < (2:ℝ)^A.kappa * B := mul_lt_mul_of_pos_right hcompare hBpos
      _ ≤ L^A.kappa := hpowerlower'
  have hfrac : B / q^2 < 1 / (p*q) := by
    rw [div_lt_div_iff₀ (sq_pos_of_pos hq) (mul_pos hp hq)]
    have hmul := mul_lt_mul_of_pos_right hBQ hq
    have hnum : B * (p*q) < q^2 := by
      calc
        B * (p*q) = (p*B)*q := by ring
        _ < q*q := hmul
        _ = q^2 := by ring
    simpa using hnum
  have hbetaCoeff : A.beta L =
      (A.c * (2:ℝ)^A.kappa * A.volumeD) / q := by
    calc
      A.beta L = (A.c * (2:ℝ)^A.kappa * A.volumeD) * (L^A.kappa)⁻¹ := by
        simp [TwoWellConstants.beta, Real.rpow_neg hLpos.le]
      _ = (A.c * (2:ℝ)^A.kappa * A.volumeD) / q := by simp [q, div_eq_mul_inv]
  let S : ℝ := 2 * A.c * A.phiMass^2
  have hS : 0 < S := by
    dsimp [S]
    exact mul_pos (mul_pos (by norm_num) A.hc) (pow_pos A.hphiMass 2)
  have hfour : (4:ℝ)^A.kappa = ((2:ℝ)^A.kappa)^2 := by
    rw [show (4:ℝ) = 2*2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
    ring
  have hleft : 4 * A.beta L^2 / A.gap = S * (B/q^2) := by
    rw [hbetaCoeff]
    dsimp [S, B, q]
    field_simp [hg.ne', A.hc.ne', A.hphiMass.ne', hq.ne']
    rw [hfour]
    ring
  have hscaled := mul_lt_mul_of_pos_left hfrac hS
  have hlowpow : (((3:ℝ)/2)*L)^(-A.kappa) = 1/(p*q) := by
    rw [Real.mul_rpow (by norm_num) hLpos.le,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ (3:ℝ)/2),
      Real.rpow_neg hLpos.le]
    dsimp [p, q]
    field_simp [hp.ne', hq.ne']
  have hplusPos : 0 < L + 2*A.R := add_pos hLpos (mul_pos (by norm_num) A.hR)
  have hsumle : L + 2*A.R ≤ ((3:ℝ)/2)*L := by nlinarith [hLfirst]
  have hpowmon : (((3:ℝ)/2)*L)^(-A.kappa) ≤ (L+2*A.R)^(-A.kappa) :=
    Real.rpow_le_rpow_of_nonpos hplusPos hsumle (neg_nonpos.mpr hk.le)
  calc
    4 * A.beta L^2 / A.gap = S * (B/q^2) := hleft
    _ < S * (1/(p*q)) := hscaled
    _ = S * (((3:ℝ)/2)*L)^(-A.kappa) := by rw [hlowpow]
    _ ≤ S * (L+2*A.R)^(-A.kappa) := mul_le_mul_of_nonneg_left hpowmon hS.le

end TwoWellAux

end Tunneling
