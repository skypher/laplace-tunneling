import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic

/-!
# Exact source extraction for the tunneling conclusions

This file records the algebraic content of the paper's main conclusions before
the fractional operator and spectral interfaces are constructed.  The
propositions below are deliberately ordinary `Prop` definitions: they have no
axioms, no `sorry`, and no hidden approximation convention.
-/

namespace Tunneling

/-- The constants and threshold in Theorem 3.3. -/
structure TwoWellConstants where
  d : ℕ
  s : ℝ
  hs : 0 < s ∧ s < 1
  kappa : ℝ
  hkappa : kappa = d + 2 * s
  c : ℝ
  hc : 0 < c
  R : ℝ
  hR : 0 < R
  volumeD : ℝ
  hvolumeD : 0 < volumeD
  mu1 : ℝ
  mu2 : ℝ
  hgap : 0 < mu2 - mu1
  phiMass : ℝ
  hphiMass : 0 < phiMass

namespace TwoWellConstants

/-- The kernel exponent is positive in the paper's range `s in (0,1)`. -/
theorem kappa_pos (A : TwoWellConstants) : 0 < A.kappa := by
  rw [A.hkappa]
  have hd : (0:ℝ) ≤ (A.d : ℝ) := Nat.cast_nonneg _
  nlinarith [A.hs.1, hd]

/-- The explicit kernel-expansion constant from equation `eq:kernel-expansion`. -/
noncomputable def C (A : TwoWellConstants) : ℝ :=
  (2:ℝ) ^ (A.kappa + 3) * A.kappa * (A.kappa + 1) * A.R ^ 2

theorem hC (A : TwoWellConstants) : 0 < A.C := by
  have hk := A.kappa_pos
  have hpow : 0 < (2:ℝ) ^ (A.kappa + 3) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hk1 : 0 < A.kappa + 1 := by positivity
  have hR2 : 0 < A.R ^ 2 := pow_pos A.hR 2
  exact mul_pos (mul_pos (mul_pos hpow hk) hk1) hR2

/-- The spectral gap `g = mu_2 - mu_1`. -/
def gap (A : TwoWellConstants) : ℝ := A.mu2 - A.mu1

/-- The interaction bound `beta_L` from Lemma 3.2. -/
noncomputable def beta (A : TwoWellConstants) (L : ℝ) : ℝ :=
  A.c * 2 ^ A.kappa * A.volumeD * L ^ (-A.kappa)

theorem beta_nonneg (A : TwoWellConstants) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ A.beta L := by
  have h2 : (0:ℝ) ≤ (2:ℝ) ^ A.kappa :=
    Real.rpow_nonneg (by norm_num) _
  have hLpow : (0:ℝ) ≤ L ^ (-A.kappa) :=
    Real.rpow_nonneg hL _
  have hbase : 0 ≤ A.c * (2:ℝ) ^ A.kappa * A.volumeD := by
    have hca : 0 ≤ A.c * (2:ℝ) ^ A.kappa :=
      mul_nonneg A.hc.le h2
    exact mul_nonneg hca A.hvolumeD.le
  simpa [TwoWellConstants.beta] using mul_nonneg hbase hLpow

/-- The explicit threshold `L_0` from Theorem 3.3. -/
noncomputable def L0 (A : TwoWellConstants) : ℝ :=
  max (4 * A.R)
    (max
      ((4 * A.c * 2 ^ A.kappa * A.volumeD / A.gap) ^ (1 / A.kappa))
      (2 * ((2 * A.c * 4 ^ A.kappa * A.volumeD ^ 2 /
        (A.gap * A.phiMass ^ 2)) ^ (1 / A.kappa))))

/-- The smallness condition in equation `eq:L0-conditions`, following from
the first threshold in `L0`. -/
theorem beta_small (A : TwoWellConstants) {L : ℝ} (hL : A.L0 ≤ L) :
    A.beta L ≤ A.gap / 4 := by
  have hk := A.kappa_pos
  have hgap : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
  have h4pos : (0:ℝ) < 4 := by norm_num
  have h4nonneg : (0:ℝ) ≤ 4 := h4pos.le
  have h2 : 0 < (2:ℝ) ^ A.kappa := Real.rpow_pos_of_pos (by norm_num) _
  have hprod1 : 0 < (4:ℝ) * A.c := mul_pos h4pos A.hc
  have hprod2 : 0 < (4:ℝ) * A.c * (2:ℝ) ^ A.kappa := mul_pos hprod1 h2
  have hprod3 : 0 < (4:ℝ) * A.c * (2:ℝ) ^ A.kappa * A.volumeD :=
    mul_pos hprod2 A.hvolumeD
  have hbase : 0 <
      (4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap) := by
    exact div_pos hprod3 hgap
  have hthreshold :
      (4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap) ^ (1 / A.kappa) ≤ A.L0 := by
    refine le_trans (le_max_left _ _) (le_max_right _ _)
  have hthresholdPos : 0 <
      (4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap) ^ (1 / A.kappa) :=
    Real.rpow_pos_of_pos hbase _
  have hLpos : 0 < L := lt_of_lt_of_le hthresholdPos (le_trans hthreshold hL)
  have hthresholdNonneg : 0 ≤
      (4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap) ^ (1 / A.kappa) :=
    hthresholdPos.le
  have hpowle :
      ((4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap) ^ (1 / A.kappa)) ^ A.kappa ≤
        L ^ A.kappa :=
    Real.rpow_le_rpow hthresholdNonneg (le_trans hthreshold hL) hk.le
  have hthresholdpow :
      ((4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap) ^ (1 / A.kappa)) ^ A.kappa =
        4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap := by
    rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hk.ne', Real.rpow_one]
  have hbasele :
      4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap ≤ L ^ A.kappa := by
    rw [← hthresholdpow]
    exact hpowle
  set P : ℝ := A.c * (2:ℝ) ^ A.kappa * A.volumeD with hP
  have hPnonneg : 0 ≤ P := by
    have h2 : 0 ≤ (2:ℝ) ^ A.kappa := Real.rpow_nonneg (by norm_num) _
    have hca : 0 ≤ A.c * (2:ℝ) ^ A.kappa := mul_nonneg A.hc.le h2
    simpa [P] using mul_nonneg hca A.hvolumeD.le
  have hbaseForm :
      4 * P / A.gap = 4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap := by
    simp [P]
    ring
  have hPbound : P ≤ A.gap / 4 * L ^ A.kappa := by
    have hmul :
        (A.gap / 4) *
          (4 * A.c * (2:ℝ) ^ A.kappa * A.volumeD / A.gap) ≤
        (A.gap / 4) * L ^ A.kappa :=
      mul_le_mul_of_nonneg_left hbasele (div_nonneg hgap.le h4nonneg)
    rw [← hbaseForm] at hmul
    field_simp [hgap.ne'] at hmul
    nlinarith
  have hLpowpos : 0 < L ^ A.kappa := Real.rpow_pos_of_pos hLpos _
  have hgoal : P / L ^ A.kappa ≤ A.gap / 4 := by
    rw [div_le_div_iff₀ hLpowpos h4pos]
    nlinarith
  have hbetaForm : A.beta L = P * L ^ (-A.kappa) := by
    simp [TwoWellConstants.beta, P]
  calc
    A.beta L = P * L ^ (-A.kappa) := hbetaForm
    _ = P / L ^ A.kappa := by
      rw [Real.rpow_neg hLpos.le]
      ring
    _ ≤ A.gap / 4 := hgoal

/-- The remainder in equations `eq:lambda1` and `eq:lambda2`. -/
noncomputable def remainder (A : TwoWellConstants) (L : ℝ) : ℝ :=
  A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) + 2 * A.beta L ^ 2 / A.gap

/-- The conclusion of Theorem 3.3, with `lambda` naming the first three
eigenvalues of the two-well operator in increasing order. -/
def twoWellConclusion (A : TwoWellConstants) (lambda : ℕ → ℝ) (L : ℝ) : Prop :=
  abs (lambda 0 - (A.mu1 - A.c * A.phiMass ^ 2 * L ^ (-A.kappa))) ≤ A.remainder L ∧
  abs (lambda 1 - (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))) ≤ A.remainder L ∧
  A.mu1 + 3 * A.gap / 4 ≤ lambda 2 ∧
  A.gap / 2 ≤ lambda 2 - lambda 1

/-- The limiting gap assertion in equation `eq:gap-limit`. -/
def gapLimit (A : TwoWellConstants) (lambda : ℝ → ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun L : ℝ => L ^ A.kappa * (lambda L 1 - lambda L 0))
    Filter.atTop (nhds (2 * A.c * A.phiMass ^ 2))

/-- Full two-well conclusion, including the threshold and the limiting gap. -/
def twoWellStatement (A : TwoWellConstants) (lambda : ℝ → ℕ → ℝ) : Prop :=
  (∀ L, A.L0 ≤ L → A.twoWellConclusion (lambda L) L) ∧ A.gapLimit lambda

end TwoWellConstants

end Tunneling
