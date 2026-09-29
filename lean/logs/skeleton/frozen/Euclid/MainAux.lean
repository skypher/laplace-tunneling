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
  sorry

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
  sorry

/-- Ordered eigenvalues of a real symmetric `2 × 2` matrix with zero
diagonal. -/
theorem eigenvalues₀_fin_two_of_zero_diag (T : Matrix (Fin 2) (Fin 2) ℝ)
    (hT : T.IsHermitian) (h00 : T 0 0 = 0) (h11 : T 1 1 = 0) :
    hT.eigenvalues₀ (Fin.rev 0) = -|T 0 1| ∧ hT.eigenvalues₀ (Fin.rev 1) = |T 0 1| := by
  sorry

/-- The strict second inequality in `eq:L0-conditions`:
`2 c m₁² (L + 2R)^{-κ} > 4 β_L² / g` for `L ≥ L₀`. -/
theorem L0_simplicity_condition (A : TwoWellConstants) (L : ℝ) (hL : A.L0 ≤ L) :
    4 * A.beta L ^ 2 / A.gap < 2 * A.c * A.phiMass ^ 2 * (L + 2 * A.R) ^ (-A.kappa) := by
  sorry

end TwoWellAux

end Tunneling
