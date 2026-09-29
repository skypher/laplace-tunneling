import Tunneling.Euclid.Translate
import Tunneling.MultiWell

/-!
# Exact multi-well reduction (paper Lemma 4.1)

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
def multiWellDomain (D : Set (Eucl d)) (a : ι → Eucl d) (L : ℝ) : Set (Eucl d) :=
  {x | ∃ j, x - L • a j ∈ D}

/-- Geometric data of paper Lemma 4.1: a measurable `D ⊆ B_R(0)` and
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

/-- The `j`-th piece `u_j = 1_D · τ_{-L a_j} ψ`, i.e. `u_j(x) = ψ(x + L a_j)`
for `x ∈ D`. -/
noncomputable def pieceL2 (j : ι) : L2 d →ₗ[ℝ] L2 d :=
  (indicatorL2 G.D G.hDm).comp (translateL2 (-(G.L • G.a j))).toLinearMap

/-- The pieces of a finite-energy function on `Ω` have finite energy on `D`
(the cross-well kernel is bounded by positive separation). -/
theorem pieceL2_mem (j : ι) (ψ : formDomain G.κ G.Ω) :
    G.pieceL2 j (ψ : L2 d) ∈ formDomain G.κ G.D := by
  sorry

/-- The restriction map `ψ ↦ u_j`. -/
noncomputable def wellMap (j : ι) : formDomain G.κ G.Ω →ₗ[ℝ] formDomain G.κ G.D where
  toFun ψ := ⟨G.pieceL2 j (ψ : L2 d), G.pieceL2_mem j ψ⟩
  map_add' ψ χ := Subtype.ext (by simp)
  map_smul' t ψ := Subtype.ext (by simp)

@[simp] theorem wellMap_coe (j : ι) (ψ : formDomain G.κ G.Ω) :
    ((G.wellMap j ψ : formDomain G.κ G.D) : L2 d) = G.pieceL2 j (ψ : L2 d) :=
  rfl

/-- The identification `L²(Ω) ≅ ⊕_j L²(D)` is unitary. -/
theorem inner_eq_sum (ψ χ : formDomain G.κ G.Ω) :
    inner ℝ (ψ : L2 d) (χ : L2 d) =
      ∑ j, inner ℝ (G.pieceL2 j (ψ : L2 d)) (G.pieceL2 j (χ : L2 d)) := by
  sorry

theorem translate_mem_Ω (φ : formDomain G.κ G.D) (j : ι) :
    translateL2 (G.L • G.a j) (φ : L2 d) ∈ formDomain G.κ G.Ω := by
  sorry

/-- The translated ground-state vectors `Φ_j = τ_{L a_j} φ`. -/
noncomputable def Φ (φ : formDomain G.κ G.D) (j : ι) : formDomain G.κ G.Ω :=
  ⟨translateL2 (G.L • G.a j) (φ : L2 d), G.translate_mem_Ω φ j⟩

theorem pieceL2_Φ (φ : formDomain G.κ G.D) (i j : ι) :
    G.pieceL2 i ((G.Φ φ j : formDomain G.κ G.Ω) : L2 d) =
      if i = j then (φ : L2 d) else 0 := by
  sorry

/-- The decoupled form `Q₀[ψ] = Σ_j Q_D[u_j]`, i.e. the form of `𝒜₀`. -/
noncomputable def Q0 (c : ℝ) : QuadraticMap ℝ (formDomain G.κ G.Ω) ℝ :=
  ∑ j, (formQ c G.κ G.D).comp (G.wellMap j)

/-- The kernel pairing between wells `i` and `j`:
`∬ u(x) v(y) |L(a_i - a_j) + x - y|^{-κ} dx dy`. -/
noncomputable def crossPair (i j : ι) (u v : L2 d) : ℝ :=
  kernelCrossPairing (multiWellCrossKernel G.κ (G.L • (G.a i - G.a j)))
    (volume : Measure (Eucl d)) (u : Eucl d → ℝ) (v : Eucl d → ℝ)

/-- The scalar interaction `w(ψ, χ)` before bilinearity is recorded. -/
noncomputable def interactionFun (c : ℝ) (ψ χ : formDomain G.κ G.Ω) : ℝ :=
  -c * ∑ i, ∑ j, if i = j then (0 : ℝ) else
    G.crossPair i j (G.pieceL2 i (ψ : L2 d)) (G.pieceL2 j (χ : L2 d))

theorem interactionFun_add_left (c : ℝ) (ψ ψ' χ : formDomain G.κ G.Ω) :
    G.interactionFun c (ψ + ψ') χ = G.interactionFun c ψ χ + G.interactionFun c ψ' χ := by
  sorry

theorem interactionFun_smul_left (c : ℝ) (t : ℝ) (ψ χ : formDomain G.κ G.Ω) :
    G.interactionFun c (t • ψ) χ = t • G.interactionFun c ψ χ := by
  sorry

theorem interactionFun_add_right (c : ℝ) (ψ χ χ' : formDomain G.κ G.Ω) :
    G.interactionFun c ψ (χ + χ') = G.interactionFun c ψ χ + G.interactionFun c ψ χ' := by
  sorry

theorem interactionFun_smul_right (c : ℝ) (t : ℝ) (ψ χ : formDomain G.κ G.Ω) :
    G.interactionFun c ψ (t • χ) = t • G.interactionFun c ψ χ := by
  sorry

/-- The interaction form `w` of `𝒱_L`. -/
noncomputable def interaction (c : ℝ) : LinearMap.BilinForm ℝ (formDomain G.κ G.Ω) :=
  LinearMap.mk₂ ℝ (G.interactionFun c) (G.interactionFun_add_left c)
    (G.interactionFun_smul_left c) (G.interactionFun_add_right c)
    (G.interactionFun_smul_right c)

theorem interaction_apply (c : ℝ) (ψ χ : formDomain G.κ G.Ω) :
    G.interaction c ψ χ = G.interactionFun c ψ χ :=
  rfl

theorem isOpen_Ω (hDo : IsOpen G.D) : IsOpen G.Ω := by
  sorry

theorem Ω_nonempty [Nonempty ι] (hDne : G.D.Nonempty) : G.Ω.Nonempty := by
  sorry

end WellGeometry

end Tunneling
