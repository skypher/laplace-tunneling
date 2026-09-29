import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Courant--Fischer levels of a quadratic form

For a real inner product space `V` (not necessarily complete) and a quadratic
map `Q` on `V`, the level of index `k` (counted from `0`) is

  `level Q k = inf { sup { Q u : u ∈ W, ‖u‖ = 1 } : W ≤ V, dim W = k + 1 }`.

For the closed form of a self-adjoint operator with compact resolvent, whose
form domain is `V`, these are the eigenvalues repeated according to
multiplicity (paper, Section 2).  This file only records the two elementary
halves of the min--max principle used in the paper: test-subspace upper bounds
and orthogonality lower bounds.
-/

namespace Tunneling
namespace MinMax

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Rayleigh supremum of `Q` over the unit sphere of the subspace `W`. -/
noncomputable def rayleighSup (Q : QuadraticMap ℝ V ℝ) (W : Submodule ℝ V) : ℝ :=
  ⨆ u : {u : W // ‖(u : V)‖ = 1}, Q (u : V)

/-- The Courant--Fischer level of index `k` (the `(k+1)`-st eigenvalue). -/
noncomputable def level (Q : QuadraticMap ℝ V ℝ) (k : ℕ) : ℝ :=
  ⨅ W : {W : Submodule ℝ V // Module.finrank ℝ W = k + 1}, rayleighSup Q W

private theorem norm_inv_smul_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [norm_smul]
  simp [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
  field_simp

private theorem exists_unit_of_pos_finrank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : 0 < Module.finrank ℝ E) : ∃ x : E, ‖x‖ = 1 := by
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hE
  exact ⟨‖x‖⁻¹ • x, norm_inv_smul_eq_one x hx⟩

private theorem quadraticMap_invNorm_smul (Q : QuadraticMap ℝ V ℝ) (u : V) :
    Q (‖u‖⁻¹ • u) = (‖u‖⁻¹) ^ 2 * Q u := by
  rw [Q.map_smul]
  simp only [smul_eq_mul, pow_two]

private theorem quadratic_le_mul_norm_sq_of_unit_bound (Q : QuadraticMap ℝ V ℝ)
    (u : V) (hu : u ≠ 0) (a : ℝ)
    (h : Q (‖u‖⁻¹ • u) ≤ a) : Q u ≤ a * ‖u‖ ^ 2 := by
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hcancel : (‖u‖⁻¹) ^ 2 * Q u * ‖u‖ ^ 2 = Q u := by
    field_simp
  calc
    Q u = (‖u‖⁻¹) ^ 2 * Q u * ‖u‖ ^ 2 := hcancel.symm
    _ = Q (‖u‖⁻¹ • u) * ‖u‖ ^ 2 := by rw [quadraticMap_invNorm_smul]
    _ ≤ a * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg ‖u‖)

private theorem exists_submodule_le_of_finrank_le (U : Submodule ℝ V) {n m : ℕ}
    (hmn : m ≤ n) (hdim : Module.finrank ℝ U = n) :
    ∃ S : Submodule ℝ V, S ≤ U ∧ Module.finrank ℝ S = m := by
  by_cases hm0 : m = 0
  · subst m
    exact ⟨⊥, bot_le, by simp⟩
  · have hnpos : 0 < n := by omega
    letI : FiniteDimensional ℝ U := .of_finrank_pos (hnpos.trans_eq hdim.symm)
    let b := Module.finBasisOfFinrankEq ℝ U hdim
    let v : Fin m → V := fun i => ((b (Fin.castLE hmn i) : U) : V)
    have hli : LinearIndependent ℝ v := by
      dsimp [v]
      exact (b.linearIndependent.comp (Fin.castLE hmn) (Fin.castLE_injective hmn)).map'
        U.subtype (Submodule.ker_subtype U)
    let S : Submodule ℝ V := Submodule.span ℝ (Set.range v)
    refine ⟨S, ?_, ?_⟩
    · exact Submodule.span_le.2 (by
        rintro x ⟨i, rfl⟩
        exact (b (Fin.castLE hmn i)).property)
    · change Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = m
      rw [finrank_span_eq_card hli]
      simp

private theorem exists_orthogonal_unit_vector (k : ℕ) (e : Fin k → V)
    (U : Submodule ℝ V) (hdim : Module.finrank ℝ U = k + 1) :
    ∃ u : U, ‖(u : V)‖ = 1 ∧ ∀ i, inner ℝ (e i) (u : V) = 0 := by
  have hdimpos : 0 < Module.finrank ℝ U := by
    rw [hdim]
    exact Nat.zero_lt_succ k
  letI : FiniteDimensional ℝ U := .of_finrank_pos hdimpos
  let f : U →ₗ[ℝ] (Fin k → ℝ) :=
    { toFun := fun u i => inner ℝ (e i) (u : V)
      map_add' := by
        intro x y
        funext i
        simp [inner_add_right]
      map_smul' := by
        intro a x
        funext i
        simp [real_inner_smul_right] }
  have hlt : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ U := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hdim]
    omega
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨x, hxker, hxne⟩ := (Submodule.ne_bot_iff (LinearMap.ker f)).mp hker
  let u : U := ‖x‖⁻¹ • x
  have hunorm : ‖(u : V)‖ = 1 := by
    dsimp [u]
    simpa using norm_inv_smul_eq_one x hxne
  have hfzero : f u = 0 := by
    dsimp [u]
    rw [f.map_smul, LinearMap.mem_ker.mp hxker, smul_zero]
  refine ⟨u, hunorm, ?_⟩
  intro i
  have hi := congrFun hfzero i
  simpa [f] using hi

theorem bddAbove_unitSphere (Q : QuadraticMap ℝ V ℝ) (W : Submodule ℝ V)
    [FiniteDimensional ℝ W] :
    BddAbove (Set.range fun u : {u : W // ‖(u : V)‖ = 1} => Q (u : V)) := by
  let qW : QuadraticMap ℝ W ℝ := Q.comp W.subtype
  letI : IsModuleTopology ℝ W := isModuleTopologyOfFiniteDimensional
  have hbil : Continuous (fun z : W × W => qW.polarBilin z.1 z.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left qW.polarBilin
  have hdiag : Continuous (fun u : W => qW.polarBilin u u) :=
    hbil.comp (continuous_id.prodMk continuous_id)
  have hq : ∀ u : W, qW.polarBilin u u = 2 * Q (u : V) := by
    intro u
    have hh : (qW.polarBilin).toQuadraticMap u = (2 • qW) u :=
      congrArg (fun q : QuadraticMap ℝ W ℝ => q u) qW.toQuadraticMap_polarBilin
    calc
      qW.polarBilin u u = (qW.polarBilin).toQuadraticMap u := rfl
      _ = (2 • qW) u := hh
      _ = 2 * Q (u : V) := by simp [smul_eq_mul, qW]
  have hcont : Continuous (fun u : W => Q (u : V)) := by
    have heq : (fun u : W => Q (u : V)) =
        fun u => (2 : ℝ)⁻¹ * qW.polarBilin u u := by
      funext u
      rw [hq]
      field_simp
    rw [heq]
    exact continuous_const.mul hdiag
  letI : ProperSpace W := FiniteDimensional.proper ℝ W
  have hsphere : IsCompact (Metric.sphere (0 : W) 1) := isCompact_sphere _ _
  have himage : Set.range (fun u : {u : W // ‖(u : V)‖ = 1} => Q (u : V)) ⊆
      (fun u : W => Q (u : V)) '' Metric.sphere (0 : W) 1 := by
    rintro y ⟨u, rfl⟩
    refine ⟨u, ?_, rfl⟩
    simpa [Metric.mem_sphere, dist_zero_right] using u.property
  exact (hsphere.bddAbove_image hcont.continuousOn).mono himage

theorem rayleighSup_le (Q : QuadraticMap ℝ V ℝ) (W : Submodule ℝ V)
    (hW : 0 < Module.finrank ℝ W) (a : ℝ)
    (h : ∀ u ∈ W, Q u ≤ a * ‖u‖ ^ 2) :
    rayleighSup Q W ≤ a := by
  letI : FiniteDimensional ℝ W := .of_finrank_pos hW
  haveI : Nonempty {u : W // ‖(u : V)‖ = 1} := by
    obtain ⟨u, hu⟩ := exists_unit_of_pos_finrank hW
    exact ⟨⟨u, by simpa using hu⟩⟩
  unfold rayleighSup
  apply ciSup_le
  intro u
  have hq := h (u : V) u.1.property
  rw [u.2] at hq
  simpa using hq

theorem le_rayleighSup (Q : QuadraticMap ℝ V ℝ) (W : Submodule ℝ V)
    [FiniteDimensional ℝ W] (u : V) (hu : u ∈ W) (hnorm : ‖u‖ = 1) :
    Q u ≤ rayleighSup Q W := by
  exact le_ciSup (bddAbove_unitSphere Q W) ⟨⟨u, hu⟩, hnorm⟩

private theorem rayleighFamily_bddBelow (Q : QuadraticMap ℝ V ℝ) (k : ℕ)
    (hbdd : ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v) :
    BddBelow (Set.range fun W : {W : Submodule ℝ V // Module.finrank ℝ W = k + 1} =>
      rayleighSup Q W) := by
  obtain ⟨m, hm⟩ := hbdd
  refine ⟨m, ?_⟩
  rintro x ⟨W, rfl⟩
  have hdimpos : 0 < Module.finrank ℝ W := by
    rw [W.property]
    exact Nat.zero_lt_succ k
  letI : FiniteDimensional ℝ W := .of_finrank_pos hdimpos
  obtain ⟨u, hu⟩ := exists_unit_of_pos_finrank hdimpos
  have huV : ‖(u : V)‖ = 1 := by simpa using hu
  have hq := hm (u : V)
  rw [huV] at hq
  simp only [one_pow, mul_one] at hq
  have hsup : Q (u : V) ≤ rayleighSup Q W :=
    le_rayleighSup Q W (u : V) u.property huV
  exact hq.trans hsup

private theorem rayleighSup_mono (Q : QuadraticMap ℝ V ℝ)
    (S U : Submodule ℝ V) (hSU : S ≤ U)
    (hSdim : 0 < Module.finrank ℝ S) (hUdim : 0 < Module.finrank ℝ U) :
    rayleighSup Q S ≤ rayleighSup Q U := by
  letI : FiniteDimensional ℝ S := .of_finrank_pos hSdim
  letI : FiniteDimensional ℝ U := .of_finrank_pos hUdim
  haveI : Nonempty {u : S // ‖(u : V)‖ = 1} := by
    obtain ⟨u, hu⟩ := exists_unit_of_pos_finrank hSdim
    exact ⟨⟨u, by simpa using hu⟩⟩
  unfold rayleighSup
  apply ciSup_le
  intro u
  have huU : (u : V) ∈ U := hSU u.1.property
  exact le_rayleighSup Q U (u : V) huU u.2

theorem level_le (Q : QuadraticMap ℝ V ℝ) (k : ℕ)
    (hbdd : ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v)
    (W : Submodule ℝ V) (hW : Module.finrank ℝ W = k + 1) (a : ℝ)
    (h : ∀ u ∈ W, Q u ≤ a * ‖u‖ ^ 2) :
    level Q k ≤ a := by
  have hdimpos : 0 < Module.finrank ℝ W := by rw [hW]; exact Nat.zero_lt_succ k
  calc
    level Q k ≤ rayleighSup Q W := by
      unfold level
      exact ciInf_le (rayleighFamily_bddBelow Q k hbdd) ⟨W, hW⟩
    _ ≤ a := rayleighSup_le Q W hdimpos a h

theorem le_level (Q : QuadraticMap ℝ V ℝ) (k : ℕ) (e : Fin k → V) (a : ℝ)
    (h : ∀ v : V, (∀ i, inner ℝ (e i) v = 0) → a * ‖v‖ ^ 2 ≤ Q v)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = k + 1) :
    a ≤ level Q k := by
  letI : Nonempty {W : Submodule ℝ V // Module.finrank ℝ W = k + 1} := by
    obtain ⟨W, hW⟩ := hdim
    exact ⟨⟨W, hW⟩⟩
  have hall : ∀ W : {W : Submodule ℝ V // Module.finrank ℝ W = k + 1},
      a ≤ rayleighSup Q W := by
    intro W
    have hdimpos : 0 < Module.finrank ℝ W.1 := by
      rw [W.property]
      exact Nat.zero_lt_succ k
    letI : FiniteDimensional ℝ W.1 := .of_finrank_pos hdimpos
    obtain ⟨u, hu, horth⟩ := exists_orthogonal_unit_vector k e W.1 W.property
    have hq := h (u : V) horth
    rw [hu] at hq
    have hq' : a ≤ Q (u : V) := by simpa using hq
    exact hq'.trans (le_rayleighSup Q W.1 (u : V) u.property hu)
  have hbelow : BddBelow (Set.range fun W : {W : Submodule ℝ V //
      Module.finrank ℝ W = k + 1} => rayleighSup Q W) := ⟨a, by
        rintro x ⟨W, rfl⟩
        exact hall W⟩
  have hle := (le_ciInf_iff hbelow).2 hall
  simpa [level] using hle

theorem level_zero_le (Q : QuadraticMap ℝ V ℝ)
    (hbdd : ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v)
    (u : V) (hu : ‖u‖ = 1) :
    level Q 0 ≤ Q u := by
  have hu0 : u ≠ 0 := by
    intro hzero
    simp [hzero] at hu
  let W : Submodule ℝ V := Submodule.span ℝ ({u} : Set V)
  have hW : Module.finrank ℝ W = 0 + 1 := by
    simpa [W] using (finrank_span_singleton hu0)
  apply level_le Q 0 hbdd W hW (Q u)
  intro v hv
  obtain ⟨c, rfl⟩ : ∃ c : ℝ, c • u = v := by
    simpa [W, Submodule.mem_span_singleton] using hv
  simp [QuadraticMap.map_smul, norm_smul, hu, Real.norm_eq_abs, sq_abs,
    mul_comm, mul_left_comm, mul_assoc]
  apply le_of_eq
  ring

theorem level_zero_mul_le (Q : QuadraticMap ℝ V ℝ)
    (hbdd : ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v) (v : V) :
    level Q 0 * ‖v‖ ^ 2 ≤ Q v := by
  by_cases hv : v = 0
  · simp [hv, Q.map_zero]
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hcancel : (‖v‖⁻¹) ^ 2 * Q v * ‖v‖ ^ 2 = Q v := by field_simp
    have hunit : level Q 0 ≤ Q (‖v‖⁻¹ • v) :=
      level_zero_le Q hbdd (‖v‖⁻¹ • v) (norm_inv_smul_eq_one v hv)
    calc
      level Q 0 * ‖v‖ ^ 2 ≤ Q (‖v‖⁻¹ • v) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hunit (sq_nonneg ‖v‖)
      _ = Q v := by rw [quadraticMap_invNorm_smul]; exact hcancel

theorem exists_subspace_of_level_lt (Q : QuadraticMap ℝ V ℝ) (k : ℕ)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = k + 1) (a : ℝ)
    (h : level Q k < a) :
    ∃ W : Submodule ℝ V, Module.finrank ℝ W = k + 1 ∧
      ∀ u ∈ W, Q u ≤ a * ‖u‖ ^ 2 := by
  let I := {W : Submodule ℝ V // Module.finrank ℝ W = k + 1}
  letI : Nonempty I := by
    obtain ⟨W, hW⟩ := hdim
    exact ⟨⟨W, hW⟩⟩
  have hlevel : (⨅ W : I, rayleighSup Q W) < a := by simpa [level, I] using h
  obtain ⟨W, hWlt⟩ := exists_lt_of_ciInf_lt hlevel
  have hdimpos : 0 < Module.finrank ℝ W := by rw [W.property]; exact Nat.zero_lt_succ k
  letI : FiniteDimensional ℝ W := .of_finrank_pos hdimpos
  refine ⟨W, W.property, ?_⟩
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    simp [Q.map_zero]
  · have hunit : ‖‖u‖⁻¹ • u‖ = 1 := norm_inv_smul_eq_one u hu0
    have hq : Q (‖u‖⁻¹ • u) ≤ rayleighSup Q W :=
      le_rayleighSup Q W (‖u‖⁻¹ • u) (Submodule.smul_mem _ _ hu) hunit
    have hq' : Q (‖u‖⁻¹ • u) ≤ a := hq.trans hWlt.le
    exact quadratic_le_mul_norm_sq_of_unit_bound Q u hu0 a hq'

theorem level_mono (Q : QuadraticMap ℝ V ℝ) (k : ℕ)
    (hbdd : ∃ m : ℝ, ∀ v : V, m * ‖v‖ ^ 2 ≤ Q v)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = k + 2) :
    level Q k ≤ level Q (k + 1) := by
  obtain ⟨W0, hW0⟩ := hdim
  have hW0' : Module.finrank ℝ W0 = (k + 1) + 1 := by omega
  letI : Nonempty {W : Submodule ℝ V // Module.finrank ℝ W = (k + 1) + 1} :=
    ⟨⟨W0, hW0'⟩⟩
  have hbddOuter := rayleighFamily_bddBelow Q (k + 1) hbdd
  have hall : ∀ U : {U : Submodule ℝ V // Module.finrank ℝ U = (k + 1) + 1},
      level Q k ≤ rayleighSup Q U := by
    intro U
    have hdimU : Module.finrank ℝ U.1 = k + 2 := by omega
    obtain ⟨S, hSU, hSdim⟩ :=
      exists_submodule_le_of_finrank_le U.1 (n := k + 2) (m := k + 1) (by omega) hdimU
    have hSpos : 0 < Module.finrank ℝ S := by rw [hSdim]; omega
    have hUpos : 0 < Module.finrank ℝ U.1 := by rw [hdimU]; omega
    have hinner : level Q k ≤ rayleighSup Q S := by
      unfold level
      exact ciInf_le (rayleighFamily_bddBelow Q k hbdd) ⟨S, hSdim⟩
    exact hinner.trans (rayleighSup_mono Q S U.1 hSU hSpos hUpos)
  have hle : level Q k ≤ ⨅ U : {U : Submodule ℝ V //
      Module.finrank ℝ U = (k + 1) + 1}, rayleighSup Q U :=
    (le_ciInf_iff hbddOuter).2 hall
  simpa [level] using hle

theorem exists_finrank_of_le {n m : ℕ} (hmn : m ≤ n)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = n) :
    ∃ W : Submodule ℝ V, Module.finrank ℝ W = m := by
  obtain ⟨U, hU⟩ := hdim
  obtain ⟨S, hSU, hSdim⟩ := exists_submodule_le_of_finrank_le U hmn hU
  exact ⟨S, hSdim⟩

end MinMax
end Tunneling
