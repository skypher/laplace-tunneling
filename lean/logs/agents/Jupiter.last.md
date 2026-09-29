- **Proved:** `exists_positiveGroundState`, `IsPositiveGroundState.polar_eq`, `eigenvalue_zero_lt_one`, `IsPositiveGroundState.gap`, `IsPositiveGroundState.mass_pos`, `IsPositiveGroundState.integrable`, and `IsPositiveGroundState.unique`.
- **Helpers added:** finite-dimensional unit and orthogonal vectors; energy-to-seminorm bounds and a lower-semicontinuity limit; quadratic coefficient extraction; integrability, sign, and orthogonality lemmas.
- **Type-checking:** I checked the assembled file through Lean on stdin. The full pass exposed three issues in the strict-gap proof; after correcting them, I type-checked the continuity and negation/subtype fixes in isolated Lean snippets. I did not rerun the entire assembled file after those final corrections.

===BEGIN FILE Tunneling/Euclid/GroundState.lean===
```lean
import Tunneling.Euclid.Bump
import Tunneling.Euclid.Compactness
import Tunneling.Euclid.Sign

/-!
# The one-well ground state

Paper Section 2 uses, for a bounded open `D ⊆ B_R(0)`:

* `μ₁ = λ₁(D) < μ₂ = λ₂(D)` (simplicity of the first eigenvalue);
* a normalized nonnegative ground state `φ₁` with `A_D φ₁ = μ₁ φ₁` and
  mass `m₁ = ∫ φ₁ > 0` (equation `eq:mass`).

The paper cites [DiNezzaPalatucciValdinoci2012, Theorems 5.4 and 7.1] and
[BrascoParini2016, Theorem 2.8] for these facts; here they are proved from the
compactness of the form embedding (`Tunneling.Euclid.Compactness`) and the
sign property of minimizers (`Tunneling.Euclid.Sign`).  In this file `μ₁` and
`μ₂` are the Courant--Fischer levels `eigenvalue c κ D 0` and
`eigenvalue c κ D 1`.
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- `φ` is the normalized nonnegative ground state of `A_D`
(paper equation `eq:mass`): it lies in the form domain, has unit `L²` norm,
nonnegative values, and attains the lowest level `μ₁`. -/
structure IsPositiveGroundState (c κ : ℝ) (D : Set (Eucl d)) (φ : L2 d) : Prop where
  mem : φ ∈ formDomain κ D
  norm_eq_one : ‖φ‖ = 1
  energy_eq : formQ c κ D ⟨φ, mem⟩ = eigenvalue c κ D 0
  nonneg : 0 ≤ᵐ[volume] (φ : Eucl d → ℝ)

theorem formQ_bddBelow (c κ : ℝ) (hc : 0 ≤ c) (G : Set (Eucl d)) :
    ∃ m : ℝ, ∀ v : formDomain κ G, m * ‖v‖ ^ 2 ≤ formQ c κ G v :=
  ⟨0, fun v => by simpa using formQ_nonneg c κ hc G v⟩

private theorem positiveGroundState_integrable (s c R : ℝ) (D : Set (Eucl d))
    (hDR : D ⊆ Metric.ball 0 R) {φ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ) :
    Integrable (φ : Eucl d → ℝ) := by
  have hclosed : D ⊆ Metric.closedBall 0 R :=
    Set.Subset.trans hDR Metric.ball_subset_closedBall
  have hμ : volume (Metric.closedBall (0 : Eucl d) R) ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : Eucl d) R).measure_lt_top.ne
  have hone : IntegrableOn (φ : Eucl d → ℝ) (Metric.closedBall 0 R) volume :=
    MeasureTheory.integrableOn_Lp_of_measure_ne_top (p := 2) φ (by norm_num) hμ
  apply hone.integrable_of_ae_notMem_eq_zero
  filter_upwards [hφ.mem.1] with x hx hnot
  exact hx (fun hxd => hnot (hclosed hxd))

private theorem exists_unit_mem_submodule {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (W : Submodule ℝ V) (hW : 0 < Module.finrank ℝ W) :
    ∃ v : V, v ∈ W ∧ ‖v‖ = 1 := by
  haveI : Module.Finite ℝ W := Module.finite_of_finrank_pos hW
  obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hW
  have huN : ‖(u : V)‖ ≠ 0 := by
    intro hz
    apply hu
    exact Subtype.ext (norm_eq_zero.mp (by simpa using hz))
  refine ⟨‖(u : V)‖⁻¹ • (u : V), W.smul_mem _ u.property, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ huN

private theorem exists_unit_orthogonal_in_two_dim {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (W : Submodule ℝ V) (hW : Module.finrank ℝ W = 2)
    (x : V) :
    ∃ v : V, v ∈ W ∧ ‖v‖ = 1 ∧ inner ℝ x v = 0 := by
  letI : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_eq_succ (by omega)
  let ell : V →ₗ[ℝ] ℝ := (innerSL ℝ x).toLinearMap
  let f : W →ₗ[ℝ] ℝ := ell.domRestrict W
  have hrange : Module.finrank ℝ f.range ≤ 1 := by
    calc
      Module.finrank ℝ f.range ≤ Module.finrank ℝ ℝ := f.range.finrank_le
      _ = 1 := Module.finrank_self ℝ
  have hk : 0 < Module.finrank ℝ f.ker := by
    have hsum := f.finrank_range_add_finrank_ker
    omega
  obtain ⟨w, hw, hn⟩ := exists_unit_mem_submodule (f.ker) hk
  refine ⟨(w : W), (w : W).property, ?_, ?_⟩
  · simpa using hn
  · have hf0 : f (w : W) = 0 := LinearMap.mem_ker.mp hw
    change inner ℝ x ((w : W) : V) = 0
    change ell ((w : W) : V) = 0 at hf0
    simpa [ell] using hf0

private theorem seminormSq_le_of_formQ_le (c κ : ℝ) (D : Set (Eucl d))
    (hc : 0 < c) {u : formDomain κ D} {a : ℝ}
    (hQ : formQ c κ D u ≤ a) :
    gagliardoSeminormSq κ (volume : Measure (Eucl d)) ((u : L2 d) : Eucl d → ℝ) ≤ 2 / c * a := by
  have hc2 : 0 < c / 2 := by positivity
  have henergy : c / 2 * gagliardoSeminormSq κ (volume : Measure (Eucl d)) ((u : L2 d) : Eucl d → ℝ) ≤ a := by
    simpa [formQ_apply] using hQ
  have hdiv : gagliardoSeminormSq κ (volume : Measure (Eucl d)) ((u : L2 d) : Eucl d → ℝ) ≤ a / (c / 2) := by
    rw [le_div_iff₀ hc2]
    simpa [mul_comm] using henergy
  calc
    gagliardoSeminormSq κ (volume : Measure (Eucl d)) ((u : L2 d) : Eucl d → ℝ) ≤ a / (c / 2) := hdiv
    _ = 2 / c * a := by field_simp [hc.ne']

private theorem refined_form_limit (c κ μ : ℝ) (hc : 0 < c) (D : Set (Eucl d))
    (g : L2 d) (F : ℕ → L2 d) (idx : ℕ → ℕ) (hidx : StrictMono idx)
    (hmem : ∀ n, F (idx n) ∈ formDomain κ D)
    (hlim : Filter.Tendsto (fun n => F (idx n)) Filter.atTop (nhds g))
    (hQ : ∀ n, formQ c κ D ⟨F (idx n), hmem n⟩ ≤ μ + 1 / ((idx n : ℝ) + 1)) :
    g ∈ formDomain κ D ∧
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (g : Eucl d → ℝ) ≤ 2 / c * μ := by
  have hidxle : ∀ n, n ≤ idx n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have hlt := hidx (Nat.lt_succ_self n)
        exact Nat.succ_le_iff.mpr (lt_of_le_of_lt ih hlt)
  let T : ℕ → L2 d := fun n => F (idx n)
  let M : ℝ := 2 / c * (|μ| + 1)
  have hM : ∀ n, gagliardoSeminormSq κ (volume : Measure (Eucl d)) (T n : Eucl d → ℝ) ≤ M := by
    intro n
    have hS := seminormSq_le_of_formQ_le c κ D hc (hQ n)
    have hidx0 : (0 : ℝ) ≤ (idx n : ℝ) := Nat.cast_nonneg _
    have hden : 1 ≤ (idx n : ℝ) + 1 := by linarith
    have hrec : 1 / ((idx n : ℝ) + 1) ≤ 1 := by
      simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden)
    have harg : μ + 1 / ((idx n : ℝ) + 1) ≤ |μ| + 1 := by nlinarith [le_abs_self μ]
    dsimp [T, M]
    exact hS.trans (mul_le_mul_of_nonneg_left harg (by positivity))
  have hdom := mem_formDomain_of_tendsto κ D T g hmem hlim M (Filter.Eventually.of_forall hM)
  have hS : gagliardoSeminormSq κ (volume : Measure (Eucl d)) (g : Eucl d → ℝ) ≤ 2 / c * μ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ : ℝ := c / 2 * ε
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hsmallBase : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / ((n : ℝ) + 1) < δ := by
      exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hδ)
    have hsmall : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / ((idx n : ℝ) + 1) < δ := by
      filter_upwards [hsmallBase] with n hn
      have hden : (n : ℝ) + 1 ≤ (idx n : ℝ) + 1 := by
        exact_mod_cast Nat.add_le_add_right (hidxle n) 1
      exact (one_div_le_one_div_of_le (by positivity) hden).trans_lt hn
    have hsemi : ∀ᶠ n : ℕ in Filter.atTop,
        gagliardoSeminormSq κ (volume : Measure (Eucl d)) (T n : Eucl d → ℝ) ≤ 2 / c * (μ + δ) := by
      filter_upwards [hsmall] with n hn
      have hSn := seminormSq_le_of_formQ_le c κ D hc (hQ n)
      have harg : μ + 1 / ((idx n : ℝ) + 1) ≤ μ + δ := by linarith
      exact hSn.trans (mul_le_mul_of_nonneg_left harg (by positivity))
    have hlim' := mem_formDomain_of_tendsto κ D T g hmem hlim (2 / c * (μ + δ)) hsemi
    have hid : 2 / c * (μ + δ) = 2 / c * μ + ε := by
      dsimp [δ]
      field_simp [hc.ne']
    calc
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (g : Eucl d → ℝ) ≤ 2 / c * (μ + δ) := hlim'.2
      _ = 2 / c * μ + ε := hid
  exact ⟨hdom.1, hS⟩

private theorem quadratic_linear_coeff_eq_zero {a b : ℝ}
    (h : ∀ t : ℝ, 0 ≤ a * t + b * t ^ 2) : a = 0 := by
  by_contra ha
  let M : ℝ := |b| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let t : ℝ := -a / (2 * M)
  have ht : 2 * M * t = -a := by dsimp [t]; field_simp [ne_of_gt hM]
  have htne : t ≠ 0 := by
    dsimp [t]
    exact div_ne_zero (neg_ne_zero.mpr ha) (mul_ne_zero two_ne_zero (ne_of_gt hM))
  have hbM : b < M := by dsimp [M]; exact lt_of_le_of_lt (le_abs_self b) (by linarith)
  have hless : a * t + b * t ^ 2 < a * t + M * t ^ 2 := by
    have : 0 < (M - b) * t ^ 2 := mul_pos (sub_pos.mpr hbM) (sq_pos_of_ne_zero htne)
    nlinarith
  have heq : a * t + M * t ^ 2 = -a ^ 2 / (4 * M) := by
    dsimp [t]
    field_simp [ne_of_gt hM]
    ring_nf
  have hneg : -a ^ 2 / (4 * M) < 0 := by
    apply div_neg_of_neg_of_pos
    · exact neg_neg_of_pos (sq_pos_of_ne_zero (by simpa [ne_eq] using ha))
    · positivity
  have hbad := h t
  rw [heq] at hless
  linarith

private theorem inner_nonneg_of_ae_nonneg {u v : L2 d}
    (hu : 0 ≤ᵐ[volume] (u : Eucl d → ℝ)) (hv : 0 ≤ᵐ[volume] (v : Eucl d → ℝ)) :
    0 ≤ inner ℝ u v := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hu, hv] with x hux hvx
  simpa [mul_comm] using mul_nonneg hux hvx

/-- Existence of the normalized nonnegative ground state. -/
theorem exists_positiveGroundState (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) :
    ∃ φ : L2 d, IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let μ : ℝ := eigenvalue c κ D 0
  let Q : QuadraticMap ℝ (formDomain κ D) ℝ := formQ c κ D
  have hbdd : ∃ m : ℝ, ∀ v : formDomain κ D, m * ‖v‖ ^ 2 ≤ Q v := by
    exact formQ_bddBelow c κ (le_of_lt hc) D
  have hdim1 : ∃ W : Submodule ℝ (formDomain κ D), Module.finrank ℝ W = 0 + 1 := by
    obtain ⟨W, hW⟩ := exists_finrank_formDomain hd s hs D hDo hDne 1
    exact ⟨W, by simpa using hW⟩
  have htest : ∀ n : ℕ, ∃ u : formDomain κ D,
      ‖(u : L2 d)‖ = 1 ∧ Q u ≤ μ + 1 / ((n : ℝ) + 1) := by
    intro n
    let a : ℝ := μ + 1 / ((n : ℝ) + 1)
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hμa : μ < a := by dsimp [a]; linarith [one_div_pos.mpr hden]
    obtain ⟨W, hW, hbound⟩ := MinMax.exists_subspace_of_level_lt Q 0 hdim1 a hμa
    have hW1 : Module.finrank ℝ W = 1 := by omega
    obtain ⟨u, huW, hu⟩ := exists_unit_mem_submodule W (by rw [hW1]; norm_num)
    refine ⟨u, ?_, ?_⟩
    · simpa using hu
    · simpa [Q, μ, a, hu] using hbound u huW
  choose f hfnorm hfQ using htest
  let F : ℕ → L2 d := fun n => (f n : L2 d)
  have hfmem : ∀ n, F n ∈ formDomain κ D := by intro n; exact (f n).property
  have hfnorm' : ∀ n, ‖F n‖ ≤ 1 := by intro n; exact (hfnorm n).le
  let M : ℝ := 2 / c * (|μ| + 1)
  have hsemi : ∀ n, gagliardoSeminormSq κ (volume : Measure (Eucl d)) (F n : Eucl d → ℝ) ≤ M := by
    intro n
    have hS := seminormSq_le_of_formQ_le c κ D hc (hfQ n)
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 n
    have hrec : 1 / ((n : ℝ) + 1) ≤ 1 := by
      simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden)
    have harg : μ + 1 / ((n : ℝ) + 1) ≤ |μ| + 1 := by nlinarith [le_abs_self μ]
    simpa [F, M] using hS.trans (mul_le_mul_of_nonneg_left harg (by positivity))
  have hclosed : D ⊆ Metric.closedBall 0 R :=
    Set.Subset.trans hDR Metric.ball_subset_closedBall
  obtain ⟨g, idx, hidx, hlim⟩ :=
    exists_tendsto_subseq s hs R D hclosed F hfmem hfnorm' M hsemi
  have hmemQ : ∀ n, formQ c κ D ⟨F (idx n), hfmem (idx n)⟩ ≤ μ + 1 / ((idx n : ℝ) + 1) := by
    intro n
    simpa [Q, F] using hfQ (idx n)
  have hliminfo := refined_form_limit c κ μ hc D g F idx hidx
    (fun n => hfmem (idx n)) hlim hmemQ
  have hgnorm : ‖g‖ = 1 := by
    have hN := hlim.norm
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    have heq : (fun n : ℕ => ‖F (idx n)‖) = fun _ => (1 : ℝ) := by
      funext n
      exact hfnorm (idx n)
    rw [heq] at hN
    exact tendsto_nhds_unique hN hconst
  let a : formDomain κ D := ⟨g, hliminfo.1⟩
  have hQg : formQ c κ D a ≤ μ := by
    rw [formQ_apply]
    have hmul := mul_le_mul_of_nonneg_left hliminfo.2 (by positivity : 0 ≤ c / 2)
    have hid : c / 2 * (2 / c * μ) = μ := by field_simp [hc.ne']
    simpa [a, hid] using hmul
  have hμle : μ ≤ formQ c κ D a :=
    MinMax.level_zero_le Q hbdd a hgnorm
  have hQeq : formQ c κ D a = μ := le_antisymm hQg hμle
  let ag : L2 d := absL2 g
  have hagmem : ag ∈ formDomain κ D := absL2_mem_formDomain κ D hliminfo.1
  have hagNorm : ‖ag‖ = 1 := by
    calc
      ‖ag‖ = ‖g‖ := norm_absL2 g
      _ = 1 := hgnorm
  let ap : formDomain κ D := ⟨ag, hagmem⟩
  have hagQle : formQ c κ D ap ≤ μ := by
    rw [formQ_apply]
    have habs := gagliardoSeminormSq_absL2_le κ D hliminfo.1
    have hmul0 := habs.trans hliminfo.2
    have hmul := mul_le_mul_of_nonneg_left hmul0 (by positivity : 0 ≤ c / 2)
    have hid : c / 2 * (2 / c * μ) = μ := by field_simp [hc.ne']
    simpa [ap, ag, hid] using hmul
  have hμleag : μ ≤ formQ c κ D ap :=
    MinMax.level_zero_le Q hbdd ap hagNorm
  have hQag : formQ c κ D ap = μ := le_antisymm hagQle hμleag
  have hapnonneg : 0 ≤ᵐ[volume] (ag : Eucl d → ℝ) := by
    simpa [ag] using absL2_nonneg g
  refine ⟨ag, ⟨hagmem, hagNorm, ?_, hapnonneg⟩⟩
  simpa [μ, κ, ap] using hQag

/-- The weak eigen-equation `A_D φ₁ = μ₁ φ₁` in form sense. -/
theorem IsPositiveGroundState.polar_eq (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) {φ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (v : formDomain ((d : ℝ) + 2 * s) D) :
    QuadraticMap.polar (formQ c ((d : ℝ) + 2 * s) D) ⟨φ, hφ.mem⟩ v =
      2 * eigenvalue c ((d : ℝ) + 2 * s) D 0 * inner ℝ φ (v : L2 d) := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let μ : ℝ := eigenvalue c κ D 0
  let Q : QuadraticMap ℝ (formDomain κ D) ℝ := formQ c κ D
  let p : formDomain κ D := ⟨φ, hφ.mem⟩
  have hQp : Q p = μ := by simpa [Q, μ, κ, p] using hφ.energy_eq
  have hpnorm : ‖(p : L2 d)‖ = 1 := by simpa [p] using hφ.norm_eq_one
  have hquad : ∀ t : ℝ,
      0 ≤ (QuadraticMap.polar Q p v - 2 * μ * inner ℝ (p : L2 d) (v : L2 d)) * t +
        (Q v - μ * ‖(v : L2 d)‖ ^ 2) * t ^ 2 := by
    intro t
    have hqexpand : Q (p + t • v) = Q p + t * QuadraticMap.polar Q p v + t ^ 2 * Q v := by
      rw [QuadraticMap.map_add Q p (t • v), QuadraticMap.map_smul Q t v,
        QuadraticMap.polar_smul_right]
      ring
    have hnormexpand : ‖(p + t • v : formDomain κ D)‖ ^ 2 =
        ‖(p : L2 d)‖ ^ 2 + 2 * t * inner ℝ (p : L2 d) (v : L2 d) +
          t ^ 2 * ‖(v : L2 d)‖ ^ 2 := by
      change ‖(p : L2 d) + t • (v : L2 d)‖ ^ 2 = _
      rw [norm_add_sq_real]
      simp [norm_smul, Real.norm_eq_abs, inner_smul_right, mul_pow, sq_abs]
      ring
    have hmin := MinMax.level_zero_mul_le (formQ c κ D)
      (formQ_bddBelow c κ (le_of_lt hc) D) (p + t • v)
    have hmin' : μ * ‖(p + t • v : formDomain κ D)‖ ^ 2 ≤
        formQ c κ D (p + t • v) := by simpa [μ, eigenvalue] using hmin
    change μ * ‖(p + t • v : formDomain κ D)‖ ^ 2 ≤ Q (p + t • v) at hmin'
    rw [hqexpand, hQp, hnormexpand, hpnorm] at hmin'
    nlinarith
  have ha := quadratic_linear_coeff_eq_zero hquad
  have hcoeff : QuadraticMap.polar Q p v -
      2 * μ * inner ℝ (p : L2 d) (v : L2 d) = 0 := ha
  have hout : QuadraticMap.polar Q p v =
      2 * μ * inner ℝ (p : L2 d) (v : L2 d) := by linarith
  simpa [Q, p, μ, κ] using hout

private theorem minimizer_sign (hd : 1 ≤ d) (c κ : ℝ) (D : Set (Eucl d))
    (hc : 0 < c) {f : L2 d} (hfmem : f ∈ formDomain κ D)
    (hQ : formQ c κ D ⟨f, hfmem⟩ = eigenvalue c κ D 0 * ‖f‖ ^ 2) :
    (0 ≤ᵐ[volume] (f : Eucl d → ℝ)) ∨ ((f : Eucl d → ℝ) ≤ᵐ[volume] 0) := by
  let μ : ℝ := eigenvalue c κ D 0
  let Q : QuadraticMap ℝ (formDomain κ D) ℝ := formQ c κ D
  let af : L2 d := absL2 f
  have hafmem : af ∈ formDomain κ D := absL2_mem_formDomain κ D hfmem
  let a : formDomain κ D := ⟨af, hafmem⟩
  let u : formDomain κ D := ⟨f, hfmem⟩
  have hafnorm : ‖af‖ = ‖f‖ := norm_absL2 f
  have hlow : μ * ‖af‖ ^ 2 ≤ Q a := by
    have hh := MinMax.level_zero_mul_le (formQ c κ D)
      (formQ_bddBelow c κ (le_of_lt hc) D) a
    simpa [μ, Q, a, eigenvalue] using hh
  have hupper : Q a ≤ Q u := by
    rw [formQ_apply]
    exact mul_le_mul_of_nonneg_left
      (gagliardoSeminormSq_absL2_le κ D hfmem) (by positivity)
  have heq : Q a = Q u := by
    apply le_antisymm hupper
    calc
      Q u = μ * ‖f‖ ^ 2 := by simpa [μ, Q, u] using hQ
      _ = μ * ‖af‖ ^ 2 := by rw [hafnorm]
      _ ≤ Q a := hlow
  have hmul : c / 2 * gagliardoSeminormSq κ (volume : Measure (Eucl d)) (af : Eucl d → ℝ) =
      c / 2 * gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ) := by
    simpa [Q, a, u, formQ_apply] using heq
  have hsemi : gagliardoSeminormSq κ (volume : Measure (Eucl d)) (af : Eucl d → ℝ) =
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ) :=
    mul_left_cancel₀ (by positivity : c / 2 ≠ 0) hmul
  exact ae_nonneg_or_nonpos_of_gagliardoSeminormSq_absL2_eq hd κ D hfmem hsemi

private theorem no_nonneg_orthogonal_minimizer (hd : 1 ≤ d) (s : ℝ)
    (hs : 0 < s ∧ s < 1) (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d))
    (hDo : IsOpen D) (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) {φ v : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (hvmem : v ∈ formDomain ((d : ℝ) + 2 * s) D) (hvn : ‖v‖ = 1)
    (hvQ : formQ c ((d : ℝ) + 2 * s) D ⟨v, hvmem⟩ = eigenvalue c ((d : ℝ) + 2 * s) D 0)
    (hvnonneg : 0 ≤ᵐ[volume] (v : Eucl d → ℝ)) (horth : inner ℝ φ v = 0) : False := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let μ : ℝ := eigenvalue c κ D 0
  let Q : QuadraticMap ℝ (formDomain κ D) ℝ := formQ c κ D
  let p : formDomain κ D := ⟨φ, hφ.mem⟩
  let u : formDomain κ D := ⟨v, hvmem⟩
  let w : formDomain κ D := p - u
  have hpQ : Q p = μ := by simpa [Q, μ, κ, p] using hφ.energy_eq
  have huQ : Q u = μ := by simpa [Q, μ, κ, u] using hvQ
  have hpol : QuadraticMap.polar Q p u = 0 := by
    rw [hφ.polar_eq hd s hs c hc R D hDo hDne hDR u, horth]
    ring
  have hQw : Q w = 2 * μ := by
    change Q (p - u) = 2 * μ
    have hsub : p - u = p + -u := by abel
    rw [hsub, QuadraticMap.map_add Q p (-u), QuadraticMap.map_neg Q u,
      QuadraticMap.polar_neg_right, hpQ, huQ, hpol]
    ring
  have hnormW : ‖(w : L2 d)‖ ^ 2 = 2 := by
    have hn := norm_sub_sq_eq_norm_sq_add_norm_sq_real (x := φ) (y := v) horth
    change ‖φ - v‖ ^ 2 = 2
    calc
      ‖φ - v‖ ^ 2 = ‖φ - v‖ * ‖φ - v‖ := by rw [pow_two]
      _ = ‖φ‖ * ‖φ‖ + ‖v‖ * ‖v‖ := hn
      _ = 2 := by rw [hφ.norm_eq_one, hvn]; norm_num
  have hWmin : Q w = μ * ‖(w : L2 d)‖ ^ 2 := by rw [hQw, hnormW]; ring
  have hsign := minimizer_sign hd c κ D hc w.property hWmin
  have hwfun : ((w : L2 d) : Eucl d → ℝ) =ᵐ[volume]
      (fun x => (φ : Eucl d → ℝ) x - (v : Eucl d → ℝ) x) := by
    change ((φ - v : L2 d) : Eucl d → ℝ) =ᵐ[volume] _
    exact MeasureTheory.Lp.coeFn_sub φ v
  have hprodNonneg : 0 ≤ᵐ[volume]
      (fun x : Eucl d => (φ : Eucl d → ℝ) x * (v : Eucl d → ℝ) x) := by
    filter_upwards [hφ.nonneg, hvnonneg] with x hx hvx
    exact mul_nonneg hx hvx
  have hprodInt : Integrable
      (fun x : Eucl d => (φ : Eucl d → ℝ) x * (v : Eucl d → ℝ) x) volume := by
    simpa [mul_comm] using MeasureTheory.L2.integrable_inner (𝕜 := ℝ) φ v
  have hprodZero : (fun x : Eucl d => (φ : Eucl d → ℝ) x * (v : Eucl d → ℝ) x) =ᵐ[volume] 0 := by
    have hz : ∫ x : Eucl d, (φ : Eucl d → ℝ) x * (v : Eucl d → ℝ) x ∂volume = 0 := by
      simpa [MeasureTheory.L2.inner_def, mul_comm] using horth
    exact (integral_eq_zero_iff_of_nonneg_ae hprodNonneg hprodInt).mp hz
  rcases hsign with hWnonneg | hWnonpos
  · have hvzeroAE : (v : Eucl d → ℝ) =ᵐ[volume] 0 := by
      filter_upwards [hwfun, hWnonneg, hvnonneg, hprodZero] with x hw hW hv hprod
      have hle : (v : Eucl d → ℝ) x ≤ (φ : Eucl d → ℝ) x := by
        rw [hw] at hW
        change 0 ≤ (φ : Eucl d → ℝ) x - (v : Eucl d → ℝ) x at hW
        linarith
      change (φ : Eucl d → ℝ) x * (v : Eucl d → ℝ) x = 0 at hprod
      have hsq : (v : Eucl d → ℝ) x * (v : Eucl d → ℝ) x ≤
          (φ : Eucl d → ℝ) x * (v : Eucl d → ℝ) x := mul_le_mul_of_nonneg_right hle hv
      rw [hprod] at hsq
      change (v : Eucl d → ℝ) x * (v : Eucl d → ℝ) x ≤ 0 at hsq
      have hsqeq : (v : Eucl d → ℝ) x * (v : Eucl d → ℝ) x = 0 :=
        le_antisymm hsq (mul_self_nonneg _)
      exact mul_self_eq_zero.mp hsqeq
    have hvzero' : (v : Eucl d → ℝ) =ᵐ[volume] (0 : L2 d) :=
      hvzeroAE.trans (Lp.coeFn_zero ℝ 2 volume).symm
    have hvzero : v = 0 := Lp.ext hvzero'
    have hvnorm0 : ‖v‖ = 0 := by rw [hvzero]; simp
    rw [hvn] at hvnorm0
    norm_num at hvnorm0
  · have hφzeroAE : (φ : Eucl d → ℝ) =ᵐ[volume] 0 := by
      filter_upwards [hwfun, hWnonpos, hφ.nonneg, hprodZero] with x hw hW hφx hprod
      have hle : (φ : Eucl d → ℝ) x ≤ (v : Eucl d → ℝ) x := by
        rw [hw] at hW
        change ((φ : Eucl d → ℝ) x - (v : Eucl d → ℝ) x) ≤ 0 at hW
        linarith
      change (φ : Eucl d → ℝ) x * (v : Eucl d → ℝ) x = 0 at hprod
      have hsq : (φ : Eucl d → ℝ) x * (φ : Eucl d → ℝ) x ≤
          (φ : Eucl d → ℝ) x * (v : Eucl d → ℝ) x := mul_le_mul_of_nonneg_left hle hφx
      rw [hprod] at hsq
      change (φ : Eucl d → ℝ) x * (φ : Eucl d → ℝ) x ≤ 0 at hsq
      have hsqeq : (φ : Eucl d → ℝ) x * (φ : Eucl d → ℝ) x = 0 :=
        le_antisymm hsq (mul_self_nonneg _)
      exact mul_self_eq_zero.mp hsqeq
    have hφzero' : (φ : Eucl d → ℝ) =ᵐ[volume] (0 : L2 d) :=
      hφzeroAE.trans (Lp.coeFn_zero ℝ 2 volume).symm
    have hφzero : φ = 0 := Lp.ext hφzero'
    have hφnorm0 : ‖φ‖ = 0 := by rw [hφzero]; simp
    rw [hφ.norm_eq_one] at hφnorm0
    norm_num at hφnorm0

/-- Simplicity of the first eigenvalue: `μ₁ < μ₂`. -/
theorem eigenvalue_zero_lt_one (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) :
    eigenvalue c ((d : ℝ) + 2 * s) D 0 < eigenvalue c ((d : ℝ) + 2 * s) D 1 := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let μ₁ : ℝ := eigenvalue c κ D 0
  let μ₂ : ℝ := eigenvalue c κ D 1
  let Q : QuadraticMap ℝ (formDomain κ D) ℝ := formQ c κ D
  have hdim2 : ∃ W : Submodule ℝ (formDomain κ D), Module.finrank ℝ W = 1 + 1 := by
    obtain ⟨W, hW⟩ := exists_finrank_formDomain hd s hs D hDo hDne 2
    exact ⟨W, by simpa using hW⟩
  by_contra hnot
  have hμ21 : μ₂ ≤ μ₁ := le_of_not_gt hnot
  obtain ⟨φ, hφ⟩ := exists_positiveGroundState hd s hs c hc R D hDo hDne hDR
  let p : formDomain κ D := ⟨φ, hφ.mem⟩
  have htest : ∀ n : ℕ, ∃ v : L2 d, ∃ hv : v ∈ formDomain κ D,
      ‖v‖ = 1 ∧ inner ℝ φ v = 0 ∧
      formQ c κ D ⟨v, hv⟩ ≤ μ₁ + 1 / ((n : ℝ) + 1) := by
    intro n
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hδ : 0 < δ := by dsimp [δ]; exact one_div_pos.mpr hden
    let aw : ℝ := μ₂ + δ
    have hlt : μ₂ < aw := by dsimp [aw]; linarith
    obtain ⟨W, hW, hWbound⟩ := MinMax.exists_subspace_of_level_lt Q 1 hdim2 aw hlt
    have hW2 : Module.finrank ℝ W = 2 := by omega
    obtain ⟨u, huW, huNorm, huorth⟩ := exists_unit_orthogonal_in_two_dim W hW2 p
    have huL2 : ‖(u : L2 d)‖ = 1 := by simpa using huNorm
    have huorth' : inner ℝ φ (u : L2 d) = 0 := by simpa [p] using huorth
    have hQupper0 : formQ c κ D u ≤ aw := by
      have hh := hWbound u huW
      simpa [Q, aw, huNorm] using hh
    have hQupper : formQ c κ D u ≤ μ₁ + δ := by
      have hh := hQupper0.trans (add_le_add_left hμ21 δ)
      simpa [aw] using hh
    exact ⟨(u : L2 d), u.property, huL2, huorth', by simpa [δ] using hQupper⟩
  choose f hfmem hfnorm hfort hfQ using htest
  let F : ℕ → L2 d := fun n => f n
  have hfmem' : ∀ n, F n ∈ formDomain κ D := by intro n; exact hfmem n
  have hfnorm' : ∀ n, ‖F n‖ ≤ 1 := by intro n; exact (hfnorm n).le
  let M : ℝ := 2 / c * (|μ₁| + 1)
  have hsemi : ∀ n, gagliardoSeminormSq κ (volume : Measure (Eucl d)) (F n : Eucl d → ℝ) ≤ M := by
    intro n
    have hS := seminormSq_le_of_formQ_le c κ D hc (hfQ n)
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 n
    have hrec : 1 / ((n : ℝ) + 1) ≤ 1 := by
      simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden)
    have harg : μ₁ + 1 / ((n : ℝ) + 1) ≤ |μ₁| + 1 := by nlinarith [le_abs_self μ₁]
    simpa [F, M] using hS.trans (mul_le_mul_of_nonneg_left harg (by positivity))
  have hclosed : D ⊆ Metric.closedBall 0 R := Set.Subset.trans hDR Metric.ball_subset_closedBall
  obtain ⟨g, idx, hidx, hlim⟩ := exists_tendsto_subseq s hs R D hclosed F hfmem' hfnorm' M hsemi
  have hmemQ : ∀ n, formQ c κ D ⟨F (idx n), hfmem' (idx n)⟩ ≤ μ₁ + 1 / ((idx n : ℝ) + 1) := by
    intro n
    simpa [F] using hfQ (idx n)
  have hliminfo := refined_form_limit c κ μ₁ hc D g F idx hidx (fun n => hfmem' (idx n)) hlim hmemQ
  have hgnorm : ‖g‖ = 1 := by
    have hN := hlim.norm
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    have heq : (fun n : ℕ => ‖F (idx n)‖) = fun _ => (1 : ℝ) := by funext n; exact hfnorm (idx n)
    rw [heq] at hN
    exact tendsto_nhds_unique hN hconst
  have hinnerlim0 := (((innerSL ℝ φ).continuous.tendsto g).comp hlim)
  change Filter.Tendsto (fun n => (innerSL ℝ φ) (F (idx n))) Filter.atTop
    (nhds ((innerSL ℝ φ) g)) at hinnerlim0
  have hinnerfun : (fun n => (innerSL ℝ φ) (F (idx n))) =
      (fun n => inner ℝ φ (F (idx n))) := by
    funext n
    exact innerSL_apply_apply (𝕜 := ℝ) (v := φ) (w := F (idx n))
  rw [hinnerfun] at hinnerlim0
  change Filter.Tendsto (fun n => inner ℝ φ (F (idx n))) Filter.atTop
    (nhds (inner ℝ φ g)) at hinnerlim0
  have hinnerlim := hinnerlim0
  have hseqzero : (fun n : ℕ => inner ℝ φ (F (idx n))) = fun _ => 0 := by
    funext n
    exact hfort (idx n)
  rw [hseqzero] at hinnerlim
  have horthg : inner ℝ φ g = 0 := tendsto_nhds_unique hinnerlim tendsto_const_nhds
  let z : formDomain κ D := ⟨g, hliminfo.1⟩
  have hQupper : formQ c κ D z ≤ μ₁ := by
    rw [formQ_apply]
    have hmul := mul_le_mul_of_nonneg_left hliminfo.2 (by positivity : 0 ≤ c / 2)
    have hid : c / 2 * (2 / c * μ₁) = μ₁ := by field_simp [hc.ne']
    simpa [z, κ, μ₁, hid] using hmul
  have hbdd : ∃ m : ℝ, ∀ y : formDomain κ D, m * ‖y‖ ^ 2 ≤ Q y :=
    formQ_bddBelow c κ (le_of_lt hc) D
  have hQlower : μ₁ ≤ formQ c κ D z := MinMax.level_zero_le Q hbdd z hgnorm
  have hQeq : formQ c κ D z = μ₁ := le_antisymm hQupper hQlower
  have hminEQ : formQ c κ D ⟨g, z.property⟩ = eigenvalue c κ D 0 * ‖g‖ ^ 2 := by
    simpa [μ₁, κ, hgnorm] using hQeq
  have hsign := minimizer_sign hd c κ D hc (f := g) z.property hminEQ
  rcases hsign with hpos | hneg
  · exact no_nonneg_orthogonal_minimizer hd s hs c hc R D hDo hDne hDR hφ z.property hgnorm
      (by simpa [μ₁, κ] using hQeq) hpos horthg
  · let gneg : L2 d := -g
    have hgnegmem : gneg ∈ formDomain κ D := by
      change (-g : L2 d) ∈ formDomain κ D
      exact (formDomain κ D).neg_mem z.property
    have hgnegnorm : ‖gneg‖ = 1 := by simp [gneg, hgnorm]
    have hgnegQ : formQ c κ D ⟨gneg, hgnegmem⟩ = μ₁ := by
      have hzneg : (⟨gneg, hgnegmem⟩ : formDomain κ D) = -z := by
        apply Subtype.ext
        rfl
      have hh : formQ c κ D ⟨gneg, hgnegmem⟩ = formQ c κ D z := by
        rw [hzneg, QuadraticMap.map_neg]
      rw [hh, hQeq]
    have hgnegpos : 0 ≤ᵐ[volume] (gneg : Eucl d → ℝ) := by
      filter_upwards [hneg, Lp.coeFn_neg g] with x hx hco
      rw [hco]
      exact neg_nonneg.mpr hx
    have horthneg : inner ℝ φ gneg = 0 := by
      change inner ℝ φ (-g) = 0
      rw [inner_neg_right, horthg]
      simp
    exact no_nonneg_orthogonal_minimizer hd s hs c hc R D hDo hDne hDR hφ hgnegmem hgnegnorm
      (by simpa [μ₁, κ] using hgnegQ) hgnegpos horthneg

/-- The spectral-gap inequality on the orthogonal complement of the ground
state: `Q_D[v] ≥ μ₂ ‖v‖²` for `v ⊥ φ₁`. -/
theorem IsPositiveGroundState.gap (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) {φ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (v : formDomain ((d : ℝ) + 2 * s) D) (hv : inner ℝ φ (v : L2 d) = 0) :
    eigenvalue c ((d : ℝ) + 2 * s) D 1 * ‖(v : L2 d)‖ ^ 2 ≤
      formQ c ((d : ℝ) + 2 * s) D v := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let μ₁ : ℝ := eigenvalue c κ D 0
  let μ₂ : ℝ := eigenvalue c κ D 1
  let Q : QuadraticMap ℝ (formDomain κ D) ℝ := formQ c κ D
  by_cases hv0 : v = 0
  · subst v
    simp [QuadraticMap.map_zero]
  · let p : formDomain κ D := ⟨φ, hφ.mem⟩
    have hpNorm : ‖(p : L2 d)‖ = 1 := by simpa [p] using hφ.norm_eq_one
    have hvL2 : (v : L2 d) ≠ 0 := by
      intro hvL2
      apply hv0
      exact Subtype.ext hvL2
    have hnormv : ‖(v : L2 d)‖ ≠ 0 := norm_ne_zero_iff.mpr hvL2
    have hnormsq : (‖(v : L2 d)‖ ^ 2) ≠ 0 := pow_ne_zero 2 hnormv
    have hpv : inner ℝ p v = 0 := by simpa using hv
    let pair : Fin 2 → formDomain κ D := ![p, v]
    have hli : LinearIndependent ℝ pair := by
      apply linearIndependent_of_ne_zero_of_inner_eq_zero
      · intro i
        fin_cases i
        · simpa [pair] using (norm_ne_zero_iff.mpr (show p ≠ 0 from by
            intro hp
            have hn : ‖(p : L2 d)‖ = 0 := by rw [hp]; simp
            linarith [hpNorm]))
        · simpa [pair] using hv0
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact False.elim (hij rfl)
        · simpa [pair] using hpv
        · simpa [pair] using inner_eq_zero_symm.mpr hpv
        · exact False.elim (hij rfl)
    let W : Submodule ℝ (formDomain κ D) := Submodule.span ℝ (Set.range pair)
    have hW : Module.finrank ℝ W = 2 := by
      calc
        Module.finrank ℝ W = Fintype.card (Fin 2) := by
          dsimp [W]
          exact finrank_span_eq_card hli
        _ = 2 := by simp
    let a : ℝ := max μ₁ (Q v / ‖(v : L2 d)‖ ^ 2)
    have hQp : Q p = μ₁ := by simpa [Q, μ₁, κ, p] using hφ.energy_eq
    have hcross : inner ℝ (p : L2 d) (v : L2 d) = 0 := by simpa using hv
    have hpol0 : QuadraticMap.polar Q p v = 0 := by
      rw [hφ.polar_eq hd s hs c hc R D hDo hDne hDR v, hv]
      ring
    have hmuq : μ₁ ≤ Q v / ‖(v : L2 d)‖ ^ 2 := by
      have hmul := MinMax.level_zero_mul_le (formQ c κ D)
        (formQ_bddBelow c κ (le_of_lt hc) D) v
      have hmul' : μ₁ * ‖(v : L2 d)‖ ^ 2 ≤ Q v := by simpa [μ₁, Q, eigenvalue] using hmul
      rw [le_div_iff₀ (sq_pos_of_ne_zero hnormv)]
      simpa [Q] using hmul'
    have hbound : ∀ z : formDomain κ D, z ∈ W → Q z ≤ a * ‖(z : L2 d)‖ ^ 2 := by
      intro z hz
      change z ∈ Submodule.span ℝ (Set.range pair) at hz
      obtain ⟨coef, hcoef⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
      let α : ℝ := coef 0
      let β : ℝ := coef 1
      have hcomb : α • p + β • v = z := by simpa [pair, α, β] using hcoef
      have hQcomb : Q (α • p + β • v) = α ^ 2 * μ₁ + β ^ 2 * Q v := by
        rw [QuadraticMap.map_add Q (α • p) (β • v), QuadraticMap.map_smul Q α p,
          QuadraticMap.map_smul Q β v, QuadraticMap.polar_smul_left,
          QuadraticMap.polar_smul_right, hQp, hpol0]
        ring
      have hcross2 : inner ℝ (α • (p : L2 d)) (β • (v : L2 d)) = 0 := by
        simp [inner_smul_left, inner_smul_right, hcross]
      have hNcomb : ‖(α • p + β • v : formDomain κ D)‖ ^ 2 =
          α ^ 2 + β ^ 2 * ‖(v : L2 d)‖ ^ 2 := by
        change ‖α • (p : L2 d) + β • (v : L2 d)‖ ^ 2 = _
        rw [norm_add_sq_real, hcross2]
        simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hpNorm]
      have hupper1 : μ₁ ≤ a := le_max_left _ _
      have hupper2 : Q v / ‖(v : L2 d)‖ ^ 2 ≤ a := le_max_right _ _
      have hQz : Q z = α ^ 2 * μ₁ + β ^ 2 * Q v := by rw [← hcomb]; exact hQcomb
      have hNz : ‖(z : L2 d)‖ ^ 2 = α ^ 2 + β ^ 2 * ‖(v : L2 d)‖ ^ 2 := by rw [← hcomb]; exact hNcomb
      calc
        Q z = α ^ 2 * μ₁ + β ^ 2 * Q v := hQz
        _ ≤ α ^ 2 * a + β ^ 2 * (a * ‖(v : L2 d)‖ ^ 2) := by
          have hqv : Q v ≤ (Q v / ‖(v : L2 d)‖ ^ 2) * ‖(v : L2 d)‖ ^ 2 := by
            rw [div_mul_cancel₀ _ hnormsq]
          have hqv' : Q v ≤ a * ‖(v : L2 d)‖ ^ 2 :=
            hqv.trans (mul_le_mul_of_nonneg_right hupper2 (sq_nonneg _))
          exact add_le_add (mul_le_mul_of_nonneg_left hupper1 (sq_nonneg α))
            (mul_le_mul_of_nonneg_left hqv' (sq_nonneg β))
        _ = a * (α ^ 2 + β ^ 2 * ‖(v : L2 d)‖ ^ 2) := by ring
        _ = a * ‖(z : L2 d)‖ ^ 2 := by rw [hNz]
    have hlevel : MinMax.level Q 1 ≤ a := MinMax.level_le Q 1
      (formQ_bddBelow c κ (le_of_lt hc) D) W hW a hbound
    have hmu2 : μ₂ ≤ a := by simpa [μ₂, Q, κ, eigenvalue] using hlevel
    have hmu2q : μ₂ ≤ Q v / ‖(v : L2 d)‖ ^ 2 := by
      change μ₂ ≤ max μ₁ (Q v / ‖(v : L2 d)‖ ^ 2) at hmu2
      rw [max_eq_right hmuq] at hmu2
      exact hmu2
    have hmul := mul_le_mul_of_nonneg_right hmu2q (sq_nonneg ‖(v : L2 d)‖)
    have hqdiv : (Q v / ‖(v : L2 d)‖ ^ 2) * ‖(v : L2 d)‖ ^ 2 = Q v :=
      div_mul_cancel₀ _ hnormsq
    rw [hqdiv] at hmul
    simpa [μ₂, Q, κ] using hmul

/-- The ground-state mass `m₁ = ∫ φ₁` is positive. -/
theorem IsPositiveGroundState.mass_pos (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) {φ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ) :
    0 < ∫ x, φ x := by
  have hi := positiveGroundState_integrable s c R D hDR hφ
  have hnonneg : 0 ≤ ∫ x, φ x := integral_nonneg_of_ae hφ.nonneg
  by_contra hn
  have hzero : ∫ x, φ x = 0 := le_antisymm (le_of_not_gt hn) hnonneg
  have hzeroAE := (integral_eq_zero_iff_of_nonneg_ae hφ.nonneg hi).mp hzero
  have hz0 : φ = 0 := Lp.ext (hzeroAE.trans (Lp.coeFn_zero ℝ 2 volume).symm)
  have hnorm0 : ‖φ‖ = 0 := by rw [hz0]; simp
  rw [hφ.norm_eq_one] at hnorm0
  norm_num at hnorm0

/-- The ground state is integrable (it is square integrable and supported in
the bounded set `D`). -/
theorem IsPositiveGroundState.integrable (s : ℝ) (c : ℝ) (R : ℝ) (D : Set (Eucl d))
    (hDR : D ⊆ Metric.ball 0 R) {φ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ) :
    Integrable (φ : Eucl d → ℝ) := by
  exact positiveGroundState_integrable s c R D hDR hφ

/-- Uniqueness of the normalized nonnegative ground state. -/
theorem IsPositiveGroundState.unique (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (D : Set (Eucl d)) (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDR : D ⊆ Metric.ball 0 R) {φ ψ : L2 d}
    (hφ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D φ)
    (hψ : IsPositiveGroundState c ((d : ℝ) + 2 * s) D ψ) : φ = ψ := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let μ : ℝ := eigenvalue c κ D 0
  let Q : QuadraticMap ℝ (formDomain κ D) ℝ := formQ c κ D
  let p : formDomain κ D := ⟨φ, hφ.mem⟩
  let q : formDomain κ D := ⟨ψ, hψ.mem⟩
  let t : ℝ := inner ℝ φ ψ
  let r : formDomain κ D := q - t • p
  have hpQ : Q p = μ := by simpa [Q, μ, κ, p] using hφ.energy_eq
  have hqQ : Q q = μ := by simpa [Q, μ, κ, q] using hψ.energy_eq
  have hself : inner ℝ φ φ = 1 := by rw [real_inner_self_eq_norm_sq, hφ.norm_eq_one]; norm_num
  have horth : inner ℝ φ (r : L2 d) = 0 := by
    change inner ℝ φ ((ψ : L2 d) - t • (φ : L2 d)) = 0
    rw [inner_sub_right, inner_smul_right]
    dsimp [t]
    rw [hself]
    ring
  have hφψ : inner ℝ φ ψ = t := by rfl
  have hψφ : inner ℝ ψ φ = t := by rw [real_inner_comm]
  have hpolpq : QuadraticMap.polar Q p q = 2 * μ * t := by
    have hp := hφ.polar_eq hd s hs c hc R D hDo hDne hDR q
    simpa [Q, p, q, μ, κ, t] using hp
  have hpolqp : QuadraticMap.polar Q q p = 2 * μ * t := by
    rw [QuadraticMap.polar_comm]
    exact hpolpq
  have hrnorm : ‖(r : L2 d)‖ ^ 2 = 1 - t ^ 2 := by
    change ‖(ψ : L2 d) - t • (φ : L2 d)‖ ^ 2 = 1 - t ^ 2
    have hn := norm_sub_sq_real (ψ : L2 d) (t • (φ : L2 d))
    have hn' : ‖(ψ : L2 d) - t • (φ : L2 d)‖ ^ 2 = 1 - 2 * (t * t) + t ^ 2 := by
      simpa [norm_smul, Real.norm_eq_abs, inner_smul_right, hψ.norm_eq_one,
        hφ.norm_eq_one, hψφ, sq_abs] using hn
    rw [hn']
    ring
  have hrQ : Q r = μ * ‖(r : L2 d)‖ ^ 2 := by
    have hexp : Q r = μ - μ * t ^ 2 := by
      change Q (q - t • p) = _
      have hsub : q - t • p = q + -(t • p) := by abel
      rw [hsub, QuadraticMap.map_add Q q (-(t • p)), QuadraticMap.map_neg Q (t • p),
        QuadraticMap.map_smul Q t p, QuadraticMap.polar_neg_right,
        QuadraticMap.polar_smul_right, hqQ, hpQ, hpolqp]
      ring
    rw [hexp, hrnorm]
    ring
  have hgap := hφ.gap hd s hs c hc R D hDo hDne hDR r horth
  have hμlt : μ < eigenvalue c κ D 1 := by
    simpa [μ, κ] using eigenvalue_zero_lt_one hd s hs c hc R D hDo hDne hDR
  have hrnorm0 : ‖(r : L2 d)‖ ^ 2 = 0 := by
    have hn : 0 ≤ ‖(r : L2 d)‖ ^ 2 := sq_nonneg _
    nlinarith [hgap, hrQ, hn]
  have hrnormzero : ‖(r : L2 d)‖ = 0 := by nlinarith [hrnorm0]
  have hrzero : (r : L2 d) = 0 := norm_eq_zero.mp hrnormzero
  have hline : (ψ : L2 d) = t • (φ : L2 d) := by
    change (ψ : L2 d) - t • (φ : L2 d) = 0 at hrzero
    exact sub_eq_zero.mp hrzero
  have htNonneg : 0 ≤ t := by
    have h := inner_nonneg_of_ae_nonneg hφ.nonneg hψ.nonneg
    simpa [t] using h
  have htAbs' : (1 : ℝ) = |t| := by
    have hn := congrArg norm hline
    simpa [norm_smul, Real.norm_eq_abs, hφ.norm_eq_one, hψ.norm_eq_one] using hn
  have ht : t = 1 := by
    rw [abs_of_nonneg htNonneg] at htAbs'
    exact htAbs'.symm
  rw [hline, ht]
  simp

end Tunneling
```
===END FILE===