import Tunneling.Euclid.GroundState

/-!
# The Courant--Fischer levels are the eigenvalues of `A_G`

Paper Section 2 writes `λ₁(G) ≤ λ₂(G) ≤ ⋯` for the eigenvalues of the
operator `A_G` associated with the closed form `eq:form`, repeated according to
multiplicity.  In weak form, `λ` is an eigenvalue with eigenfunction
`u ∈ H^s_0(G) \ {0}` when `Q_G(u, v) = λ ⟪u, v⟫` for all `v ∈ H^s_0(G)`, i.e.
`polar Q_G u v = 2 λ ⟪u, v⟫`.

This file proves, for a bounded open nonempty `G`, that the levels
`eigenvalue c κ G k` enumerate exactly these eigenvalues with multiplicity:

* there is an orthonormal sequence of weak eigenfunctions with eigenvalues
  `eigenvalue c κ G k`;
* every weak eigenvalue is one of the levels;
* the weak eigenspace of `λ` has dimension `#{k | eigenvalue c κ G k = λ}`.
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- `u` is a weak eigenfunction of the restricted fractional Laplacian `A_G`
with eigenvalue `lam`. -/
def IsWeakEigenfunction (c κ : ℝ) (G : Set (Eucl d)) (lam : ℝ)
    (u : formDomain κ G) : Prop :=
  ∀ v : formDomain κ G,
    QuadraticMap.polar (formQ c κ G) u v = 2 * lam * inner ℝ (u : L2 d) (v : L2 d)

/-- The weak eigenspace of `A_G` for `lam`. -/
def weakEigenspace (c κ : ℝ) (G : Set (Eucl d)) (lam : ℝ) :
    Submodule ℝ (formDomain κ G) where
  carrier := {u | IsWeakEigenfunction c κ G lam u}
  zero_mem' := by
    intro v
    simp [IsWeakEigenfunction, QuadraticMap.polar]
  add_mem' := by
    intro u w hu hw v
    have h1 := hu v
    have h2 := hw v
    rw [QuadraticMap.polar_add_left, h1, h2]
    simp [inner_add_left, mul_add]
  smul_mem' := by
    intro t u hu v
    have h1 := hu v
    rw [QuadraticMap.polar_smul_left, h1]
    simp [inner_smul_left]
    ring

private theorem norm_inv_smul_eq_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V) (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [norm_smul]
  simp [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
  field_simp

private theorem exists_unit_mem_orthogonal {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} (e : Fin n → V) (W : Submodule ℝ V)
    (hW : Module.finrank ℝ W = n + 1) :
    ∃ v ∈ W, ‖v‖ = 1 ∧ ∀ i, inner ℝ (e i) v = 0 := by
  have hdimpos : 0 < Module.finrank ℝ W := by rw [hW]; omega
  letI : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_pos hdimpos
  let L : W →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun w i => inner ℝ (e i) (w : V)
      map_add' := by intro x y; funext i; simp [inner_add_right]
      map_smul' := by intro a x; funext i; simp [inner_smul_right] }
  have hlt : Module.finrank ℝ (Fin n → ℝ) < Module.finrank ℝ W := by simp [hW]
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨x, hxker, hxne⟩ := (Submodule.ne_bot_iff (LinearMap.ker L)).mp hker
  have hzero : ∀ i, inner ℝ (e i) (x : V) = 0 := by
    intro i
    have hh := congrFun (show L x = 0 from (hxker)) i
    simpa [L] using hh
  refine ⟨‖x‖⁻¹ • (x : V), W.smul_mem _ x.property, ?_, ?_⟩
  · exact norm_inv_smul_eq_one x hxne
  · intro i
    rw [inner_smul_right, hzero i, mul_zero]

private theorem orthonormal_snoc {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (e : Fin n → V) (he : Orthonormal ℝ e) (w : V)
    (hw : ‖w‖ = 1) (horth : ∀ i, inner ℝ (e i) w = 0) :
    Orthonormal ℝ (Fin.snoc e w) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [hw]
    | cast j =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [real_inner_comm, horth j]
      simpa using (Fin.castSucc_ne_last j).symm
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simpa [Fin.snoc_castSucc, Fin.snoc_last] using horth i
    | cast j =>
      simpa [Fin.snoc_castSucc] using (orthonormal_iff_ite.mp he i j)

private theorem polar_sum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : QuadraticMap ℝ V ℝ) {n : ℕ} (e : Fin n → V) (a b : Fin n → ℝ) :
    QuadraticMap.polar Q (∑ i, a i • e i) (∑ j, b j • e j) =
      ∑ i, ∑ j, a i * b j * QuadraticMap.polar Q (e i) (e j) := by
  classical
  rw [← QuadraticMap.polarBilin_apply_apply, LinearMap.map_sum₂]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  ring

private theorem polar_right_sum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : QuadraticMap ℝ V ℝ) (x : V) {n : ℕ} (e : Fin n → V) (a : Fin n → ℝ) :
    QuadraticMap.polar Q x (∑ i, a i • e i) =
      ∑ i, a i * QuadraticMap.polar Q x (e i) := by
  classical
  rw [← QuadraticMap.polarBilin_apply_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [QuadraticMap.polarBilin_apply_apply, smul_eq_mul]

private theorem ortho_sum_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (e : Fin n → V) (he : Orthonormal ℝ e) (a : Fin n → ℝ) :
    ‖∑ i, a i • e i‖ ^ 2 = ∑ i, a i ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp [real_inner_smul_left, he.inner_right_fintype, pow_two]

private theorem energy_ortho_sum_diag {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : QuadraticMap ℝ V ℝ) {n : ℕ} (e : Fin n → V)
    (μ : Fin n → ℝ)
    (hdiag : ∀ i j, QuadraticMap.polar Q (e i) (e j) =
      if i = j then 2 * μ i else 0)
    (a : Fin n → ℝ) :
    Q (∑ i, a i • e i) = ∑ i, a i ^ 2 * μ i := by
  classical
  have hpol := polar_sum Q e a a
  have hsimp : (∑ i, ∑ j, a i * a j * QuadraticMap.polar Q (e i) (e j)) =
      2 * ∑ i, a i ^ 2 * μ i := by
    simp_rw [hdiag]
    simp [eq_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hu := QuadraticMap.polar_self Q (∑ i, a i • e i)
  rw [hpol, hsimp, two_smul] at hu
  nlinarith

private theorem energy_le_span_diag {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : QuadraticMap ℝ V ℝ) {n : ℕ} (e : Fin n → V) (he : Orthonormal ℝ e)
    (μ : Fin n → ℝ)
    (hdiag : ∀ i j, QuadraticMap.polar Q (e i) (e j) =
      if i = j then 2 * μ i else 0)
    (a : ℝ) (ha : ∀ i, μ i ≤ a) {x : V}
    (hx : x ∈ Submodule.span ℝ (Set.range e)) : Q x ≤ a * ‖x‖ ^ 2 := by
  classical
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := e)).mp hx
  rw [← hf, energy_ortho_sum_diag Q e μ hdiag f, ortho_sum_norm_sq e he f]
  calc
    (∑ i, f i ^ 2 * μ i) ≤ ∑ i, f i ^ 2 * a := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (ha i) (sq_nonneg (f i))
    _ = a * ∑ i, f i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem le_of_forall_pos_add_real {a b : ℝ} (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := by
  by_contra hn
  have hba : b < a := lt_of_not_ge hn
  let ε := (a - b) / 2
  have heps : 0 < ε := by dsimp [ε]; linarith
  have hsmall := h ε heps
  dsimp [ε] at hsmall
  linarith

private theorem linear_zero_of_quadratic_nonneg {b c : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t * b + t ^ 2 * c) : b = 0 := by
  by_contra hb
  let D := 2 * (|c| + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  let t := -b / D
  have hpoly : t * b + t ^ 2 * c = b ^ 2 * (c - D) / D ^ 2 := by
    dsimp [t]
    field_simp [hD.ne']
    ring
  have hcd : c - D < 0 := by dsimp [D]; nlinarith [abs_nonneg c, le_abs_self c]
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hnegative : b ^ 2 * (c - D) / D ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_pos_of_neg hb2 hcd
    · exact sq_pos_of_pos hD
  have ht := h t
  rw [hpoly] at ht
  linarith

set_option maxHeartbeats 1000000 in
private theorem eigenfamily_lower
    (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1) (c : ℝ) (hc : 0 < c)
    (R : ℝ) (G : Set (Eucl d)) (hGo : IsOpen G) (hGne : G.Nonempty)
    (hGR : G ⊆ Metric.ball 0 R)
    (hmono : Monotone (eigenvalue c ((d : ℝ) + 2 * s) G)) :
    ∀ n, ∃ e : Fin n → formDomain ((d : ℝ) + 2 * s) G,
      Orthonormal ℝ (fun i => ((e i : formDomain ((d : ℝ) + 2 * s) G) : L2 d)) ∧
      (∀ i, IsWeakEigenfunction c ((d : ℝ) + 2 * s) G
          (eigenvalue c ((d : ℝ) + 2 * s) G i.val) (e i)) ∧
      ∀ v : formDomain ((d : ℝ) + 2 * s) G,
        (∀ i, inner ℝ (e i) v = 0) →
          eigenvalue c ((d : ℝ) + 2 * s) G n * ‖(v : L2 d)‖ ^ 2 ≤
            formQ c ((d : ℝ) + 2 * s) G v := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let Q := formQ c κ G
  let lev := eigenvalue c κ G
  have hQbdd : ∃ m : ℝ, ∀ v : formDomain κ G, m * ‖v‖ ^ 2 ≤ Q v :=
    formQ_bddBelow c κ (le_of_lt hc) G
  have hdim (n : ℕ) : ∃ W : Submodule ℝ (formDomain κ G), Module.finrank ℝ W = n + 1 := by
    exact exists_finrank_formDomain hd s hs G hGo hGne (n + 1)
  have hclosed : G ⊆ Metric.closedBall 0 R := by
    intro x hx
    have hxball := hGR hx
    exact Metric.ball_subset_closedBall hxball
  intro n
  induction n with
  | zero =>
      refine ⟨Fin.elim0, ?_, ?_, ?_⟩
      · rw [orthonormal_iff_ite]
        intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro v hv
        simpa [lev, eigenvalue, Q] using MinMax.level_zero_mul_le Q hQbdd v
  | succ n ih =>
      obtain ⟨e, he, hweak, hlower⟩ := ih
      have heV : Orthonormal ℝ e := by
        rw [orthonormal_iff_ite] at he ⊢
        intro i j
        simpa using he i j
      let levn := lev n
      let U : Set (formDomain κ G) := {v | ‖(v : L2 d)‖ = 1 ∧ ∀ i, inner ℝ (e i) v = 0}
      let S : Set ℝ := Q '' U
      have hUnon : U.Nonempty := by
        obtain ⟨W, hW⟩ := hdim n
        obtain ⟨v, hvW, hvnorm, hvorth⟩ := exists_unit_mem_orthogonal e W hW
        exact ⟨v, hvnorm, hvorth⟩
      have hSnon : S.Nonempty := by
        obtain ⟨v, hv⟩ := hUnon
        exact ⟨Q v, ⟨v, hv, rfl⟩⟩
      have hSbound : ∀ q ∈ S, levn ≤ q := by
        intro q hq
        rcases hq with ⟨v, hv, rfl⟩
        have h := hlower v hv.2
        simpa [levn, hv.1] using h
      have hSbdd : BddBelow S := ⟨levn, hSbound⟩
      let m : ℝ := sInf S
      have hlevnm : levn ≤ m := (le_csInf_iff hSbdd hSnon).2 hSbound
      have hmupper : m ≤ levn := by
        apply le_of_forall_pos_add_real
        intro ε hε
        have hlevel : MinMax.level Q n < levn + ε := by
          dsimp [levn, lev, eigenvalue, Q]
          exact lt_add_of_pos_right _ hε
        obtain ⟨W, hWdim, hWbound⟩ :=
          MinMax.exists_subspace_of_level_lt Q n (hdim n) (levn + ε) hlevel
        obtain ⟨v, hvW, hvnorm, hvorth⟩ := exists_unit_mem_orthogonal e W hWdim
        have hvQ : Q v ≤ levn + ε := by
          have hh := hWbound v hvW
          simpa [hvnorm] using hh
        have hvU : v ∈ U := ⟨hvnorm, hvorth⟩
        have hmq : m ≤ Q v := csInf_le hSbdd ⟨v, hvU, rfl⟩
        linarith
      have hm : m = levn := le_antisymm hmupper hlevnm
      have happrox : ∀ k : ℕ, ∃ v : formDomain κ G,
          ‖(v : L2 d)‖ = 1 ∧ (∀ i, inner ℝ (e i) v = 0) ∧ Q v < m + 1 / (k + 1 : ℝ) := by
        intro k
        have hlt : m < m + 1 / (k + 1 : ℝ) := by
          have : 0 < (1 : ℝ) / (k + 1 : ℝ) := by positivity
          linarith
        obtain ⟨q, hqS, hq⟩ := exists_lt_of_csInf_lt hSnon hlt
        rcases hqS with ⟨v, hv, rfl⟩
        exact ⟨v, hv.1, hv.2, hq⟩
      let vseq : ℕ → formDomain κ G := fun k => Classical.choose (happrox k)
      have hvseq : ∀ k, ‖(vseq k : L2 d)‖ = 1 ∧
          (∀ i, inner ℝ (e i) (vseq k) = 0) ∧ Q (vseq k) < m + 1 / (k + 1 : ℝ) :=
        fun k => Classical.choose_spec (happrox k)
      let f : ℕ → L2 d := fun k => (vseq k : L2 d)
      let M : ℝ := 2 * (m + 1) / c
      have hfmem : ∀ k, f k ∈ formDomain κ G := by
        intro k
        exact (vseq k).property
      have hfnorm : ∀ k, ‖f k‖ ≤ 1 := by
        intro k
        simpa [f] using (hvseq k).1.le
      have hM : ∀ k, gagliardoSeminormSq κ (volume : Measure (Eucl d))
          (f k : Eucl d → ℝ) ≤ M := by
        intro k
        have hqeq : Q (vseq k) =
            c / 2 * gagliardoSeminormSq κ (volume : Measure (Eucl d))
              ((vseq k : L2 d) : Eucl d → ℝ) := by
          simpa [Q] using formQ_apply c κ G (vseq k)
        have hqle : Q (vseq k) ≤ m + 1 := by
          have hrec : (0 : ℝ) ≤ 1 / (k + 1 : ℝ) := by positivity
          have hrec_le : (1 : ℝ) / (k + 1 : ℝ) ≤ 1 := by
            have hk : (1 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
            apply (div_le_iff₀ (by positivity)).2
            simpa using hk
          linarith [(hvseq k).2.2]
        have hprod : c * gagliardoSeminormSq κ (volume : Measure (Eucl d))
            ((vseq k : L2 d) : Eucl d → ℝ) ≤ 2 * (m + 1) := by
          nlinarith
        dsimp [M]
        exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hprod)
      obtain ⟨g, φ, hφ, hconv⟩ := exists_tendsto_subseq s hs R G hclosed f hfmem hfnorm M hM
      have hφat : Filter.Tendsto φ Filter.atTop Filter.atTop := hφ.tendsto_atTop
      have hrecip : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((φ k : ℝ) + 1))
          Filter.atTop (nhds 0) := by
        exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφat
      have hsemiBound : ∀ ε : ℝ, 0 < ε →
          ∀ᶠ k in Filter.atTop,
            gagliardoSeminormSq κ (volume : Measure (Eucl d))
              (f (φ k) : Eucl d → ℝ) ≤ 2 * (m + ε) / c := by
        intro ε hε
        have hevent : ∀ᶠ k in Filter.atTop,
            (1 : ℝ) / ((φ k : ℝ) + 1) < ε :=
          hrecip.eventually (Iio_mem_nhds hε)
        filter_upwards [hevent] with k hk
        have hqeq : Q (vseq (φ k)) =
            c / 2 * gagliardoSeminormSq κ (volume : Measure (Eucl d))
              ((vseq (φ k) : L2 d) : Eucl d → ℝ) := by
          simpa [Q] using formQ_apply c κ G (vseq (φ k))
        have hqle : Q (vseq (φ k)) ≤ m + ε := by
          have hstrict := (hvseq (φ k)).2.2
          exact hstrict.le.trans (by linarith)
        have hprod : c * gagliardoSeminormSq κ (volume : Measure (Eucl d))
            ((vseq (φ k) : L2 d) : Eucl d → ℝ) ≤ 2 * (m + ε) := by
          nlinarith
        exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hprod)
      have hsubconv : Filter.Tendsto (fun k => f (φ k)) Filter.atTop (nhds g) := hconv
      have hnormconv : Filter.Tendsto (fun k => ‖f (φ k)‖) Filter.atTop (nhds ‖g‖) := hconv.norm
      have hnormone : Filter.Tendsto (fun k => ‖f (φ k)‖) Filter.atTop (nhds 1) := by
        have hfun : (fun k => ‖f (φ k)‖) = fun _ => (1 : ℝ) := by
          funext k
          simpa [f] using (hvseq (φ k)).1
        rw [hfun]
        exact tendsto_const_nhds
      have hgNorm : ‖g‖ = 1 := by
        have h := tendsto_nhds_unique hnormone hnormconv
        linarith
      have hgmem : g ∈ formDomain κ G := by
        have hlsc := mem_formDomain_of_tendsto κ G (fun k => f (φ k)) g
          (fun k => hfmem (φ k)) hsubconv (2 * (m + 1) / c)
          (hsemiBound 1 (by norm_num))
        exact hlsc.1
      have hgorth : ∀ i, inner ℝ ((e i : formDomain κ G) : L2 d) g = 0 := by
        intro i
        have hinnerlim : Filter.Tendsto
            (fun k => inner ℝ ((e i : formDomain κ G) : L2 d) (f (φ k))) Filter.atTop
            (nhds (inner ℝ ((e i : formDomain κ G) : L2 d) g)) :=
          (tendsto_const_nhds : Filter.Tendsto
            (fun _ : ℕ => ((e i : formDomain κ G) : L2 d)) Filter.atTop
            (nhds ((e i : formDomain κ G) : L2 d))).inner hsubconv
        have hconst : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
        have hzero : (fun k => inner ℝ ((e i : formDomain κ G) : L2 d) (f (φ k))) =
            fun _ => (0 : ℝ) := by
          funext k
          simpa [f] using (hvseq (φ k)).2.1 i
        rw [hzero] at hinnerlim
        have hresult := tendsto_nhds_unique hinnerlim hconst
        simpa using hresult
      have hQg_le : Q ⟨g, hgmem⟩ ≤ m := by
        apply le_of_forall_pos_add_real
        intro ε hε
        have hlsc := mem_formDomain_of_tendsto κ G (fun k => f (φ k)) g
          (fun k => hfmem (φ k)) hsubconv (2 * (m + ε) / c) (hsemiBound ε hε)
        rw [formQ_apply]
        have hcineq := hlsc.2
        calc
          c / 2 * gagliardoSeminormSq κ (volume : Measure (Eucl d)) (g : Eucl d → ℝ) ≤
              c / 2 * (2 * (m + ε) / c) := mul_le_mul_of_nonneg_left hcineq (by positivity)
          _ = m + ε := by field_simp
      let en : formDomain κ G := ⟨g, hgmem⟩
      have henNorm : ‖(en : L2 d)‖ = 1 := hgNorm
      have henorth : ∀ i, inner ℝ (e i) en = 0 := by
        intro i
        simpa using hgorth i
      have hQen : Q en = levn := by
        have hlower := hlower en henorth
        have hnorm2 : ‖(en : L2 d)‖ ^ 2 = 1 := by rw [henNorm]; norm_num
        have hle : levn ≤ Q en := by simpa [hnorm2] using hlower
        have hQle : Q en ≤ m := by simpa [en] using hQg_le
        rw [hm] at hQle
        exact le_antisymm hQle hle
      have hencomp : ∀ v : formDomain κ G, (∀ i, inner ℝ (e i) v = 0) →
          QuadraticMap.polar Q en v = 2 * levn *
            inner ℝ (en : L2 d) (v : L2 d) := by
        intro v hv
        have hpoly : ∀ t : ℝ,
            0 ≤ t * (QuadraticMap.polar Q en v - 2 * levn *
              inner ℝ (en : L2 d) (v : L2 d)) +
              t ^ 2 * (Q v - levn * ‖(v : L2 d)‖ ^ 2) := by
          intro t
          have horth : ∀ i, inner ℝ (e i) (en + t • v) = 0 := by
            intro i
            have hvL2 : inner ℝ ((e i : formDomain κ G) : L2 d) (v : L2 d) = 0 := by simpa using hv i
            simp [inner_add_right, real_inner_smul_right, henorth i, hvL2]
          have hlower' := hlower (en + t • v) horth
          have hqexp : Q (en + t • v) =
              Q en + t * QuadraticMap.polar Q en v + t ^ 2 * Q v := by
            rw [QuadraticMap.map_add (Q : formDomain κ G → ℝ) en (t • v),
              Q.map_smul, QuadraticMap.polar_smul_right]
            simp only [smul_eq_mul]
            ring
          have hnexp :
              ‖((en + t • v : formDomain κ G) : L2 d)‖ ^ 2 =
                ‖(en : L2 d)‖ ^ 2 +
                  2 * t * inner ℝ (en : L2 d) (v : L2 d) +
                    t ^ 2 * ‖(v : L2 d)‖ ^ 2 := by
            change ‖((en : L2 d) + t • (v : L2 d))‖ ^ 2 = _
            rw [norm_add_sq_real, real_inner_smul_right, norm_smul]
            simp only [Real.norm_eq_abs, mul_pow, sq_abs]
            ring
          rw [hqexp, hnexp, hQen, henNorm] at hlower'
          nlinarith
        have hb := linear_zero_of_quadratic_nonneg hpoly
        linarith
      have hnewweak : ∀ v : formDomain κ G,
          QuadraticMap.polar Q en v = 2 * levn *
            inner ℝ (en : L2 d) (v : L2 d) := by
        intro v
        let a : Fin n → ℝ := fun i => inner ℝ (e i) v
        let p : formDomain κ G := ∑ i, a i • e i
        let w : formDomain κ G := v - p
        have hpcoord : ∀ i, inner ℝ (e i) p = a i := by
          intro i
          dsimp [p]
          exact heV.inner_right_fintype a i
        have hworth : ∀ i, inner ℝ (e i) w = 0 := by
          intro i
          change inner ℝ (e i : formDomain κ G) (v - p : formDomain κ G) = 0
          rw [inner_sub_right, hpcoord]
          simp [a]
        have hwEL := hencomp w hworth
        have hpolar0 : ∀ i, QuadraticMap.polar Q en (e i) = 0 := by
          intro i
          calc
            QuadraticMap.polar Q en (e i) = QuadraticMap.polar Q (e i) en :=
              QuadraticMap.polar_comm Q en (e i)
            _ = 2 * lev i.val * inner ℝ ((e i : formDomain κ G) : L2 d) (en : L2 d) :=
              hweak i en
            _ = 0 := by
              have hi : inner ℝ ((e i : formDomain κ G) : L2 d) (en : L2 d) = 0 := by
                simpa using henorth i
              simp [hi]
        have hpolarP : QuadraticMap.polar Q en p = 0 := by
          rw [polar_right_sum]
          simp_rw [hpolar0]
          simp
        have hinnerP : inner ℝ (en : L2 d) (p : L2 d) = 0 := by
          rw [real_inner_comm]
          have horthL2 : ∀ i, inner ℝ ((e i : formDomain κ G) : L2 d) (en : L2 d) = 0 := by
            intro i
            simpa using henorth i
          simp [p, sum_inner, real_inner_smul_left, horthL2]
        have hvdecomp : w + p = v := by dsimp [w]; exact sub_add_cancel v p
        calc
          QuadraticMap.polar Q en v = QuadraticMap.polar Q en (w + p) := by rw [← hvdecomp]
          _ = QuadraticMap.polar Q en w + QuadraticMap.polar Q en p :=
            QuadraticMap.polar_add_right Q en w p
          _ = 2 * levn * inner ℝ (en : L2 d) (w : L2 d) := by rw [hpolarP, hwEL]; ring
          _ = 2 * levn * inner ℝ (en : L2 d) (v : L2 d) := by
            rw [← hvdecomp]
            change 2 * levn * inner ℝ (en : L2 d) (w : L2 d) =
              2 * levn * inner ℝ (en : L2 d) ((w : L2 d) + (p : L2 d))
            rw [inner_add_right, hinnerP]
            ring
      let b : Fin (n + 1) → formDomain κ G := Fin.snoc e en
      have hbOrtho : Orthonormal ℝ b := orthonormal_snoc e heV en (by simpa using henNorm) henorth
      have hbWeak : ∀ i : Fin (n + 1), ∀ v : formDomain κ G,
          QuadraticMap.polar Q (b i) v = 2 * lev i.val *
            inner ℝ ((b i : formDomain κ G) : L2 d) (v : L2 d) := by
        intro i v
        induction i using Fin.lastCases with
        | cast i => simpa [b, Fin.snoc_castSucc, IsWeakEigenfunction] using hweak i v
        | last => simpa [b, Fin.snoc_last, lev] using hnewweak v
      have hbWeakV : ∀ i : Fin (n + 1), ∀ v : formDomain κ G,
          QuadraticMap.polar Q (b i) v = 2 * lev i.val * inner ℝ (b i) v := by
        intro i v
        simpa using hbWeak i v
      have hbDiag : ∀ i j : Fin (n + 1),
          QuadraticMap.polar Q (b i) (b j) = if i = j then 2 * lev i.val else 0 := by
        intro i j
        by_cases hij : i = j
        · subst j
          rw [hbWeak i (b i)]
          have hn : ‖((b i : formDomain κ G) : L2 d)‖ = 1 := by simpa using hbOrtho.norm_eq_one i
          have hi : inner ℝ ((b i : formDomain κ G) : L2 d) ((b i : formDomain κ G) : L2 d) = 1 := by
            rw [real_inner_self_eq_norm_sq, hn]
            norm_num
          rw [hi]
          simp
        · rw [hbWeakV i (b j), hbOrtho.inner_eq_zero hij]
          simp [hij]
      have hnewLower : ∀ v : formDomain κ G,
          (∀ i : Fin (n + 1), inner ℝ (b i) v = 0) →
          lev (n + 1) * ‖(v : L2 d)‖ ^ 2 ≤ Q v := by
        intro v hv
        by_cases hvzero : v = 0
        · subst v
          simp [Q]
        · let w : formDomain κ G := ‖(v : L2 d)‖⁻¹ • v
          have hwNorm : ‖(w : L2 d)‖ = 1 := by
            dsimp [w]
            exact norm_inv_smul_eq_one v hvzero
          have hworth : ∀ i : Fin (n + 1), inner ℝ (b i) w = 0 := by
            intro i
            change inner ℝ ((b i : formDomain κ G) : L2 d)
              (‖(v : L2 d)‖⁻¹ • (v : L2 d)) = 0
            rw [real_inner_smul_right]
            have hi : inner ℝ ((b i : formDomain κ G) : L2 d) (v : L2 d) = 0 := by simpa using hv i
            rw [hi]
            simp
          let f : Fin (n + 2) → formDomain κ G := Fin.snoc b w
          have hfOrtho : Orthonormal ℝ f := orthonormal_snoc b hbOrtho w hwNorm hworth
          let μ : Fin (n + 2) → ℝ := Fin.snoc (fun i : Fin (n + 1) => lev i.val) (Q w)
          have hfDiag : ∀ i j : Fin (n + 2),
              QuadraticMap.polar Q (f i) (f j) = if i = j then 2 * μ i else 0 := by
            intro i j
            induction i using Fin.lastCases with
            | cast i =>
              induction j using Fin.lastCases with
              | cast j =>
                simpa [f, b, μ, Fin.snoc_castSucc] using hbDiag i j
              | last =>
                simp only [f, Fin.snoc_castSucc, Fin.snoc_last, μ]
                rw [hbWeakV i w, hworth i]
                simp [Fin.castSucc_ne_last]
            | last =>
              induction j using Fin.lastCases with
              | cast j =>
                simp only [f, Fin.snoc_last, Fin.snoc_castSucc, μ]
                rw [QuadraticMap.polar_comm, hbWeakV j w, hworth j]
                have hne : Fin.last (n + 1) ≠ j.castSucc := Ne.symm (Fin.castSucc_ne_last j)
                simp [hne]
              | last =>
                simp [f, μ]
          have hdimW : Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = (n + 1) + 1 := by
            rw [finrank_span_eq_card hfOrtho.linearIndependent]
            simp
          have hbaseorth : ∀ j : Fin n, inner ℝ (e j) w = 0 := by
            intro j
            simpa [b, Fin.snoc_castSucc] using hworth j.castSucc
          have hμbound : ∀ i : Fin (n + 2), μ i ≤ Q w := by
            intro i
            induction i using Fin.lastCases with
            | last => simp [μ]
            | cast i =>
              simp [μ, Fin.snoc_castSucc]
              calc
                lev i.val ≤ lev n := hmono (Nat.le_of_lt_succ i.isLt)
                _ ≤ Q w := by
                  have hh := hlower w hbaseorth
                  simpa [lev, hwNorm] using hh
          have htest0 : MinMax.level Q (n + 1) ≤ Q w := by
            apply MinMax.level_le Q (n + 1) hQbdd
              (Submodule.span ℝ (Set.range f)) hdimW (Q w)
            intro x hx
            exact energy_le_span_diag Q f hfOrtho μ hfDiag (Q w) hμbound hx
          have htest : lev (n + 1) ≤ Q w := by
            simpa [lev, eigenvalue, Q] using htest0
          have hwQ : Q w = (‖(v : L2 d)‖⁻¹) ^ 2 * Q v := by
            dsimp [w]
            rw [Q.map_smul]
            simp only [smul_eq_mul]
            ring
          have hscale : Q v = Q w * ‖(v : L2 d)‖ ^ 2 := by
            have hvL2 : (v : L2 d) ≠ 0 := by
              intro h
              exact hvzero (Subtype.ext h)
            have hn0 : ‖(v : L2 d)‖ ≠ 0 :=
              ne_of_gt (norm_pos_iff.mpr hvL2)
            have hpow : (‖(v : L2 d)‖⁻¹) ^ 2 * ‖(v : L2 d)‖ ^ 2 = 1 := by
              rw [← mul_pow, inv_mul_cancel₀ hn0, one_pow]
            rw [hwQ]
            calc
              Q v = ((‖(v : L2 d)‖⁻¹) ^ 2 * ‖(v : L2 d)‖ ^ 2) * Q v := by
                rw [hpow]
                simp
              _ = (‖(v : L2 d)‖⁻¹) ^ 2 * Q v * ‖(v : L2 d)‖ ^ 2 := by ring
          have hmul := mul_le_mul_of_nonneg_right htest (sq_nonneg ‖(v : L2 d)‖)
          rw [← hscale] at hmul
          exact hmul
      have hbOrthoL2 : Orthonormal ℝ (fun i => ((b i : formDomain κ G) : L2 d)) := by
        rw [orthonormal_iff_ite] at hbOrtho ⊢
        intro i j
        simpa using hbOrtho i j
      refine ⟨b, hbOrthoL2, ?_, hnewLower⟩
      intro i v
      simpa [IsWeakEigenfunction, lev] using hbWeak i v

private theorem eigenvalue_mono_aux
    (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1) (c : ℝ) (hc : 0 < c)
    (G : Set (Eucl d)) (hGo : IsOpen G) (hGne : G.Nonempty) :
    Monotone (eigenvalue c ((d : ℝ) + 2 * s) G) := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let Q := formQ c κ G
  have hQbdd : ∃ m : ℝ, ∀ v : formDomain κ G, m * ‖v‖ ^ 2 ≤ Q v :=
    formQ_bddBelow c κ (le_of_lt hc) G
  apply monotone_nat_of_le_succ
  intro k
  have hdim : ∃ W : Submodule ℝ (formDomain κ G), Module.finrank ℝ W = k + 2 := by
    exact exists_finrank_formDomain hd s hs G hGo hGne (k + 2)
  simpa [eigenvalue, Q] using MinMax.level_mono Q k hQbdd hdim

private theorem eigenvalue_tendsto_of_family
    (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1) (c : ℝ) (hc : 0 < c)
    (R : ℝ) (G : Set (Eucl d)) (hGo : IsOpen G) (hGne : G.Nonempty)
    (hGR : G ⊆ Metric.ball 0 R)
    (hmono : Monotone (eigenvalue c ((d : ℝ) + 2 * s) G))
    (hfamily : ∀ n : ℕ, ∃ e : Fin n → formDomain ((d : ℝ) + 2 * s) G,
      Orthonormal ℝ (fun i => ((e i : formDomain ((d : ℝ) + 2 * s) G) : L2 d)) ∧
      ∀ i, IsWeakEigenfunction c ((d : ℝ) + 2 * s) G
        (eigenvalue c ((d : ℝ) + 2 * s) G i.val) (e i)) :
    Filter.Tendsto (eigenvalue c ((d : ℝ) + 2 * s) G) Filter.atTop Filter.atTop := by
  let κ : ℝ := (d : ℝ) + 2 * s
  let Q := formQ c κ G
  let lev := eigenvalue c κ G
  have hclosed : G ⊆ Metric.closedBall 0 R := by
    intro x hx
    have hxball := hGR hx
    exact Metric.ball_subset_closedBall hxball
  have hdim (k : ℕ) : ∃ W : Submodule ℝ (formDomain κ G), Module.finrank ℝ W = k + 1 := by
    exact exists_finrank_formDomain hd s hs G hGo hGne (k + 1)
  have hnonneg : ∀ k, 0 ≤ lev k := by
    intro k
    have h := MinMax.le_level Q k (fun _ => (0 : formDomain κ G)) (0 : ℝ)
      (fun v _ => by simpa using formQ_nonneg c κ (le_of_lt hc) G v) (hdim k)
    simpa [lev, eigenvalue, Q] using h
  have hunbounded : ∀ B : ℝ, ∃ k, B ≤ lev k := by
    intro B
    by_contra hnot
    push_neg at hnot
    have hBpos : 0 < B := by
      have h0 := hnonneg 0
      have hlt := hnot 0
      linarith
    let M : ℝ := 2 * B / c
    have hTB := totallyBounded_energySublevel s hs R G hclosed M
    obtain ⟨t, htfin, htcover⟩ :=
      Metric.totallyBounded_iff.mp hTB (1 / 2) (by norm_num)
    letI : Fintype t := htfin.fintype
    let N : ℕ := Fintype.card t + 1
    obtain ⟨e, he, hweak⟩ := hfamily N
    have henergy : ∀ i : Fin N, formQ c κ G (e i) = lev i.val := by
      intro i
      have hi := hweak i (e i)
      have hinner : inner ℝ ((e i : formDomain κ G) : L2 d)
          ((e i : formDomain κ G) : L2 d) = 1 := by
        rw [real_inner_self_eq_norm_sq, he.norm_eq_one i]
        norm_num
      rw [QuadraticMap.polar_self] at hi
      rw [two_smul, hinner] at hi
      nlinarith
    have hsemi : ∀ i : Fin N,
        gagliardoSeminormSq κ (volume : Measure (Eucl d))
          (((e i : formDomain κ G) : L2 d) : Eucl d → ℝ) ≤ M := by
      intro i
      have hq := formQ_apply c κ G (e i)
      have hprod : c * gagliardoSeminormSq κ (volume : Measure (Eucl d))
          (((e i : formDomain κ G) : L2 d) : Eucl d → ℝ) ≤ 2 * B := by
        have hlt := hnot i.val
        have hltQ : formQ c κ G (e i) < B := by
          rw [henergy i]
          exact hlt
        nlinarith [hq, hltQ]
      dsimp [M]
      exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hprod)
    have hsub : ∀ i : Fin N,
        ((e i : formDomain κ G) : L2 d) ∈
          {f : L2 d | f ∈ formDomain κ G ∧ ‖f‖ ≤ 1 ∧
            gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f : Eucl d → ℝ) ≤ M} := by
      intro i
      refine ⟨(e i).property, ?_, hsemi i⟩
      simpa [he.norm_eq_one i]
    have hcoveri : ∀ i : Fin N, ∃ x : t,
        dist ((e i : formDomain κ G) : L2 d) (x : L2 d) < 1 / 2 := by
      intro i
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (htcover (hsub i))
      obtain ⟨hxt, hball⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨x, hxt⟩, Metric.mem_ball.mp hball⟩
    let center : Fin N → t := fun i => Classical.choose (hcoveri i)
    have hcenter : ∀ i, dist ((e i : formDomain κ G) : L2 d) (center i : L2 d) < 1 / 2 :=
      fun i => Classical.choose_spec (hcoveri i)
    have hcenter_inj : Function.Injective center := by
      intro i j hij
      by_contra hne
      have hnormsq : ‖((e i : formDomain κ G) : L2 d) -
          ((e j : formDomain κ G) : L2 d)‖ ^ 2 = 2 := by
        rw [norm_sub_sq_real, he.norm_eq_one i, he.inner_eq_zero hne, he.norm_eq_one j]
        norm_num
      have hdistlarge : 1 <
          dist ((e i : formDomain κ G) : L2 d) ((e j : formDomain κ G) : L2 d) := by
        rw [dist_eq_norm]
        let x := ‖((e i : formDomain κ G) : L2 d) - ((e j : formDomain κ G) : L2 d)‖
        have hxnonneg : 0 ≤ x := norm_nonneg _
        by_contra hx
        have hxle : x ≤ 1 := le_of_not_gt hx
        have hxprod : 0 ≤ x * (1 - x) := mul_nonneg hxnonneg (sub_nonneg.mpr hxle)
        have hxSq : x ^ 2 = 2 := by simpa [x] using hnormsq
        nlinarith [hxSq, hxprod]
      have hji : dist ((e j : formDomain κ G) : L2 d) (center i : L2 d) < 1 / 2 := by
        rw [hij]
        exact hcenter j
      have htri := dist_triangle ((e i : formDomain κ G) : L2 d)
        (center i : L2 d) ((e j : formDomain κ G) : L2 d)
      have hsmall : dist ((e i : formDomain κ G) : L2 d)
          ((e j : formDomain κ G) : L2 d) < 1 := by
        calc
          dist ((e i : formDomain κ G) : L2 d) ((e j : formDomain κ G) : L2 d)
              ≤ dist ((e i : formDomain κ G) : L2 d) (center i : L2 d) +
                dist (center i : L2 d) ((e j : formDomain κ G) : L2 d) := htri
          _ < 1 := by
            have hright : dist (center i : L2 d) ((e j : formDomain κ G) : L2 d) < 1 / 2 := by
              simpa [dist_comm] using hji
            linarith [hcenter i, hright]
      linarith [hdistlarge, hsmall]
    have hcard := Fintype.card_le_of_injective center hcenter_inj
    simp [N] at hcard
  apply Filter.tendsto_atTop.2
  intro B
  obtain ⟨N, hN⟩ := hunbounded B
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn =>
    hN.trans (hmono hn)⟩] with n hn
  exact hn

private theorem exists_level_of_weak
    (c κ : ℝ) (G : Set (Eucl d)) (lam : ℝ)
    (htendsto : Filter.Tendsto (eigenvalue c κ G) Filter.atTop Filter.atTop)
    (hfamily : ∀ n : ℕ, ∃ e : Fin n → formDomain κ G,
      Orthonormal ℝ (fun i => ((e i : formDomain κ G) : L2 d)) ∧
      (∀ i, IsWeakEigenfunction c κ G (eigenvalue c κ G i.val) (e i)) ∧
      ∀ v : formDomain κ G,
        (∀ i, inner ℝ (e i) v = 0) →
          eigenvalue c κ G n * ‖(v : L2 d)‖ ^ 2 ≤ formQ c κ G v)
    (u : formDomain κ G) (hu : u ≠ 0)
    (heig : IsWeakEigenfunction c κ G lam u) :
    ∃ k : ℕ, eigenvalue c κ G k = lam := by
  by_cases hex : ∃ k, eigenvalue c κ G k = lam
  · exact hex
  · have hneq : ∀ k, eigenvalue c κ G k ≠ lam := by
      intro k heq
      exact hex ⟨k, heq⟩
    have hev : ∀ᶠ k in Filter.atTop, lam < eigenvalue c κ G k := by
      filter_upwards [(Filter.tendsto_atTop.1 htendsto) (lam + 1)] with k hk
      linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    have hNlam : lam < eigenvalue c κ G N := hN N le_rfl
    obtain ⟨e, he, hweak, hlower⟩ := hfamily N
    have horth : ∀ i : Fin N, inner ℝ (e i) u = 0 := by
      intro i
      have h1 := heig (e i)
      have h2 := hweak i u
      rw [QuadraticMap.polar_comm] at h1
      rw [real_inner_comm] at h1
      have hmul : (2 * lam - 2 * eigenvalue c κ G i.val) *
          inner ℝ ((e i : formDomain κ G) : L2 d) (u : L2 d) = 0 := by
        rw [h1] at h2
        nlinarith [h2]
      have hcoeff : 2 * lam - 2 * eigenvalue c κ G i.val ≠ 0 := by
        intro hc
        apply hneq i.val
        linarith
      have hz := (mul_eq_zero.mp hmul).resolve_left hcoeff
      simpa using hz
    have hlow := hlower u horth
    have hQu : formQ c κ G u = lam * ‖(u : L2 d)‖ ^ 2 := by
      have h := heig u
      rw [QuadraticMap.polar_self, two_smul, real_inner_self_eq_norm_sq] at h
      nlinarith
    have hnormpos : 0 < ‖(u : L2 d)‖ ^ 2 := by
      have huL2 : (u : L2 d) ≠ 0 := by
        intro hzero
        apply hu
        apply Subtype.ext
        exact hzero
      exact sq_pos_of_pos (norm_pos_iff.mpr huL2)
    nlinarith

private theorem finrank_aux
    (c κ : ℝ) (G : Set (Eucl d)) (lam : ℝ)
    (hmono : Monotone (eigenvalue c κ G))
    (htendsto : Filter.Tendsto (eigenvalue c κ G) Filter.atTop Filter.atTop)
    (hfamily : ∀ n : ℕ, ∃ e : Fin n → formDomain κ G,
      Orthonormal ℝ (fun i => ((e i : formDomain κ G) : L2 d)) ∧
      (∀ i, IsWeakEigenfunction c κ G (eigenvalue c κ G i.val) (e i)) ∧
      ∀ v : formDomain κ G,
        (∀ i, inner ℝ (e i) v = 0) →
          eigenvalue c κ G n * ‖(v : L2 d)‖ ^ 2 ≤ formQ c κ G v) :
    FiniteDimensional ℝ (weakEigenspace c κ G lam) ∧
      Module.finrank ℝ (weakEigenspace c κ G lam) =
        Nat.card {k : ℕ // eigenvalue c κ G k = lam} := by
  classical
  let lev := eigenvalue c κ G
  have hev : ∀ᶠ k in Filter.atTop, lam < lev k := by
    filter_upwards [(Filter.tendsto_atTop.1 htendsto) (lam + 1)] with k hk
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hNlam : lam < lev N := hN N le_rfl
  obtain ⟨e, he, hweak, hlower⟩ := hfamily N
  let I : Set (Fin N) := {i | eigenvalue c κ G i.val = lam}
  letI : Fintype I := Fintype.ofFinite I
  let g : I → formDomain κ G := fun i => e i.val
  have hGI : ∀ i : I, IsWeakEigenfunction c κ G lam (g i) := by
    intro i
    have hi := hweak i.val
    have hEq : eigenvalue c κ G i.val = lam := i.property
    simpa [g, hEq] using hi
  let S : Submodule ℝ (formDomain κ G) := Submodule.span ℝ (Set.range g)
  have hSincl : S ≤ weakEigenspace c κ G lam := by
    apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    exact hGI i
  have heV : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite] at he ⊢
    intro i j
    simpa using he i j
  have hgV : Orthonormal ℝ g := heV.comp (fun i : I => i.val) Subtype.val_injective
  have hEqSub : weakEigenspace c κ G lam = S := by
    apply le_antisymm
    · intro u hu
      have huEig : IsWeakEigenfunction c κ G lam u := hu
      let a : Fin N → ℝ := fun i =>
        inner ℝ ((e i : formDomain κ G) : L2 d) (u : L2 d)
      let p : formDomain κ G := ∑ i, a i • e i
      have hpcoord : ∀ i : Fin N, inner ℝ (e i) p = a i := by
        intro i
        dsimp [p]
        change inner ℝ ((e i : formDomain κ G) : L2 d)
          (((∑ j, a j • e j : formDomain κ G) : formDomain κ G) : L2 d) = a i
        simp only [Submodule.coe_sum, Submodule.coe_smul]
        exact he.inner_right_fintype a i
      have hcoeffzero : ∀ i : Fin N, lev i.val ≠ lam → a i = 0 := by
        intro i hneq
        have h1 := huEig (e i)
        have h2 := hweak i u
        rw [QuadraticMap.polar_comm] at h1
        rw [real_inner_comm] at h1
        have hmul :
            (2 * lam - 2 * lev i.val) *
              inner ℝ ((e i : formDomain κ G) : L2 d) (u : L2 d) = 0 := by
          rw [h1] at h2
          nlinarith [h2]
        have hc : 2 * lam - 2 * lev i.val ≠ 0 := by
          intro hc
          apply hneq
          linarith
        have hzero := (mul_eq_zero.mp hmul).resolve_left hc
        simpa [a] using hzero
      have hpS : p ∈ S := by
        dsimp [p, S]
        apply Submodule.sum_mem
        intro i hi
        by_cases hEq : lev i.val = lam
        · exact Submodule.smul_mem _ _ (Submodule.subset_span
            (show e i ∈ Set.range g from ⟨⟨i, hEq⟩, rfl⟩))
        · have hz := hcoeffzero i hEq
          simp [a, hz]
      let w : formDomain κ G := u - p
      have hworth : ∀ i : Fin N, inner ℝ (e i) w = 0 := by
        intro i
        change inner ℝ ((e i : formDomain κ G) : L2 d)
          ((u - p : formDomain κ G) : L2 d) = 0
        rw [Submodule.coe_sub, inner_sub_right]
        have hpcoordL2 : inner ℝ ((e i : formDomain κ G) : L2 d)
            ((p : formDomain κ G) : L2 d) = a i := by
          simpa using hpcoord i
        rw [hpcoordL2]
        simp [a]
      have hpWeak : p ∈ weakEigenspace c κ G lam := hSincl hpS
      have hwWeak : w ∈ weakEigenspace c κ G lam := by
        have h := (weakEigenspace c κ G lam).sub_mem hu hpWeak
        simpa [w] using h
      have hQw : formQ c κ G w = lam * ‖(w : L2 d)‖ ^ 2 := by
        have h := hwWeak w
        rw [QuadraticMap.polar_self, two_smul, real_inner_self_eq_norm_sq] at h
        nlinarith
      have hwzero : w = 0 := by
        by_contra hwn
        have hwL2 : (w : L2 d) ≠ 0 := by
          intro h
          apply hwn
          exact Subtype.ext h
        have hnpos : 0 < ‖(w : L2 d)‖ ^ 2 :=
          sq_pos_of_pos (norm_pos_iff.mpr hwL2)
        have hlow := hlower w hworth
        rw [hQw] at hlow
        nlinarith
      have hEq : u = p := by
        have hzero : u - p = 0 := by simpa [w] using hwzero
        exact sub_eq_zero.mp hzero
      rw [hEq]
      exact hpS
    · exact hSincl
  have hboundJ : ∀ k : {k : ℕ // lev k = lam}, k.val < N := by
    intro k
    by_contra hk
    have hNk : N ≤ k.val := Nat.le_of_not_gt hk
    have hmon := hmono hNk
    change lev N ≤ lev k.val at hmon
    rw [k.property] at hmon
    exact (not_le_of_gt hNlam) hmon
  let J := {k : ℕ // lev k = lam}
  let eI : I ≃ J := {
    toFun := fun i => ⟨i.val.val, i.property⟩
    invFun := fun k => ⟨⟨k.val, hboundJ k⟩, k.property⟩
    left_inv := by
      intro i
      apply Subtype.ext
      apply Fin.ext
      rfl
    right_inv := by
      intro k
      apply Subtype.ext
      rfl
  }
  have hcard : Nat.card J = Fintype.card I := by
    calc
      Nat.card J = Nat.card I := (Nat.card_congr eI).symm
      _ = Fintype.card I := by simp
  have hfdS : FiniteDimensional ℝ S := by
    dsimp [S]
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range g)
  have hfinrankS : Module.finrank ℝ S = Fintype.card I := by
    dsimp [S]
    exact finrank_span_eq_card hgV.linearIndependent
  have hfdE : FiniteDimensional ℝ (weakEigenspace c κ G lam) :=
    hEqSub.symm ▸ hfdS
  constructor
  · exact hfdE
  · calc
      Module.finrank ℝ (weakEigenspace c κ G lam) = Module.finrank ℝ S := by rw [hEqSub]
      _ = Fintype.card I := hfinrankS
      _ = Nat.card J := hcard.symm

/-- The levels are attained by an orthonormal family of weak eigenfunctions. -/
theorem exists_orthonormal_eigenfunctions (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (G : Set (Eucl d)) (hGo : IsOpen G)
    (hGne : G.Nonempty) (hGR : G ⊆ Metric.ball 0 R) (n : ℕ) :
    ∃ e : Fin n → formDomain ((d : ℝ) + 2 * s) G,
      Orthonormal ℝ (fun i => ((e i : formDomain ((d : ℝ) + 2 * s) G) : L2 d)) ∧
        ∀ i : Fin n, IsWeakEigenfunction c ((d : ℝ) + 2 * s) G
          (eigenvalue c ((d : ℝ) + 2 * s) G i.val) (e i) := by
  have hmono := eigenvalue_mono_aux hd s hs c hc G hGo hGne
  obtain ⟨e, he, hweak, _hlower⟩ :=
    eigenfamily_lower hd s hs c hc R G hGo hGne hGR hmono n
  exact ⟨e, he, hweak⟩
/-- The levels are nondecreasing and tend to infinity. -/
theorem eigenvalue_monotone_tendsto (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (G : Set (Eucl d)) (hGo : IsOpen G)
    (hGne : G.Nonempty) (hGR : G ⊆ Metric.ball 0 R) :
    Monotone (eigenvalue c ((d : ℝ) + 2 * s) G) ∧
      Filter.Tendsto (eigenvalue c ((d : ℝ) + 2 * s) G) Filter.atTop Filter.atTop := by
  have hmono := eigenvalue_mono_aux hd s hs c hc G hGo hGne
  have hfamily :
      ∀ n : ℕ, ∃ e : Fin n → formDomain ((d : ℝ) + 2 * s) G,
        Orthonormal ℝ (fun i => ((e i : formDomain ((d : ℝ) + 2 * s) G) : L2 d)) ∧
          ∀ i, IsWeakEigenfunction c ((d : ℝ) + 2 * s) G
            (eigenvalue c ((d : ℝ) + 2 * s) G i.val) (e i) := by
    intro n
    obtain ⟨e, he, hweak, _hlower⟩ :=
      eigenfamily_lower hd s hs c hc R G hGo hGne hGR hmono n
    exact ⟨e, he, hweak⟩
  refine ⟨hmono, ?_⟩
  exact eigenvalue_tendsto_of_family hd s hs c hc R G hGo hGne hGR hmono hfamily
/-- Every weak eigenvalue of `A_G` is one of the levels. -/
theorem exists_eigenvalue_eq_of_weakEigenfunction (hd : 1 ≤ d) (s : ℝ)
    (hs : 0 < s ∧ s < 1) (c : ℝ) (hc : 0 < c) (R : ℝ) (G : Set (Eucl d))
    (hGo : IsOpen G) (hGne : G.Nonempty) (hGR : G ⊆ Metric.ball 0 R) (lam : ℝ)
    (u : formDomain ((d : ℝ) + 2 * s) G) (hu : u ≠ 0)
    (heig : IsWeakEigenfunction c ((d : ℝ) + 2 * s) G lam u) :
    ∃ k : ℕ, eigenvalue c ((d : ℝ) + 2 * s) G k = lam := by
  let κ : ℝ := (d : ℝ) + 2 * s
  have hmono := eigenvalue_mono_aux hd s hs c hc G hGo hGne
  have hfamily :
      ∀ n : ℕ, ∃ e : Fin n → formDomain κ G,
        Orthonormal ℝ (fun i => ((e i : formDomain κ G) : L2 d)) ∧
          (∀ i, IsWeakEigenfunction c κ G (eigenvalue c κ G i.val) (e i)) ∧
          ∀ v : formDomain κ G,
            (∀ i, inner ℝ (e i) v = 0) →
              eigenvalue c κ G n * ‖(v : L2 d)‖ ^ 2 ≤ formQ c κ G v := by
    intro n
    simpa [κ] using
      (eigenfamily_lower hd s hs c hc R G hGo hGne hGR hmono n)
  have hplain :
      ∀ n : ℕ, ∃ e : Fin n → formDomain κ G,
        Orthonormal ℝ (fun i => ((e i : formDomain κ G) : L2 d)) ∧
          ∀ i, IsWeakEigenfunction c κ G (eigenvalue c κ G i.val) (e i) := by
    intro n
    obtain ⟨e, he, hweak, _hlower⟩ := hfamily n
    exact ⟨e, he, hweak⟩
  have htendsto :=
    eigenvalue_tendsto_of_family hd s hs c hc R G hGo hGne hGR hmono hplain
  exact exists_level_of_weak c κ G lam htendsto hfamily u hu heig
/-- Multiplicity: the weak eigenspace of `lam` has dimension equal to the
number of levels equal to `lam` (so the levels are the eigenvalues repeated
according to multiplicity). -/
theorem finrank_weakEigenspace (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (G : Set (Eucl d)) (hGo : IsOpen G)
    (hGne : G.Nonempty) (hGR : G ⊆ Metric.ball 0 R) (lam : ℝ) :
    FiniteDimensional ℝ (weakEigenspace c ((d : ℝ) + 2 * s) G lam) ∧
      Module.finrank ℝ (weakEigenspace c ((d : ℝ) + 2 * s) G lam) =
        Nat.card {k : ℕ // eigenvalue c ((d : ℝ) + 2 * s) G k = lam} := by
  let κ : ℝ := (d : ℝ) + 2 * s
  have hmono := eigenvalue_mono_aux hd s hs c hc G hGo hGne
  have hfamily :
      ∀ n : ℕ, ∃ e : Fin n → formDomain κ G,
        Orthonormal ℝ (fun i => ((e i : formDomain κ G) : L2 d)) ∧
          (∀ i, IsWeakEigenfunction c κ G (eigenvalue c κ G i.val) (e i)) ∧
          ∀ v : formDomain κ G,
            (∀ i, inner ℝ (e i) v = 0) →
              eigenvalue c κ G n * ‖(v : L2 d)‖ ^ 2 ≤ formQ c κ G v := by
    intro n
    simpa [κ] using
      (eigenfamily_lower hd s hs c hc R G hGo hGne hGR hmono n)
  have hplain :
      ∀ n : ℕ, ∃ e : Fin n → formDomain κ G,
        Orthonormal ℝ (fun i => ((e i : formDomain κ G) : L2 d)) ∧
          ∀ i, IsWeakEigenfunction c κ G (eigenvalue c κ G i.val) (e i) := by
    intro n
    obtain ⟨e, he, hweak, _hlower⟩ := hfamily n
    exact ⟨e, he, hweak⟩
  have htendsto :=
    eigenvalue_tendsto_of_family hd s hs c hc R G hGo hGne hGR hmono hplain
  exact finrank_aux c κ G lam hmono htendsto hfamily

end Tunneling
