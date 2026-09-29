import Tunneling.Euclid.Main
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Corollaries of the main theorems (paper Corollaries 3.4 and 4.4--4.8)
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}


private theorem sigmaKappa_fin_two_eq_dist (a : Fin 2 → Eucl d) (p : ℝ)
    (_ha : a 0 ≠ a 1) :
    sigmaKappa a p = ‖a 0 - a 1‖ ^ (-p) := by
  classical
  let row : Fin 2 → ℝ := fun i =>
    ∑ j, (if i = j then (0 : ℝ) else ‖a i - a j‖ ^ (-p))
  have h0 : row 0 = ‖a 0 - a 1‖ ^ (-p) := by
    simp [row, Fin.sum_univ_two]
  have h1 : row 1 = ‖a 0 - a 1‖ ^ (-p) := by
    simp [row, Fin.sum_univ_two, norm_sub_rev]
  unfold sigmaKappa
  change (⨆ i : Fin 2, row i) = _
  apply le_antisymm
  · apply ciSup_le
    intro i
    fin_cases i <;> simp [h0, h1]
  · calc
      ‖a 0 - a 1‖ ^ (-p) = row 0 := h0.symm
      _ ≤ sigmaKappa a p := row_le_sigmaKappa a p 0

private theorem sigmaKappa_twoWellSites_eq_one (e : Eucl d) (he : ‖e‖ = 1) (p : ℝ) :
    sigmaKappa (twoWellSites e) p = 1 := by
  have hvec : -((1 / 2 : ℝ) • e) - (1 / 2 : ℝ) • e = -e := by
    rw [← neg_smul, ← sub_smul]
    norm_num
  have hdist : ‖twoWellSites e 0 - twoWellSites e 1‖ = 1 := by
    change ‖-((1 / 2 : ℝ) • e) - (1 / 2 : ℝ) • e‖ = 1
    rw [hvec, norm_neg, he]
  have hne : twoWellSites e 0 ≠ twoWellSites e 1 := by
    intro h
    have hh := congrArg norm (sub_eq_zero.mpr h)
    rw [hdist] at hh
    norm_num at hh
  rw [sigmaKappa_fin_two_eq_dist (twoWellSites e) p hne, hdist, Real.one_rpow]

private theorem multiTwo_remainder_aux (A : TwoWellConstants) (e : Eucl d)
    (he : ‖e‖ = 1) (L : ℝ) :
    multiWellEpsilon A (twoWellSites e) L +
        2 * multiWellGamma A (twoWellSites e) L ^ 2 / A.gap =
      A.remainder L := by
  rw [show multiWellEpsilon A (twoWellSites e) L =
      A.c * A.C * A.phiMass ^ 2 * L ^ (-A.kappa - 2) by
        simp [multiWellEpsilon, sigmaKappa_twoWellSites_eq_one e he]]
  rw [show multiWellGamma A (twoWellSites e) L = A.beta L by
        simp [multiWellGamma, TwoWellConstants.beta,
          sigmaKappa_twoWellSites_eq_one e he]]
  rfl

private theorem equidistant_affineIndependent {d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (a : ι → Eucl d) (r : ℝ) (hr : 0 < r)
    (hdist : ∀ i j, i ≠ j → ‖a i - a j‖ = r) : AffineIndependent ℝ a := by
  classical
  let i0 : ι := Classical.choice inferInstance
  let I := {i : ι // i ≠ i0}
  let v : I → Eucl d := fun i => a i - a i0
  have hgram : Matrix.gram ℝ v =
      (r ^ 2 / 2) • ((1 : Matrix I I ℝ) + Matrix.gram ℝ (fun _ : I => (1 : ℝ))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hi : (i : ι) ≠ i0 := i.property
      have hd := hdist i i0 hi
      simp only [Matrix.gram_apply, Matrix.one_apply, Matrix.add_apply,
        Matrix.smul_apply, ite_true]
      rw [real_inner_self_eq_norm_sq]
      rw [hd]
      simp only [real_inner_self_eq_norm_sq, norm_one, one_pow]
      ring
    · have hij' : (i : ι) ≠ j := by
        intro he
        exact hij (Subtype.ext he)
      have hni : ‖v i‖ = r := hdist i i0 i.property
      have hnj : ‖v j‖ = r := hdist j i0 j.property
      have hnd : ‖v i - v j‖ = r := by
        rw [show v i - v j = a i - a j by dsimp [v]; abel]
        exact hdist i j hij'
      simp only [Matrix.gram_apply, Matrix.one_apply, Matrix.add_apply,
        Matrix.smul_apply, if_neg hij]
      rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
      rw [hni, hnj, hnd]
      simp only [real_inner_self_eq_norm_sq, norm_one, one_pow]
      ring
  have hpos : (Matrix.gram ℝ v).PosDef := by
    rw [hgram]
    apply (Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_gram ℝ (fun _ : I => (1 : ℝ)))).smul
    positivity
  have hli : LinearIndependent ℝ v := Matrix.linearIndependent_of_posDef_gram hpos
  rw [affineIndependent_iff_linearIndependent_vsub ℝ a i0]
  simpa [v, vsub_eq_sub] using hli

private theorem row_const_offdiag {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (w : ℝ) (z : ι → ℝ) :
    (∑ j, (if i = j then (0 : ℝ) else -w) * z j) =
      w * z i - w * ∑ j, z j := by
  calc
    _ = ∑ j, ((-w) * z j - if i = j then (-w) * z j else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : i = j <;> simp [h]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.mul_sum]
      ring

private theorem const_offdiag_eigen_class {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (M : Matrix ι ι ℝ) (w lam : ℝ)
    (hM : ∀ i j, M i j = if i = j then 0 else -w)
    (z : ι → ℝ) (hz : z ≠ 0) (heig : M.mulVec z = lam • z) :
    lam = w ∨
      (lam = -(((Fintype.card ι : ℝ) - 1) * w) ∧
        ∀ i, z i = z (Classical.choice ‹Nonempty ι›)) := by
  classical
  let b : ι := Classical.choice ‹Nonempty ι›
  have hmul : M.mulVec z = fun i => w * z i - w * ∑ j, z j := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    calc
      ∑ j, M i j * z j = ∑ j, (if i = j then (0 : ℝ) else -w) * z j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hM]
      _ = w * z i - w * ∑ j, z j := row_const_offdiag i w z
  have hrow (i : ι) : w * z i - w * ∑ j, z j = lam * z i := by
    have h := congrFun heig i
    rw [hmul] at h
    simpa [smul_eq_mul] using h
  by_cases hw : lam = w
  · exact Or.inl hw
  · right
    have hf : w - lam ≠ 0 := by
      intro h
      exact hw (by linarith)
    have hprod (i : ι) : (w - lam) * z i = w * ∑ j, z j := by
      have := hrow i
      nlinarith
    have hconst (i : ι) : z i = z b := by
      have hh : (w - lam) * (z i - z b) = 0 := by
        calc
          (w - lam) * (z i - z b) = (w - lam) * z i - (w - lam) * z b :=
            mul_sub _ _ _
          _ = w * ∑ j, z j - w * ∑ j, z j := by rw [hprod i, hprod b]
          _ = 0 := sub_self _
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hf)
    have hq : z b ≠ 0 := by
      intro hzero
      apply hz
      funext i
      simp [hconst i, hzero]
    have hsum : (∑ i, z i) = (Fintype.card ι : ℝ) * z b := by
      calc
        _ = ∑ i, z b := Finset.sum_congr rfl fun i hi => hconst i
        _ = _ := by simp
    have hlast := hrow b
    rw [hsum] at hlast
    have hzero : (lam + ((Fintype.card ι : ℝ) - 1) * w) * z b = 0 := by
      nlinarith [hlast]
    have hcoef : lam + ((Fintype.card ι : ℝ) - 1) * w = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hq
    exact ⟨by linarith, hconst⟩

private theorem uniform_sign_dot_ne {ι : Type*} [Fintype ι] [Nonempty ι]
    (u v : ι → ℝ) (hu : (∀ i, 0 < u i) ∨ (∀ i, u i < 0))
    (hv : (∀ i, 0 < v i) ∨ (∀ i, v i < 0)) :
    (∑ i, u i * v i) ≠ 0 := by
  classical
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact ne_of_gt (Finset.sum_pos (s := Finset.univ)
      (fun i hi => mul_pos (hu i) (hv i)) Finset.univ_nonempty)
  · have hp := Finset.sum_pos (s := Finset.univ)
      (fun i hi => mul_pos (hu i) (neg_pos.mpr (hv i))) Finset.univ_nonempty
    have hsum : (∑ i, u i * v i) = -∑ i, -(u i * v i) := by
      rw [← Finset.sum_neg_distrib]
      simp
    rw [hsum]
    exact neg_ne_zero.mpr (ne_of_gt (by simpa [mul_neg] using hp))
  · have hp := Finset.sum_pos (s := Finset.univ)
      (fun i hi => mul_pos (neg_pos.mpr (hu i)) (hv i)) Finset.univ_nonempty
    have hsum : (∑ i, u i * v i) = -∑ i, -(u i * v i) := by
      rw [← Finset.sum_neg_distrib]
      simp
    rw [hsum]
    exact neg_ne_zero.mpr (ne_of_gt (by simpa [mul_neg] using hp))
  · have hp := Finset.sum_pos (s := Finset.univ)
      (fun i hi => mul_pos (neg_pos.mpr (hu i)) (neg_pos.mpr (hv i)))
      Finset.univ_nonempty
    exact ne_of_gt (by simpa using hp)

private theorem euclidean_inner_eq_sum {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ x y = ∑ i, x i * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Pi.star_apply, mul_comm]

private theorem inner_double_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    inner ℝ (M.toEuclideanLin (WithLp.toLp 2 v)) (WithLp.toLp 2 v) =
      ∑ i, ∑ j, M i j * v j * v i := by
  rw [Matrix.toEuclideanLin_toLp, EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
  congr 1 with i
  congr 1 with j
  ring

private theorem lowest_eigenvalue_le_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) [NeZero n] (x : E) :
    hT.eigenvalues hn ⊤ * ‖x‖ ^ 2 ≤ inner ℝ (T x) x := by
  classical
  let B := hT.eigenvectorBasis hn
  have hspan : Submodule.span ℝ (B.toBasis '' (Set.univ : Set (Fin n))) = ⊤ := by
    rw [Set.image_univ]
    exact Module.Basis.span_eq B.toBasis
  have hx : x ∈ Submodule.span ℝ (B.toBasis '' Set.univ) := by
    rw [hspan]
    exact Submodule.mem_top
  exact rayleigh_ge_on_eigenvectorSpan T hT hn (hT.eigenvalues hn ⊤) Set.univ
    (fun i _ => hT.eigenvalues_antitone hn le_top) x hx

private theorem quad_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hdiag : ∀ i, M i i = 0)
    (hneg : ∀ i j, i ≠ j → M i j ≤ 0) (v : ι → ℝ) :
    inner ℝ (M.toEuclideanLin (WithLp.toLp 2 (fun i => |v i|)))
        (WithLp.toLp 2 (fun i => |v i|)) ≤
      inner ℝ (M.toEuclideanLin (WithLp.toLp 2 v)) (WithLp.toLp 2 v) := by
  rw [inner_double_sum, inner_double_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simp [hdiag]
  · have hp : v j * v i ≤ |v j| * |v i| := by
      calc
        v j * v i ≤ |v j * v i| := le_abs_self _
        _ = |v j| * |v i| := abs_mul _ _
    calc
        M i j * |v j| * |v i| = M i j * (|v j| * |v i|) := by ring
        _ ≤ M i j * (v j * v i) := mul_le_mul_of_nonpos_left hp (hneg i j hij)
        _ = M i j * v j * v i := by ring

private theorem quad_abs_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hdiag : ∀ i, M i i = 0)
    (hneg : ∀ i j, i ≠ j → M i j ≤ 0)
    (hneg' : ∀ i j, i ≠ j → M i j < 0) (v : ι → ℝ) (i j : ι)
    (hij : i ≠ j) (hvi : v i < 0) (hvj : 0 < v j) :
    inner ℝ (M.toEuclideanLin (WithLp.toLp 2 (fun k => |v k|)))
        (WithLp.toLp 2 (fun k => |v k|)) <
      inner ℝ (M.toEuclideanLin (WithLp.toLp 2 v)) (WithLp.toLp 2 v) := by
  rw [inner_double_sum, inner_double_sum]
  have hrowle (k : ι) :
      (∑ l, M k l * |v l| * |v k|) ≤ ∑ l, M k l * v l * v k := by
    apply Finset.sum_le_sum
    intro l hl
    by_cases hkl : k = l
    · subst l
      simp [hdiag]
    · have hp : v l * v k ≤ |v l| * |v k| := by
        calc
          v l * v k ≤ |v l * v k| := le_abs_self _
          _ = |v l| * |v k| := abs_mul _ _
      calc
        M k l * |v l| * |v k| = M k l * (|v l| * |v k|) := by ring
        _ ≤ M k l * (v l * v k) := mul_le_mul_of_nonpos_left hp (hneg k l hkl)
        _ = M k l * v l * v k := by ring
  have hrowlt :
      (∑ l, M i l * |v l| * |v i|) < ∑ l, M i l * v l * v i := by
    refine Finset.sum_lt_sum ?_ ⟨j, Finset.mem_univ j, ?_⟩
    intro l hl
    · by_cases hil : i = l
      · subst l
        simp [hdiag]
      · have hp : v l * v i ≤ |v l| * |v i| := by
          calc
            v l * v i ≤ |v l * v i| := le_abs_self _
            _ = |v l| * |v i| := abs_mul _ _
        calc
        M i l * |v l| * |v i| = M i l * (|v l| * |v i|) := by ring
        _ ≤ M i l * (v l * v i) := mul_le_mul_of_nonpos_left hp (hneg i l hil)
        _ = M i l * v l * v i := by ring
    · have hp : v j * v i < |v j| * |v i| := by
        rw [abs_of_pos hvj, abs_of_neg hvi]
        nlinarith
      calc
        M i j * |v j| * |v i| = M i j * (|v j| * |v i|) := by ring
        _ < M i j * (v j * v i) := mul_lt_mul_of_neg_left hp (hneg' i j hij)
        _ = M i j * v j * v i := by ring
  have hout :
      (∑ k, ∑ l, M k l * |v l| * |v k|) <
        ∑ k, ∑ l, M k l * v l * v k := by
    apply Finset.sum_lt_sum (fun k hk => hrowle k) ⟨i, Finset.mem_univ i, hrowlt⟩
  exact hout

private theorem nonneg_eigenvector_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hdiag : ∀ i, M i i = 0)
    (hneg : ∀ i j, i ≠ j → M i j < 0) (lam : ℝ) (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hzn : z ≠ 0) (heig : M.mulVec z = lam • z) :
    ∀ i, 0 < z i := by
  classical
  have hex : ∃ j, z j ≠ 0 := by
    by_contra h
    have hzall : ∀ j, z j = 0 := by
      intro j
      by_contra hj
      exact h ⟨j, hj⟩
    exact hzn (funext hzall)
  obtain ⟨j, hj⟩ := hex
  have hjpos : 0 < z j := lt_of_le_of_ne (hz j) (Ne.symm hj)
  intro i
  by_contra hnot
  have hi0 : z i = 0 := by linarith [hz i]
  have hij : i ≠ j := by
    intro h
    subst j
    exact hj hi0
  have hrow := congrFun heig i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply] at hrow
  have hterm (k : ι) : M i k * z k ≤ 0 := by
    by_cases hik : i = k
    · subst k
      simp [hdiag i]
    · exact mul_nonpos_of_nonpos_of_nonneg (hneg i k hik).le (hz k)
  have hstrict : M i j * z j < 0 := mul_neg_of_neg_of_pos (hneg i j hij) hjpos
  have hsum : (∑ k, M i k * z k) < 0 := by
    have hs := Finset.sum_lt_sum (fun k hk => hterm k)
      ⟨j, Finset.mem_univ j, hstrict⟩
    simpa using hs
  rw [hi0, smul_eq_mul, mul_zero] at hrow
  linarith

private theorem inner_eigen_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (lam : ℝ) (v : ι → ℝ)
    (heig : M.mulVec v = lam • v) :
    inner ℝ (M.toEuclideanLin (WithLp.toLp 2 v)) (WithLp.toLp 2 v) =
      lam * ‖WithLp.toLp 2 v‖ ^ 2 := by
  have hlin : M.toEuclideanLin (WithLp.toLp 2 v) =
      WithLp.toLp 2 (lam • v) := by
    rw [Matrix.toEuclideanLin_apply_piLp_toLp, heig]
  rw [hlin, WithLp.toLp_smul]
  rw [inner_smul_left, real_inner_self_eq_norm_sq]
  simp

private theorem ground_eigenvector_sign {ι : Type*} [Fintype ι] [DecidableEq ι]
    [NeZero (Fintype.card ι)] (M : Matrix ι ι ℝ) (hdiag : ∀ i, M i i = 0)
    (hneg : ∀ i j, i ≠ j → M i j < 0) (hT : M.toEuclideanLin.IsSymmetric)
    (hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι)
    (lam : ℝ) (hlam : lam = hT.eigenvalues hn ⊤) (hln : lam < 0)
    (v : ι → ℝ) (hv : M.mulVec v = lam • v) (hvne : v ≠ 0) :
    (∀ i, 0 < v i) ∨ (∀ i, v i < 0) := by
  classical
  let B := hT.eigenvectorBasis hn
  have hspan : Submodule.span ℝ
      (B.toBasis '' (Set.univ : Set (Fin (Fintype.card ι))) ) = ⊤ := by
    rw [Set.image_univ]
    exact Module.Basis.span_eq B.toBasis
  have hx : WithLp.toLp 2 v ∈
      Submodule.span ℝ (B.toBasis '' (Set.univ : Set (Fin (Fintype.card ι)))) := by
    rw [hspan]
    exact Submodule.mem_top
  have hlow := rayleigh_ge_on_eigenvectorSpan (M.toEuclideanLin) hT hn
      (hT.eigenvalues hn ⊤) Set.univ
      (fun k hk => hT.eigenvalues_antitone hn le_top)
      (WithLp.toLp 2 v) hx
  have hlow' : lam * ‖WithLp.toLp 2 v‖ ^ 2 ≤
      inner ℝ (M.toEuclideanLin (WithLp.toLp 2 v)) (WithLp.toLp 2 v) := by
    simpa [hlam] using hlow
  have hQv := inner_eigen_eq M lam v hv
  have hxAbs : WithLp.toLp 2 (fun i => |v i|) ∈
      Submodule.span ℝ (B.toBasis '' (Set.univ : Set (Fin (Fintype.card ι)))) := by
    rw [hspan]
    exact Submodule.mem_top
  have hlowAbs := rayleigh_ge_on_eigenvectorSpan (M.toEuclideanLin) hT hn
    (hT.eigenvalues hn ⊤) Set.univ
    (fun k hk => hT.eigenvalues_antitone hn le_top)
    (WithLp.toLp 2 (fun i => |v i|)) hxAbs
  have hlowAbs' : lam * ‖WithLp.toLp 2 (fun i => |v i|)‖ ^ 2 ≤
      inner ℝ (M.toEuclideanLin (WithLp.toLp 2 (fun i => |v i|)))
        (WithLp.toLp 2 (fun i => |v i|)) := by
    simpa [hlam] using hlowAbs
  have habsNorm : ‖WithLp.toLp 2 (fun i => |v i|)‖ =
      ‖WithLp.toLp 2 v‖ := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [Real.norm_eq_abs, sq_abs]
  have hnomix : ¬ ∃ i j, v i < 0 ∧ 0 < v j := by
    intro hmix
    obtain ⟨i, j, hi, hj⟩ := hmix
    have hneq : i ≠ j := by
      intro h
      subst j
      linarith
    have hQlt := quad_abs_lt M hdiag
      (fun i j hij => (hneg i j hij).le) hneg v i j hneq hi hj
    rw [hQv] at hQlt
    rw [habsNorm] at hlowAbs'
    linarith [hlowAbs']
  by_cases hpos : ∃ i, 0 < v i
  · obtain ⟨j, hj⟩ := hpos
    have hnonneg : ∀ i, 0 ≤ v i := by
      intro i
      by_contra hi
      have hvi : v i < 0 := lt_of_not_ge hi
      exact hnomix ⟨i, j, hvi, hj⟩
    exact Or.inl (nonneg_eigenvector_pos M hdiag hneg lam v hnonneg hvne hv)
  · have hnonpos : ∀ i, v i ≤ 0 := by
      intro i
      exact le_of_not_gt (fun hi => hpos ⟨i, hi⟩)
    have hminus : M.mulVec (-v) = lam • (-v) := by
      rw [Matrix.mulVec_neg, hv, smul_neg]
    have hminusne : -v ≠ 0 := by simpa using hvne
    have hnonneg : ∀ i, 0 ≤ (-v) i := by
      intro i
      simpa using neg_nonneg.mpr (hnonpos i)
    have hstrict := nonneg_eigenvector_pos M hdiag hneg lam (-v) hnonneg hminusne hminus
    exact Or.inr (by intro i; simpa using hstrict i)



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
  let A := oneWellConstants hd s hs c hc R hR
    (Metric.ball (0 : Eucl d) R) Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hR) Set.Subset.rfl φ hφ
  let lam : ℝ → ℕ → ℝ := fun L k =>
    eigenvalue A.c A.kappa (twoWellDomain (Metric.ball 0 R) e L) k
  have htwo := twoWell_main hd s hs c hc R hR
    (Metric.ball (0 : Eucl d) R) Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hR) Set.Subset.rfl φ hφ e he
  have htwo' : A.twoWellStatement lam ∧
      ∀ L : ℝ, A.L0 ≤ L →
        eigenvalue A.c A.kappa (twoWellDomain (Metric.ball 0 R) e L) 0 <
            eigenvalue A.c A.kappa (twoWellDomain (Metric.ball 0 R) e L) 1 ∧
          eigenvalue A.c A.kappa (twoWellDomain (Metric.ball 0 R) e L) 1 <
            eigenvalue A.c A.kappa (twoWellDomain (Metric.ball 0 R) e L) 2 := by
    simpa [A, lam, oneWellConstants] using htwo
  have hpt : ∀ L : ℝ, A.L0 ≤ L →
      |lam L 1 - (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))| ≤
        A.remainder L := by
    intro L hL
    have hh := (htwo'.1.1 L hL).2.1
    simpa [lam] using hh
  have hbudget : Filter.Tendsto
      (fun L : ℝ => L ^ A.kappa * A.remainder L)
      Filter.atTop (nhds 0) := by
    simpa only [← multiTwo_remainder_aux A e he] using
      (multiWellRescaledError_tendsto_zero A (twoWellSites e))
  let err : ℝ → ℝ := fun L =>
    L ^ A.kappa * (lam L 1 - A.mu1) - A.c * A.phiMass ^ 2
  have hL0pos : 0 < A.L0 :=
    lt_of_lt_of_le (mul_pos (by norm_num) A.hR) (le_max_left _ _)
  have hbound : ∀ᶠ L : ℝ in Filter.atTop, |err L| ≤ L ^ A.kappa * A.remainder L := by
    filter_upwards [Filter.eventually_ge_atTop A.L0] with L hL
    have hLp : 0 < L := lt_of_lt_of_le hL0pos hL
    have hpow : L ^ A.kappa * L ^ (-A.kappa) = 1 := by
      rw [← Real.rpow_add hLp, add_neg_cancel]
      exact Real.rpow_zero L
    have hcalc : err L =
        L ^ A.kappa *
          (lam L 1 - (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))) := by
      dsimp [err]
      calc
        L ^ A.kappa * (lam L 1 - A.mu1) - A.c * A.phiMass ^ 2
            = L ^ A.kappa * (lam L 1 - A.mu1) -
                (L ^ A.kappa * L ^ (-A.kappa)) * (A.c * A.phiMass ^ 2) := by
                  rw [hpow]
                  ring
        _ = L ^ A.kappa *
              (lam L 1 - (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa))) := by ring
    have hpowNonneg : 0 ≤ L ^ A.kappa := Real.rpow_nonneg hLp.le _
    have habs :
        |L ^ A.kappa *
          (lam L 1 - (A.mu1 + A.c * A.phiMass ^ 2 * L ^ (-A.kappa)))| ≤
            L ^ A.kappa * A.remainder L := by
      rw [abs_mul, abs_of_nonneg hpowNonneg]
      exact mul_le_mul_of_nonneg_left (hpt L hL) hpowNonneg
    rw [hcalc]
    exact habs
  have habs : Filter.Tendsto (fun L : ℝ => |err L|)
      Filter.atTop (nhds 0) :=
    squeeze_zero'
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      hbound hbudget
  have herr : Filter.Tendsto err Filter.atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero err).2 habs
  have hcst : Filter.Tendsto (fun _ : ℝ => A.c * A.phiMass ^ 2)
      Filter.atTop (nhds (A.c * A.phiMass ^ 2)) := tendsto_const_nhds
  have hlim : Filter.Tendsto
      (fun L : ℝ => L ^ A.kappa * (lam L 1 - A.mu1))
      Filter.atTop (nhds (A.c * A.phiMass ^ 2)) := by
    have hadd : Filter.Tendsto
        (fun L : ℝ => A.c * A.phiMass ^ 2 + err L)
        Filter.atTop (nhds (A.c * A.phiMass ^ 2)) := by
      simpa using hcst.add herr
    have hfun : (fun L : ℝ => L ^ A.kappa * (lam L 1 - A.mu1)) =
        (fun L => A.c * A.phiMass ^ 2 + err L) := by
      funext L
      simp [err]
    rw [hfun]
    exact hadd
  simpa [A, lam, oneWellConstants] using hlim

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
  let μ₁ : ℝ := eigenvalue c κ D 0
  let m : ℝ := ∫ x, φ x
  let r : ℝ := ‖a 0 - a 1‖
  let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
  let w : ℝ := A.c * A.phiMass ^ 2 * r ^ (-A.kappa)
  let lam : ℝ → ℕ → ℝ := fun L k =>
    eigenvalue A.c A.kappa (multiWellDomain D a L) k
  let theta : Fin 2 → ℝ := effectiveInteractionTheta a A.c A.phiMass A.kappa
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hmass : 0 < m := hφ.mass_pos hd s hs c hc R D hDo hDne hDR
  have hsig (p : ℝ) : sigmaKappa a p = r ^ (-p) := by
    simpa [r] using sigmaKappa_fin_two_eq_dist a p ha
  have hw : 0 < w := by
    dsimp [w, A]
    exact mul_pos (mul_pos hc (sq_pos_of_pos hmass)) (Real.rpow_pos_of_pos hr _)
  let M : Matrix (Fin 2) (Fin 2) ℝ :=
    effectiveInteractionMatrix a A.c A.phiMass A.kappa
  have hM : M.IsHermitian := by
    exact effectiveInteractionMatrix_isHermitian a A.c A.phiMass A.kappa
  have hM00 : M 0 0 = 0 := by simp [M]
  have hM11 : M 1 1 = 0 := by simp [M]
  have hM01 : M 0 1 = -w := by
    simp only [M, effectiveInteractionMatrix_apply]
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    rw [if_neg h01]
    dsimp [w, r, A, oneWellConstants, κ, m]
    ring
  have hpair := eigenvalues₀_fin_two_of_zero_diag M hM hM00 hM11
  have htheta0 : theta 0 = -w := by
    change hM.eigenvalues₀ (Fin.rev 0) = -w
    rw [hpair.1, hM01, abs_neg, abs_of_pos hw]
  have htheta1 : theta 1 = w := by
    change hM.eigenvalues₀ (Fin.rev 1) = w
    rw [hpair.2, hM01, abs_neg, abs_of_pos hw]
  have ha' : ∀ i j : Fin 2, i ≠ j → a i ≠ a j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact ha
    · exact ha.symm
    · exact False.elim (hij rfl)
  have hmain := multiWell_main hd s hs c hc R hR D hDo hDne hDR φ hφ a ha'
  have hstmt : multiWellStatement A a theta lam := by
    simpa [A, theta, lam] using hmain
  have hcond := multiWellCondition_eventually A a ha'
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.1 hcond
  let U : ℝ := A.c * A.C * A.phiMass ^ 2 * r ^ (-A.kappa - 2)
  let G : ℝ := A.c * 2 ^ A.kappa * A.volumeD * r ^ (-A.kappa)
  let V : ℝ := 2 * G ^ 2 / A.gap
  let C : ℝ := U + V
  have hε (L : ℝ) :
      multiWellEpsilon A a L = U * L ^ (-A.kappa - 2) := by
    rw [multiWellEpsilon, hsig (A.kappa + 2)]
    have hexp : -(A.kappa + 2) = -A.kappa - 2 := by ring
    dsimp [U]
    rw [hexp]
  have hγ (L : ℝ) :
      multiWellGamma A a L = G * L ^ (-A.kappa) := by
    rw [multiWellGamma, hsig A.kappa]
  have hpow (L : ℝ) (hL : 0 ≤ L) :
      (L ^ (-A.kappa)) ^ 2 = L ^ (-2 * A.kappa) := by
    rw [← Real.rpow_mul_natCast hL (-A.kappa) 2]
    congr 1
    ring
  have hU : 0 ≤ U := by
    dsimp [U]
    exact mul_nonneg (mul_nonneg (mul_nonneg A.hc.le A.hC.le)
      (sq_nonneg A.phiMass)) (Real.rpow_nonneg hr.le _)
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (mul_nonneg (mul_nonneg A.hc.le
      (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)) A.hvolumeD.le)
      (Real.rpow_nonneg hr.le _)
  have hV : 0 ≤ V := by
    dsimp [V]
    have hgap : 0 < A.gap := by simpa [TwoWellConstants.gap] using A.hgap
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg G)) hgap.le
  have herr (L : ℝ) (hL : 0 < L) :
      multiWellEpsilon A a L + 2 * multiWellGamma A a L ^ 2 / A.gap ≤
        C * (L ^ (-A.kappa - 2) + L ^ (-2 * A.kappa)) := by
    have hpowL : 0 ≤ L ^ (-A.kappa - 2) := Real.rpow_nonneg hL.le _
    have hpowG : 0 ≤ L ^ (-2 * A.kappa) := Real.rpow_nonneg hL.le _
    rw [hε, hγ, mul_pow, hpow L hL.le]
    calc
      _ = U * L ^ (-A.kappa - 2) + V * L ^ (-2 * A.kappa) := by
        dsimp [U, V]
        ring
      _ ≤ C * (L ^ (-A.kappa - 2) + L ^ (-2 * A.kappa)) := by
        change U * L ^ (-A.kappa - 2) + V * L ^ (-2 * A.kappa) ≤
          (U + V) * (L ^ (-A.kappa - 2) + L ^ (-2 * A.kappa))
        nlinarith [mul_nonneg hU hpowG, mul_nonneg hV hpowL]
  have hmodel0 (L : ℝ) :
      A.mu1 + L ^ (-A.kappa) * theta 0 =
        μ₁ - c * m ^ 2 * r ^ (-κ) * L ^ (-κ) := by
    rw [htheta0]
    dsimp [w, μ₁, A, oneWellConstants, κ, m]
    ring
  have hmodel1 (L : ℝ) :
      A.mu1 + L ^ (-A.kappa) * theta 1 =
        μ₁ + c * m ^ 2 * r ^ (-κ) * L ^ (-κ) := by
    rw [htheta1]
    dsimp [w, μ₁, A, oneWellConstants, κ, m]
    ring
  have hquant (L : ℝ) (hL : L₁ ≤ L) :
      |lam L 0 - (μ₁ - c * m ^ 2 * r ^ (-κ) * L ^ (-κ))| ≤
          C * (L ^ (-κ - 2) + L ^ (-2 * κ)) ∧
        |lam L 1 - (μ₁ + c * m ^ 2 * r ^ (-κ) * L ^ (-κ))| ≤
          C * (L ^ (-κ - 2) + L ^ (-2 * κ)) := by
    have hcnd := hL₁ L hL
    have hcon := hstmt.1 L hcnd.1 hcnd.2.1 hcnd.2.2
    have h0 := hcon.1 (0 : Fin 2)
    have h1 := hcon.1 (1 : Fin 2)
    rw [hmodel0 L] at h0
    rw [hmodel1 L] at h1
    exact ⟨h0.trans (herr L hcnd.1), h1.trans (herr L hcnd.1)⟩
  have hgaplim :
      Filter.Tendsto (fun L : ℝ => L ^ A.kappa * (lam L 1 - lam L 0))
        Filter.atTop (nhds (2 * w)) := by
    let k0 : Fin 2 := ⟨0, by decide⟩
    let k1 : Fin 2 := ⟨1, by decide⟩
    have hlim := (hstmt.2 k1).sub (hstmt.2 k0)
    have hfun :
        (fun L : ℝ => L ^ A.kappa * (lam L 1 - lam L 0)) =
          (fun L => L ^ A.kappa * (lam L 1 - A.mu1) -
            L ^ A.kappa * (lam L 0 - A.mu1)) := by
      funext L
      ring
    rw [hfun]
    have hlimVal : theta k1 - theta k0 = 2 * w := by
      simp [k0, k1, htheta0, htheta1]
      ring
    rw [← hlimVal]
    exact hlim
  refine ⟨?_, ?_⟩
  · refine ⟨C, L₁, ?_⟩
    intro L hL
    simpa [κ, μ₁, m, r, lam, A, oneWellConstants] using hquant L hL
  · have hval : 2 * w = 2 * c * m ^ 2 * r ^ (-κ) := by
      dsimp [w, A, oneWellConstants, κ, m]
      ring
    have hfinal :
        Filter.Tendsto (fun L : ℝ => L ^ A.kappa * (lam L 1 - lam L 0))
          Filter.atTop (nhds (2 * c * m ^ 2 * r ^ (-κ))) := by
      rw [← hval]
      exact hgaplim
    simpa [κ, m, r, lam, A, oneWellConstants] using hfinal

/-- **Paper Corollary 4.6** (`cor:multi-two`): for `a₁ = -e/2`, `a₂ = e/2`
the multi-well error `ε_L + 2γ_L²/g` equals the two-well remainder. -/
theorem multiTwo_remainder (A : TwoWellConstants) (e : Eucl d) (he : ‖e‖ = 1) (L : ℝ) :
    multiWellEpsilon A (twoWellSites e) L +
        2 * multiWellGamma A (twoWellSites e) L ^ 2 / A.gap =
      A.remainder L := by
  exact multiTwo_remainder_aux A e he L

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
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let n : ℕ := Fintype.card ι
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  let theta : Fin n → ℝ := effectiveInteractionTheta a c m κ
  let M : Matrix ι ι ℝ := effectiveInteractionMatrix a c m κ
  have hM : M.IsHermitian := effectiveInteractionMatrix_isHermitian a c m κ
  have hMform (i j : ι) :
      M i j = if i = j then 0 else -c * m ^ 2 * ‖a i - a j‖ ^ (-κ) := by
    simp [M, effectiveInteractionMatrix_apply]
  have hdiag (i : ι) : M i i = 0 := by
    simp [hMform]
  have hneg' : ∀ i j, i ≠ j → M i j < 0 := by
    intro i j hij
    have hnorm : 0 < ‖a i - a j‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (ha i j hij))
    have hpow : 0 < ‖a i - a j‖ ^ (-κ) :=
      Real.rpow_pos_of_pos hnorm _
    have hprod : 0 < c * m ^ 2 * ‖a i - a j‖ ^ (-κ) :=
      mul_pos (mul_pos hc (sq_pos_of_pos hm)) hpow
    rw [hMform i j, if_neg hij]
    nlinarith
  have hneg : ∀ i j, i ≠ j → M i j ≤ 0 :=
    fun i j hij => (hneg' i j hij).le
  let T := M.toEuclideanLin
  have hT : T.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  have hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = n := by
    simp [n]
  let e : ι ≃ Fin n :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  let k0 : Fin n := ⟨0, by omega⟩
  let k1 : Fin n := ⟨1, by omega⟩
  let kLast : Fin n := ⟨n - 1, by omega⟩
  have hk01 : k0 ≤ k1 := by
    apply Fin.le_iff_val_le_val.mpr
    simp [k0, k1]
  have thetaMono : Monotone theta := by
    simpa [theta] using effectiveInteractionTheta_monotone a c m κ
  have hqneq : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
    intro hh
    have hv := congrArg Fin.val hh
    norm_num at hv
  let site0 : ι := e.symm (⟨0, by omega⟩ : Fin n)
  let site1 : ι := e.symm (⟨1, by omega⟩ : Fin n)
  have hsite : site0 ≠ site1 := by
    intro hh
    apply hqneq
    have heq := congrArg e hh
    change e (e.symm (⟨0, by omega⟩ : Fin n)) =
      e (e.symm (⟨1, by omega⟩ : Fin n)) at heq
    simpa only [Equiv.apply_symm_apply] using heq
  have hExt := effectiveInteractionTheta_extreme_signs_of_distinct
    a c m κ site0 site1 hsite (ha site0 site1 hsite) hc.ne' hm.ne'
  have hk0bot : k0 = ⊥ := by
    dsimp [k0]
    exact (Fin.bot_eq_zero n).symm
  have htheta0 : theta k0 < 0 := by
    have hh : theta ⊥ < 0 := by simpa [theta] using hExt.1
    rw [hk0bot]
    exact hh
  have htop : kLast = ⊤ := by
    apply Fin.ext
    simp [kLast, n]
  have hthetaLast : 0 < theta kLast := by
    have hh : 0 < theta ⊤ := by simpa [theta] using hExt.2
    rw [htop]
    exact hh
  let lam : ℝ := hM.eigenvalues₀ (⊤ : Fin n)
  have hrev : Fin.rev k0 = ⊤ := by
    simpa [k0] using (Fin.rev_zero_eq_top n)
  have htheta0lam : theta k0 = lam := by
    change hM.eigenvalues₀ (Fin.rev k0) = hM.eigenvalues₀ ⊤
    rw [hrev]
  have hlamneg : lam < 0 := by
    rw [← htheta0lam]
    exact htheta0
  have hthetaK : ∀ k : Fin n, theta k = hM.eigenvalues₀ (Fin.rev k) := by
    intro k
    rfl
  let zfun : Fin n → ι → ℝ := fun j =>
    ⇑(hM.eigenvectorBasis (e.symm j))
  have heigVec (j : Fin n) :
      M.mulVec (zfun j) = (hM.eigenvalues₀ j) • zfun j := by
    have heig := hM.mulVec_eigenvectorBasis (e.symm j)
    have heval : hM.eigenvalues (e.symm j) = hM.eigenvalues₀ j := by
      simp [Matrix.IsHermitian.eigenvalues, e]
    simpa [zfun, heval] using heig
  have hzne (j : Fin n) : zfun j ≠ 0 := by
    intro hz
    apply hM.eigenvectorBasis.orthonormal.ne_zero (e.symm j)
    ext i
    simpa [zfun] using congrFun hz i
  have hLam : lam = hT.eigenvalues hn ⊤ := by
    rfl
  let z0 : ι → ℝ := zfun (⊤ : Fin n)
  have hz0eig : M.mulVec z0 = lam • z0 := by
    simpa [z0, lam] using heigVec ⊤
  have hsign0 := ground_eigenvector_sign M hdiag hneg' hT hn lam hLam hlamneg
    z0 hz0eig (hzne ⊤)
  have hidx0 : theta k0 = hM.eigenvalues₀ (⊤ : Fin n) := by
    simpa [lam] using htheta0lam
  have htheta1eig : theta k1 = hM.eigenvalues₀ (Fin.rev k1) := by
    exact hthetaK k1
  have hsimple : theta k0 < theta k1 := by
    have hle := thetaMono hk01
    by_contra hnot
    have hback : theta k1 ≤ theta k0 := le_of_not_gt hnot
    have heq : theta k0 = theta k1 := le_antisymm hle hback
    let j0 : Fin n := ⊤
    let j1 : Fin n := Fin.rev k1
    have heqEig : hM.eigenvalues₀ j1 = lam := by
      calc
        hM.eigenvalues₀ j1 = theta k1 := htheta1eig.symm
        _ = theta k0 := heq.symm
        _ = lam := htheta0lam
    let z1 : ι → ℝ := zfun j1
    have hz1eig : M.mulVec z1 = lam • z1 := by
      simpa [z1, j1, heqEig] using heigVec j1
    have hsign1 := ground_eigenvector_sign M hdiag hneg' hT hn lam hLam hlamneg
      z1 hz1eig (hzne j1)
    have hj01 : j0 ≠ j1 := by
      intro hh
      have hh' : k0 = k1 := by
        apply Fin.rev_injective
        calc
          Fin.rev k0 = j0 := by
            simpa [j0] using hrev
          _ = j1 := hh
          _ = Fin.rev k1 := rfl
      have hval := congrArg Fin.val hh'
      simp [k0, k1] at hval
    have hidx : e.symm j0 ≠ e.symm j1 := by
      intro hh
      apply hj01
      have := congrArg e hh
      simpa using this
    have horth :
        inner ℝ (hM.eigenvectorBasis (e.symm j0))
          (hM.eigenvectorBasis (e.symm j1)) = 0 :=
      Orthonormal.inner_eq_zero hM.eigenvectorBasis.orthonormal hidx
    have horth' :
        inner ℝ (WithLp.toLp 2 (zfun j0)) (WithLp.toLp 2 (zfun j1)) = 0 := by
      simpa [zfun] using horth
    rw [euclidean_inner_eq_sum] at horth'
    exact (uniform_sign_dot_ne (zfun j0) (zfun j1) hsign0 hsign1) horth'
  have hLastIndex :
      (⟨Fintype.card ι - 1, by omega⟩ : Fin (Fintype.card ι)) = kLast := by
    apply Fin.ext
    simp [kLast, n]
  refine ⟨?_, hsimple, ?_, ?_⟩
  · change theta k0 < 0
    exact htheta0
  · change 0 < theta kLast
    exact hthetaLast
  · rcases hsign0 with hzpos | hzneg
    · refine ⟨z0, hzpos, ?_⟩
      change M.mulVec z0 = theta k0 • z0
      rw [htheta0lam]
      exact hz0eig
    · refine ⟨-z0, ?_, ?_⟩
      · intro i
        exact neg_pos.mpr (hzneg i)
      · have hv : M.mulVec (-z0) = lam • (-z0) := by
          rw [Matrix.mulVec_neg, hz0eig, smul_neg]
        change M.mulVec (-z0) = theta k0 • (-z0)
        rw [htheta0lam]
        exact hv

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
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let κ : ℝ := (d : ℝ) + 2 * s
  let μ₁ : ℝ := eigenvalue c κ D 0
  let m : ℝ := ∫ x, φ x
  let A := oneWellConstants hd s hs c hc R hR D hDo hDne hDR φ hφ
  let lambda : ℝ → ℕ → ℝ := fun L k =>
    eigenvalue A.c A.kappa (multiWellDomain D a L) k
  let theta : Fin (Fintype.card ι) → ℝ :=
    effectiveInteractionTheta a A.c A.phiMass A.kappa
  have hmain := multiWell_main hd s hs c hc R hR D hDo hDne hDR φ hφ a ha
  have hstmt : multiWellStatement A a theta lambda := by
    simpa [A, theta, lambda] using hmain
  have hm : 0 < m := hφ.mass_pos hd s hs c hc R D hDo hDne hDR
  have hground := collectiveGround_matrix hN a ha c m κ hc hm
  have htheta0 : theta ⟨0, by omega⟩ < 0 := by
    simpa [theta, A, oneWellConstants] using hground.1
  have hthetaN :
      0 < theta ⟨Fintype.card ι - 1, by omega⟩ := by
    simpa [theta, A, oneWellConstants] using hground.2.2.1
  have hSimple : ∀ L : ℝ, 0 < L →
      eigenvalue c κ (multiWellDomain D a L) 0 <
        eigenvalue c κ (multiWellDomain D a L) 1 := by
    intro L hL
    let B : ℝ := ∑ j : ι, ‖a j‖
    have hB : 0 ≤ B := by
      dsimp [B]
      exact Finset.sum_nonneg fun j hj => norm_nonneg _
    have hAj (j : ι) : ‖a j‖ ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (fun i hi => norm_nonneg (a i))
        (Finset.mem_univ j)
    let R' : ℝ := R + |L| * B + 1
    have hR' : 0 < R' := by
      dsimp [R']
      have := mul_nonneg (abs_nonneg L) hB
      linarith
    have hopen : IsOpen (multiWellDomain D a L) := by
      unfold multiWellDomain
      rw [show {x : Eucl d | ∃ j : ι, x - L • a j ∈ D} =
          ⋃ j : ι, {x : Eucl d | x - L • a j ∈ D} by
        ext x
        simp]
      exact isOpen_iUnion fun j =>
        hDo.preimage (continuous_id.sub continuous_const)
    have hne : (multiWellDomain D a L).Nonempty := by
      obtain ⟨y, hy⟩ := hDne
      let j : ι := Classical.choice ‹Nonempty ι›
      refine ⟨y + L • a j, ?_⟩
      change ∃ j', (y + L • a j) - L • a j' ∈ D
      refine ⟨j, ?_⟩
      convert hy using 1 <;> abel
    have hsub : multiWellDomain D a L ⊆ Metric.ball 0 R' := by
      intro x hx
      obtain ⟨j, hxj⟩ := hx
      have hball : ‖x - L • a j‖ < R := by
        have := hDR hxj
        simpa [Metric.mem_ball, dist_zero_right] using this
      have hnorm : ‖L • a j‖ = |L| * ‖a j‖ := by
        simpa [Real.norm_eq_abs] using (norm_smul L (a j))
      rw [Metric.mem_ball, dist_zero_right]
      calc
        ‖x‖ = ‖(x - L • a j) + L • a j‖ := by congr 1 <;> abel
        _ ≤ ‖x - L • a j‖ + ‖L • a j‖ := norm_add_le _ _
        _ < R' := by
          rw [hnorm]
          dsimp [R']
          have hmul := mul_le_mul_of_nonneg_left (hAj j) (abs_nonneg L)
          nlinarith
    have h := eigenvalue_zero_lt_one hd s hs c hc R'
      (multiWellDomain D a L) hopen hne hsub
    simpa [κ] using h
  let k0 : Fin (Fintype.card ι) := ⟨0, by omega⟩
  let kN : Fin (Fintype.card ι) :=
    ⟨Fintype.card ι - 1, by omega⟩
  have hnegLim := hstmt.2 k0
  have hposLim := hstmt.2 kN
  have heventNeg :
      ∀ᶠ L : ℝ in Filter.atTop,
        L ^ A.kappa * (lambda L 0 - A.mu1) < 0 := by
    have hh := hnegLim.eventually (isOpen_Iio.mem_nhds (by simpa [k0] using htheta0))
    filter_upwards [hh] with L hL
    simpa [k0] using hL
  have heventPos :
      ∀ᶠ L : ℝ in Filter.atTop,
        0 < L ^ A.kappa * (lambda L (Fintype.card ι - 1) - A.mu1) := by
    have hh := hposLim.eventually (isOpen_Ioi.mem_nhds (by simpa [kN] using hthetaN))
    filter_upwards [hh] with L hL
    simpa [kN] using hL
  have hLpos : ∀ᶠ L : ℝ in Filter.atTop, 0 < L :=
    Filter.eventually_gt_atTop 0
  have hlarge :
      ∀ᶠ L : ℝ in Filter.atTop,
        eigenvalue c κ (multiWellDomain D a L) 0 < μ₁ ∧
          μ₁ < eigenvalue c κ (multiWellDomain D a L) (Fintype.card ι - 1) := by
    filter_upwards [heventNeg, heventPos, hLpos] with L hnegL hposL hL
    have hpow : 0 < L ^ A.kappa := Real.rpow_pos_of_pos hL _
    have hdiff0 :
        lambda L 0 - A.mu1 < 0 := by
      by_contra hnot
      have hnonneg : 0 ≤ lambda L 0 - A.mu1 := le_of_not_gt hnot
      have hmul := mul_nonneg hpow.le hnonneg
      linarith
    have hdiffN :
        0 < lambda L (Fintype.card ι - 1) - A.mu1 := by
      by_contra hnot
      have hnonpos : lambda L (Fintype.card ι - 1) - A.mu1 ≤ 0 :=
        le_of_not_gt hnot
      have hmul := mul_nonpos_of_nonneg_of_nonpos hpow.le hnonpos
      linarith
    have hcmp : lambda L 0 < A.mu1 ∧
        A.mu1 < lambda L (Fintype.card ι - 1) := by
      constructor
      · linarith [hdiff0]
      · linarith [hdiffN]
    simpa [lambda, μ₁, A, oneWellConstants, κ] using hcmp
  refine ⟨?_, ?_⟩
  · intro L hL
    exact hSimple L hL
  · simpa [κ, μ₁, lambda, A, oneWellConstants] using hlarge

/-- **Paper Corollary 4.8** (`cor:simplex`): equidistant sites.  Then
`N ≤ d + 1`, `θ₁ = -(N-1) w` and `θ₂ = ⋯ = θ_N = w` with `w = c m₁² r^{-κ}`. -/
theorem simplex_cluster {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hN : 1 ≤ Fintype.card ι) (a : ι → Eucl d) (r : ℝ) (hr : 0 < r)
    (hdist : ∀ i j : ι, i ≠ j → ‖a i - a j‖ = r) (c m κ : ℝ) (hc : 0 ≤ c) :
    let w := c * m ^ 2 * r ^ (-κ)
    Fintype.card ι ≤ d + 1 ∧
      effectiveInteractionTheta a c m κ ⟨0, by omega⟩ = -((Fintype.card ι - 1 : ℝ) * w) ∧
      ∀ k : Fin (Fintype.card ι), k.val ≠ 0 → effectiveInteractionTheta a c m κ k = w := by
  classical
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let n : ℕ := Fintype.card ι
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  let w : ℝ := c * m ^ 2 * r ^ (-κ)
  let theta : Fin n → ℝ := effectiveInteractionTheta a c m κ
  have hcard : Fintype.card ι ≤ d + 1 := by
    have hAI := equidistant_affineIndependent a r hr hdist
    have hcardAI := AffineIndependent.card_le_finrank_succ hAI
    have hspan :
        Module.finrank ℝ (vectorSpan ℝ (Set.range a)) ≤
          Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) :=
      Submodule.finrank_le _
    calc
      Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range a)) + 1 := hcardAI
      _ ≤ d + 1 := by simpa using Nat.add_le_add_right hspan 1
  have ha : ∀ i j : ι, i ≠ j → a i ≠ a j := by
    intro i j hij heq
    have hh := hdist i j hij
    rw [heq, sub_self, norm_zero] at hh
    linarith
  have hw : 0 ≤ w := by
    dsimp [w]
    exact mul_nonneg (mul_nonneg hc (sq_nonneg m))
      (Real.rpow_nonneg hr.le _)
  let M : Matrix ι ι ℝ := effectiveInteractionMatrix a c m κ
  have hM : M.IsHermitian := effectiveInteractionMatrix_isHermitian a c m κ
  have hMform (i j : ι) : M i j = if i = j then 0 else -w := by
    by_cases hij : i = j
    · subst j
      simp [M]
    · simp only [M, effectiveInteractionMatrix_apply, if_neg hij]
      rw [hdist i j hij]
      dsimp [w]
      ring
  let e : ι ≃ Fin n :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  let zfun : Fin n → ι → ℝ := fun j =>
    ⇑(hM.eigenvectorBasis (e.symm j))
  have heigVec (j : Fin n) :
      M.mulVec (zfun j) = (hM.eigenvalues₀ j) • zfun j := by
    have heig := hM.mulVec_eigenvectorBasis (e.symm j)
    have heval : hM.eigenvalues (e.symm j) = hM.eigenvalues₀ j := by
      simp [Matrix.IsHermitian.eigenvalues, e]
    simpa [zfun, heval] using heig
  have hzne (j : Fin n) : zfun j ≠ 0 := by
    intro hz
    apply hM.eigenvectorBasis.orthonormal.ne_zero (e.symm j)
    ext i
    simpa [zfun] using congrFun hz i
  have hclass (j : Fin n) :
      hM.eigenvalues₀ j = w ∨
        hM.eigenvalues₀ j = -(((n : ℝ) - 1) * w) := by
    have hc := const_offdiag_eigen_class M w (hM.eigenvalues₀ j)
      hMform (zfun j) (hzne j) (heigVec j)
    rcases hc with h | h
    · exact Or.inl h
    · exact Or.inr (by
        calc
          hM.eigenvalues₀ j = -(((Fintype.card ι : ℝ) - 1) * w) := h.1
          _ = -(((n : ℝ) - 1) * w) := by simp [n])
  let k0 : Fin n := ⟨0, by omega⟩
  have hrev0 : Fin.rev k0 = ⊤ := by
    simpa [k0] using (Fin.rev_zero_eq_top n)
  have hthetaEig (k : Fin n) :
      theta k = hM.eigenvalues₀ (Fin.rev k) := rfl
  have hsum : (∑ j : Fin n, theta j) = 0 := by
    simpa [theta, n] using effectiveInteractionTheta_sum_eq_zero a c m κ
  have htheta0 :
      theta k0 = -(((n : ℝ) - 1) * w) := by
    by_cases hwzero : w = 0
    · rcases hclass (Fin.rev k0) with heqw | heqneg
      · calc
          theta k0 = hM.eigenvalues₀ (Fin.rev k0) := hthetaEig k0
          _ = w := heqw
          _ = -(((n : ℝ) - 1) * w) := by simp [hwzero]
      · calc
          theta k0 = hM.eigenvalues₀ (Fin.rev k0) := hthetaEig k0
          _ = -(((n : ℝ) - 1) * w) := heqneg
    · by_cases hn1 : n = 1
      · have hjeq (j : Fin n) : j = k0 := by
          apply Fin.ext
          have hjlt : j.val < 1 := by simpa [hn1] using j.isLt
          have hj0 : j.val = 0 := by omega
          simpa [k0] using hj0
        have hsumConst : (∑ j : Fin n, theta j) = theta k0 := by
          calc
            _ = ∑ j : Fin n, theta k0 := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hjeq j]
            _ = theta k0 := by simp [hn1]
        have hzero : theta k0 = 0 := by
          calc
            theta k0 = ∑ j : Fin n, theta j := hsumConst.symm
            _ = 0 := hsum
        rw [hzero]
        have hfac : (n : ℝ) - 1 = 0 := by norm_num [hn1]
        rw [hfac]
        ring
      · have hn2 : 2 ≤ n := by omega
        have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hwzero)
        have hcne : c ≠ 0 := by
          intro hc0
          have hzero : w = 0 := by simp [w, hc0]
          exact hwzero hzero
        have hmne : m ≠ 0 := by
          intro hm0
          have hzero : w = 0 := by simp [w, hm0]
          exact hwzero hzero
        have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcne)
        let eqv : ι ≃ Fin n :=
          (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
        have hqneq : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
          intro hh
          have hv := congrArg Fin.val hh
          norm_num at hv
        let site0 : ι := eqv.symm (⟨0, by omega⟩ : Fin n)
        let site1 : ι := eqv.symm (⟨1, by omega⟩ : Fin n)
        have hsite : site0 ≠ site1 := by
          intro hh
          apply hqneq
          have heq := congrArg eqv hh
          change eqv (eqv.symm (⟨0, by omega⟩ : Fin n)) =
            eqv (eqv.symm (⟨1, by omega⟩ : Fin n)) at heq
          simpa only [Equiv.apply_symm_apply] using heq
        have hExt := effectiveInteractionTheta_extreme_signs_of_distinct
          a c m κ site0 site1 hsite (ha site0 site1 hsite) hcne hmne
        have hk0bot : k0 = ⊥ := by
          dsimp [k0]
          exact (Fin.bot_eq_zero n).symm
        have htheta0neg : theta k0 < 0 := by
          have hh : theta ⊥ < 0 := by simpa [theta] using hExt.1
          rw [hk0bot]
          exact hh
        rcases hclass (Fin.rev k0) with heqw | heqneg
        · have htheta0w : theta k0 = w := (hthetaEig k0).trans heqw
          linarith
        · calc
            theta k0 = hM.eigenvalues₀ (Fin.rev k0) := hthetaEig k0
            _ = -(((n : ℝ) - 1) * w) := heqneg
  have hMabs :
      effectiveInteractionMatrix a c |m| κ = M := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [M]
    · simp [M, effectiveInteractionMatrix_apply, hij, sq_abs]
  have hthetaMono : Monotone theta := by
    simpa [theta] using effectiveInteractionTheta_monotone a c m κ
  have hforall : ∀ k : Fin n, k.val ≠ 0 → theta k = w := by
    intro k hk
    rcases hclass (Fin.rev k) with heqw | heqneg
    · exact (hthetaEig k).trans heqw
    · have hnegEq : theta k = -(((n : ℝ) - 1) * w) := by
        rw [hthetaEig k]
        exact heqneg
      by_cases hwzero : w = 0
      · calc
          theta k = -(((n : ℝ) - 1) * w) := hnegEq
          _ = 0 := by simp [hwzero]
          _ = w := hwzero.symm
      · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hwzero)
        have hn2 : 2 ≤ n := by
          have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
          omega
        have hcne : c ≠ 0 := by
          intro hc0
          have hzero : w = 0 := by simp [w, hc0]
          exact hwzero hzero
        have hmne : m ≠ 0 := by
          intro hm0
          have hzero : w = 0 := by simp [w, hm0]
          exact hwzero hzero
        have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcne)
        let eqv : ι ≃ Fin n :=
          (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
        have hqneq : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
          intro hh
          have hv := congrArg Fin.val hh
          norm_num at hv
        let site0 : ι := eqv.symm (⟨0, by omega⟩ : Fin n)
        let site1 : ι := eqv.symm (⟨1, by omega⟩ : Fin n)
        have hsite : site0 ≠ site1 := by
          intro hh
          apply hqneq
          have heq := congrArg eqv hh
          change eqv (eqv.symm (⟨0, by omega⟩ : Fin n)) =
            eqv (eqv.symm (⟨1, by omega⟩ : Fin n)) at heq
          simpa only [Equiv.apply_symm_apply] using heq
        have hground := collectiveGround_matrix hn2 a ha c |m| κ hcpos
          (abs_pos.mpr hmne)
        have hsimpleAbs := hground.2.1
        let k1 : Fin n := ⟨1, by omega⟩
        have hsimple : theta k0 < theta k1 := by
          simpa [theta, k0, k1, effectiveInteractionTheta, M, hMabs] using hsimpleAbs
        have hk1le : k1 ≤ k := by
          apply Fin.le_iff_val_le_val.mpr
          simp [k1]
          exact Nat.one_le_iff_ne_zero.mpr hk
        have hmono := hthetaMono hk1le
        have hstrict : theta k0 < theta k := hsimple.trans_le hmono
        have hne : theta k ≠ -(((n : ℝ) - 1) * w) := by
          intro heq
          rw [htheta0] at hstrict
          rw [heq] at hstrict
          exact (lt_irrefl _ hstrict)
        exact (hne hnegEq).elim
  refine ⟨hcard, ?_, ?_⟩
  · simpa [theta, n, w, k0] using htheta0
  · intro k hk
    simpa [theta, n, w] using hforall k hk

end Tunneling
