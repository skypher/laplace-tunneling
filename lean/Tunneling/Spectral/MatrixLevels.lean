import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Tunneling.Spectral.MinMax

/-!
# Courant--Fischer in finite dimensions

If `e` is an orthonormal basis of a finite-dimensional real inner product
space `V`, the Courant--Fischer levels of a quadratic map `Q` on `V` are the
eigenvalues, in increasing order, of its Galerkin matrix
`A i j = polar Q (e i) (e j) / 2`.  Used for the Galerkin eigenvalues of paper
Section 5 and for the finite-matrix parts of the corollaries.
-/

namespace Tunneling
namespace MinMax

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem associated_diag_helper (Q : QuadraticMap ℝ V ℝ) (x y : V) :
    (QuadraticMap.associatedHom ℝ Q) x y = QuadraticMap.polar Q x y / 2 := by
  rw [QuadraticMap.associated_apply]
  change (⅟(2 : Module.End ℝ ℝ)) (Q (x+y)-Q x-Q y) = _
  rw [QuadraticMap.half_moduleEnd_apply_eq_half_smul]
  simp only [QuadraticMap.polar, smul_eq_mul]
  norm_num
  ring
private theorem associated_self_helper (Q : QuadraticMap ℝ V ℝ) (x : V) :
    (QuadraticMap.associatedHom ℝ Q) x x = Q x := by
  rw [associated_diag_helper]
  rw [QuadraticMap.polar]
  have hq : Q (x+x)=4*Q x := by
    rw [show x+x=(2:ℝ) • x by module]
    rw [Q.map_smul]
    norm_num [smul_eq_mul]
  rw [hq]
  norm_num
  ring

set_option maxHeartbeats 1000000 in
private theorem level_eq_eigenbasis_aux {n : ℕ} [FiniteDimensional ℝ V]
    (Q : QuadraticMap ℝ V ℝ) (b : OrthonormalBasis (Fin n) ℝ V)
    (lam : Fin n → ℝ) (hlam : Antitone lam)
    (hQ : ∀ x, Q x = ∑ i, lam i * inner ℝ (b i) x * inner ℝ (b i) x)
    (k : Fin n) :
    level Q k.val = lam (Fin.rev k) := by
  classical
  let castUp : Fin (k.val + 1) → Fin n :=
    Fin.castLE (Nat.succ_le_of_lt k.isLt)
  let f : Fin (k.val + 1) → Fin n := fun i => Fin.rev (castUp i)
  let v : Fin (k.val + 1) → V := fun i => b.toBasis (f i)
  let S : Set (Fin n) := Set.range f
  let W : Submodule ℝ V := Submodule.span ℝ (b.toBasis '' S)
  have hfi : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val (Fin.rev_injective hij)
    simpa [f, castUp] using h
  have hli : LinearIndependent ℝ v := by
    dsimp [v]
    exact b.toBasis.linearIndependent.comp f hfi
  have hrange : Set.range v = b.toBasis '' S := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨j, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hspan : Submodule.span ℝ (Set.range v) = W := by
    dsimp [W]
    exact congrArg (Submodule.span ℝ) hrange
  have hW : Module.finrank ℝ W = k.val + 1 := by
    rw [← hspan, finrank_span_eq_card hli]
    simp
  have hcoeff (x : V) (i : Fin n) :
      b.toBasis.repr x i = inner ℝ (b i) x := by
    simpa [OrthonormalBasis.coe_toBasis_repr_apply] using
      OrthonormalBasis.repr_apply_apply b x i
  have hnorm (x : V) :
      (∑ i, inner ℝ (b i) x * inner ℝ (b i) x) = ‖x‖ ^ 2 := by
    have h := OrthonormalBasis.sum_sq_norm_inner_right b x
    calc
      _ = ∑ i, |inner ℝ (b i) x| ^ 2 := by
        congr 1 with i
        rw [sq_abs]
        ring
      _ = ‖x‖ ^ 2 := by simpa [Real.norm_eq_abs] using h
  have hupper (x : V) (hx : x ∈ W) : Q x ≤ lam (Fin.rev k) * ‖x‖ ^ 2 := by
    have hsub := Module.Basis.repr_support_subset_of_mem_span b.toBasis S hx
    have hsupport : ∀ i, inner ℝ (b i) x ≠ 0 → i ∈ S := by
      intro i hi
      have hm : i ∈ (b.toBasis.repr x).support := by
        simpa [Finsupp.mem_support_iff, hcoeff x i] using hi
      exact hsub hm
    have hterm : ∀ i, lam i * inner ℝ (b i) x * inner ℝ (b i) x ≤
        lam (Fin.rev k) * inner ℝ (b i) x * inner ℝ (b i) x := by
      intro i
      by_cases hi : i ∈ S
      · rcases hi with ⟨j, rfl⟩
        have hc : castUp j ≤ k := by
          apply Fin.le_iff_val_le_val.mpr
          exact Nat.le_of_lt_succ j.isLt
        have hrev : Fin.rev k ≤ f j := by
          rw [Fin.rev_le_iff]
          simpa [f, Fin.rev_rev] using hc
        have hle : lam (f j) ≤ lam (Fin.rev k) := hlam hrev
        nlinarith [sq_nonneg (inner ℝ (b (f j)) x)]
      · have hz : inner ℝ (b i) x = 0 := by
          by_contra hn
          exact hi (hsupport i hn)
        simp [hz]
    have hsum : (∑ i : Fin n, lam i * inner ℝ (b i) x * inner ℝ (b i) x) ≤
        ∑ i : Fin n, lam (Fin.rev k) * inner ℝ (b i) x * inner ℝ (b i) x :=
      Finset.sum_le_sum (fun i _ => hterm i)
    calc
      Q x = ∑ i, lam i * inner ℝ (b i) x * inner ℝ (b i) x := hQ x
      _ ≤ ∑ i, lam (Fin.rev k) * inner ℝ (b i) x * inner ℝ (b i) x := hsum
      _ = lam (Fin.rev k) * (∑ i, inner ℝ (b i) x * inner ℝ (b i) x) := by
        rw [Finset.mul_sum]
        congr 1 with i
        ring
      _ = lam (Fin.rev k) * ‖x‖ ^ 2 := by rw [hnorm]
  have hbdd : ∃ m : ℝ, ∀ x : V, m * ‖x‖ ^ 2 ≤ Q x := by
    let m : ℝ := -∑ i, |lam i|
    have hmlam : ∀ i, m ≤ lam i := by
      intro i
      have hsum : |lam i| ≤ ∑ j, |lam j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (lam j)) (Finset.mem_univ i)
      dsimp [m]
      have hneg : -|lam i| ≤ lam i := neg_abs_le _
      linarith
    refine ⟨m, ?_⟩
    intro x
    have hterm : ∀ i, m * inner ℝ (b i) x * inner ℝ (b i) x ≤
        lam i * inner ℝ (b i) x * inner ℝ (b i) x := by
      intro i
      nlinarith [hmlam i, sq_nonneg (inner ℝ (b i) x)]
    have hsum : (∑ i : Fin n, m * inner ℝ (b i) x * inner ℝ (b i) x) ≤
        ∑ i : Fin n, lam i * inner ℝ (b i) x * inner ℝ (b i) x :=
      Finset.sum_le_sum (fun i _ => hterm i)
    calc
      m * ‖x‖ ^ 2 = m * (∑ i, inner ℝ (b i) x * inner ℝ (b i) x) := by
            rw [hnorm]
      _ = ∑ i, m * inner ℝ (b i) x * inner ℝ (b i) x := by
            rw [Finset.mul_sum]
            congr 1 with i
            ring
      _ ≤ ∑ i, lam i * inner ℝ (b i) x * inner ℝ (b i) x := hsum
      _ = Q x := (hQ x).symm
  have hlevel_le : level Q k.val ≤ lam (Fin.rev k) :=
    level_le Q k.val hbdd W hW (lam (Fin.rev k)) hupper
  let e : Fin k.val → V :=
    fun i => b (Fin.rev (Fin.castLE (Nat.le_of_lt k.isLt) i))
  have hlower : ∀ x : V, (∀ i, inner ℝ (e i) x = 0) →
      lam (Fin.rev k) * ‖x‖ ^ 2 ≤ Q x := by
    intro x horth
    have hsupport : ∀ j, inner ℝ (b j) x ≠ 0 → j ≤ Fin.rev k := by
      intro j hj
      by_contra hnot
      have hgt : Fin.rev k < j := lt_of_not_ge hnot
      have hi : Fin.rev j < k := Fin.rev_lt_iff.mp hgt
      let i : Fin k.val := ⟨(Fin.rev j).val, hi⟩
      have hcast : Fin.castLE (Nat.le_of_lt k.isLt) i = Fin.rev j := Fin.ext rfl
      have hidx : Fin.rev (Fin.castLE (Nat.le_of_lt k.isLt) i) = j := by
        rw [hcast, Fin.rev_rev]
      have hz := horth i
      have hz' : inner ℝ (b j) x = 0 := by simpa [e, hidx] using hz
      exact hj hz'
    have hterm : ∀ j, lam (Fin.rev k) * inner ℝ (b j) x * inner ℝ (b j) x ≤
        lam j * inner ℝ (b j) x * inner ℝ (b j) x := by
      intro j
      by_cases hj : j ≤ Fin.rev k
      · have hle : lam (Fin.rev k) ≤ lam j := hlam hj
        nlinarith [sq_nonneg (inner ℝ (b j) x)]
      · have hz : inner ℝ (b j) x = 0 := by
          by_contra hn
          exact hj (hsupport j hn)
        simp [hz]
    have hsum : (∑ j : Fin n, lam (Fin.rev k) * inner ℝ (b j) x * inner ℝ (b j) x) ≤
        ∑ j : Fin n, lam j * inner ℝ (b j) x * inner ℝ (b j) x :=
      Finset.sum_le_sum (fun j _ => hterm j)
    calc
      lam (Fin.rev k) * ‖x‖ ^ 2 =
          lam (Fin.rev k) * (∑ j, inner ℝ (b j) x * inner ℝ (b j) x) := by
            rw [hnorm]
      _ = ∑ j, lam (Fin.rev k) * inner ℝ (b j) x * inner ℝ (b j) x := by
            rw [Finset.mul_sum]
            congr 1 with j
            ring
      _ ≤ ∑ j, lam j * inner ℝ (b j) x * inner ℝ (b j) x := hsum
      _ = Q x := (hQ x).symm
  have hlevel_ge : lam (Fin.rev k) ≤ level Q k.val :=
    le_level Q k.val e (lam (Fin.rev k)) hlower ⟨W, hW⟩
  exact le_antisymm hlevel_le hlevel_ge

/-- Finite-dimensional min--max: levels are the ordered Galerkin eigenvalues. -/
theorem level_eq_eigenvalues₀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticMap ℝ V ℝ) (e : ι → V) (he : Orthonormal ℝ e)
    (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    (A : Matrix ι ι ℝ) (hAe : ∀ i j, A i j = QuadraticMap.polar Q (e i) (e j) / 2)
    (hA : A.IsHermitian) (k : Fin (Fintype.card ι)) :
    level Q k = hA.eigenvalues₀ (Fin.rev k) := by
  classical
  let eb : OrthonormalBasis ι ℝ V := OrthonormalBasis.mk he (by rw [hspan])
  letI : FiniteDimensional ℝ V := eb.toBasis.finiteDimensional_of_finite
  let coord : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι := eb.repr
  let Aop : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := Matrix.toEuclideanLin A
  let T : V →ₗ[ℝ] V := coord.symm.toLinearMap.comp (Aop.comp coord.toLinearMap)
  have hAop : Aop.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hT : T.IsSymmetric := by
    intro x y
    calc
      inner ℝ (T x) y = inner ℝ (coord (T x)) (coord y) := by rw [coord.inner_map_map]
      _ = inner ℝ (Aop (coord x)) (coord y) := by simp [T]
      _ = inner ℝ (coord x) (Aop (coord y)) := hAop (coord x) (coord y)
      _ = inner ℝ x (T y) := by
        rw [← coord.inner_map_map x (T y)]
        simp [T]
  let B : LinearMap.BilinForm ℝ V := QuadraticMap.associatedHom ℝ Q
  let F : LinearMap.BilinForm ℝ V :=
    { toFun := fun x =>
        { toFun := fun y => inner ℝ x (T y)
          map_add' := by intro y z; simp [T.map_add, inner_add_right]
          map_smul' := by intro a y; simp [T.map_smul, real_inner_smul_right] }
      map_add' := by intro x y; ext z; simp [inner_add_left]
      map_smul' := by intro a x; ext z; simp [real_inner_smul_left] }
  let std : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) := EuclideanSpace.basisFun ι ℝ
  have hcoordbasis (i : ι) : coord (eb i) = std i := by
    ext j
    rw [OrthonormalBasis.repr_apply_apply]
    rw [EuclideanSpace.basisFun_apply]
    simp only [EuclideanSpace.single_apply]
    have hei : eb i = e i := by simp [eb, OrthonormalBasis.coe_mk]
    have hej : eb j = e j := by simp [eb, OrthonormalBasis.coe_mk]
    rw [hei, hej]
    exact (orthonormal_iff_ite.mp he) j i
  have hstd : ∀ i j, inner ℝ (std i) (Aop (std j)) = A i j := by
    intro i j
    have hmat : LinearMap.toMatrixOrthonormal std Aop = A := by
      change LinearMap.toMatrix std.toBasis std.toBasis (Matrix.toEuclideanLin A) = A
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      exact LinearMap.toMatrix_toLin std.toBasis std.toBasis A
    calc
      inner ℝ (std i) (Aop (std j)) =
          (LinearMap.toMatrixOrthonormal std Aop) i j :=
        (LinearMap.toMatrixOrthonormal_apply_apply std Aop i j).symm
      _ = A i j := by rw [hmat]
  have hBpol (x y : V) : B x y = QuadraticMap.polar Q x y / 2 := by
    change (QuadraticMap.associatedHom ℝ Q) x y = _
    exact associated_diag_helper Q x y
  have hBF : B = F := by
    apply LinearMap.BilinForm.ext_basis eb.toBasis
    intro i j
    have hFij : F (eb i) (eb j) = A i j := by
      calc
        F (eb i) (eb j) = inner ℝ (eb i) (T (eb j)) := rfl
        _ = inner ℝ (coord (eb i)) (Aop (coord (eb j))) := by
          rw [← coord.inner_map_map (eb i) (T (eb j))]
          simp [T]
        _ = inner ℝ (std i) (Aop (std j)) := by rw [hcoordbasis i, hcoordbasis j]
        _ = A i j := hstd i j
    have hBij : B (eb i) (eb j) = A i j := by
      rw [hBpol]
      have hei : eb i = e i := by simp [eb, OrthonormalBasis.coe_mk]
      have hej : eb j = e j := by simp [eb, OrthonormalBasis.coe_mk]
      rw [hei, hej]
      exact (hAe i j).symm
    exact hBij.trans hFij.symm
  have hdiag (x : V) : B x x = Q x := by
    change (QuadraticMap.associatedHom ℝ Q) x x = Q x
    exact associated_self_helper Q x
  have hQT (x : V) : Q x = inner ℝ (T x) x := by
    calc
      Q x = B x x := (hdiag x).symm
      _ = F x x := by rw [hBF]
      _ = inner ℝ x (T x) := rfl
      _ = inner ℝ (T x) x := real_inner_comm _ _
  let er : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  let b : OrthonormalBasis (Fin (Fintype.card ι)) ℝ V :=
    (hA.eigenvectorBasis.map coord.symm).reindex er.symm
  have hlam (j : Fin (Fintype.card ι)) :
      hA.eigenvalues (er j) = hA.eigenvalues₀ j := by
    simp [Matrix.IsHermitian.eigenvalues, er]
  have hTb (j : Fin (Fintype.card ι)) :
      T (b j) = hA.eigenvalues₀ j • b j := by
    apply coord.injective
    simp [b, T, Aop, hlam, Matrix.toEuclideanLin_apply, hA.mulVec_eigenvectorBasis]

  have hQ (x : V) :
      Q x = ∑ j, hA.eigenvalues₀ j * inner ℝ (b j) x * inner ℝ (b j) x := by
    calc
      Q x = inner ℝ (T x) x := hQT x
      _ = ∑ j, hA.eigenvalues₀ j * inner ℝ (b j) x * inner ℝ (b j) x := by
        calc
          inner ℝ (T x) x =
              ∑ j, inner ℝ (T x) (b j) * inner ℝ (b j) x :=
            (OrthonormalBasis.sum_inner_mul_inner b (T x) x).symm
          _ = ∑ j, hA.eigenvalues₀ j * inner ℝ (b j) x * inner ℝ (b j) x := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hT x (b j), hTb j, inner_smul_right, real_inner_comm x (b j)]
  have hmain := level_eq_eigenbasis_aux Q b hA.eigenvalues₀
    hA.eigenvalues₀_antitone hQ k
  simpa using hmain


end MinMax
end Tunneling
