import Tunneling.Euclid.CellMatrix
import Tunneling.Euclid.Compression
import Tunneling.Spectral.Cluster
import Tunneling.Spectral.MatrixLevels
import Tunneling.Spectral.PerronFrobenius
import Tunneling.Euclid.DecompForm
import Tunneling.Euclid.DecompBound
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Fixed-mesh cluster asymptotic (paper Corollary 5.2)

`d = 1`, `0 < s < 1/2`, `D = (-1/2, 1/2)` with the uniform partition into `n`
cells of length `h = 1/n` and centres `x_α = -1/2 + (α + 1/2) h`.  The one-well
Galerkin matrix is `A_h = (B(e_α, e_β))` in the orthonormal basis
`e_α = h^{-1/2} 1_{I_α}` (entries from paper Proposition 5.1), and the
multi-well Galerkin matrix on `⋃_j (D + L a_j)` with the translated partition
is `H_{h,L}((i,α),(j,β)) = B(e_{i,α}, e_{j,β})`, `e_{i,α}` the cell vector
centred at `L a_i + x_α`.  Its ordered eigenvalues satisfy
`λ_{k,h}(L) = μ_{1,h} + L^{-1-2s} θ_{k,h} + O(L^{-3-2s} + L^{-2-4s})`.
-/
namespace Tunneling

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- Centres of the uniform partition of `(-1/2, 1/2)` into `n` cells. -/
noncomputable def meshCenter (n : ℕ) (α : Fin n) : ℝ := -1 / 2 + ((α : ℝ) + 1 / 2) / n

/-- The one-well Galerkin matrix `A_h`. -/
noncomputable def oneWellGalerkin (c s : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun α β =>
    formBilin c (1 + 2 * s) (cellVec (meshCenter n α) (1 / n)) (cellVec (meshCenter n β) (1 / n))

/-- The multi-well Galerkin matrix `H_{h,L}` for sites `a : ι → ℝ`. -/
noncomputable def multiWellGalerkin {ι : Type*} (c s : ℝ) (n : ℕ) (a : ι → ℝ) (L : ℝ) :
    Matrix (ι × Fin n) (ι × Fin n) ℝ :=
  Matrix.of fun p q =>
    formBilin c (1 + 2 * s) (cellVec (L * a p.1 + meshCenter n p.2) (1 / n))
      (cellVec (L * a q.1 + meshCenter n q.2) (1 / n))

private def linePoint (t : ℝ) : Eucl 1 :=
  WithLp.toLp 2 (fun _ : Fin 1 => t)

private theorem linePoint_norm (t : ℝ) : ‖linePoint t‖ = |t| := by
  have hsq : ‖linePoint t‖ ^ 2 = t ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [linePoint]
  nlinarith [norm_nonneg (linePoint t), abs_nonneg t, sq_abs t]

private theorem linePoint_sub_norm (t u : ℝ) : ‖linePoint t - linePoint u‖ = |t-u| := by
  rw [show linePoint t - linePoint u = linePoint (t-u) by
    ext i
    fin_cases i
    simp [linePoint]]
  exact linePoint_norm _

private theorem linePoint_smul (L t : ℝ) : L • linePoint t = linePoint (L*t) := by
  ext i
  fin_cases i
  simp [linePoint]

private theorem cellVec_translate (t a h : ℝ) :
    translateL2 (linePoint t) (cellVec a h) = cellVec (t+a) h := by
  rw [cellVec, cellVec]
  rw [map_smul]
  congr 1
  have hpres : MeasurePreserving (fun x : Eucl 1 => x - linePoint t) volume volume :=
    measurePreserving_sub_right volume (linePoint t)
  change Lp.compMeasurePreserving (fun x : Eucl 1 => x-linePoint t) hpres
    (indicatorConstLp 2 (measurableSet_lineCell a h) (volume_lineCell_ne_top a h) (1:ℝ)) = _
  have hcomp := Lp.indicatorConstLp_compMeasurePreserving
    (p := 2) (hs := measurableSet_lineCell a h) (hμs := volume_lineCell_ne_top a h)
    (c := (1:ℝ)) (hf := hpres)
  have hset : (fun x : Eucl 1 => x-linePoint t) ⁻¹' lineCell a h = lineCell (t+a) h := by
    ext x
    simp only [Set.mem_preimage, lineCell, Set.mem_setOf_eq]
    change |(x-linePoint t) 0-a| < h/2 ↔ |x 0-(t+a)| < h/2
    rw [show (x-linePoint t) 0=x 0-t by simp [linePoint]]
    rw [show x 0-t-a=x 0-(t+a) by ring]
  have hcomp' : Lp.compMeasurePreserving (fun x : Eucl 1 => x-linePoint t) hpres
      (indicatorConstLp 2 (measurableSet_lineCell a h) (volume_lineCell_ne_top a h) (1:ℝ)) =
      indicatorConstLp 2 (measurableSet_lineCell (t+a) h)
        (volume_lineCell_ne_top (t+a) h) (1:ℝ) := by
    simpa only [hset] using hcomp
  simpa [hcomp']

private theorem meshCenter_sub (n : ℕ) (α β : Fin n) :
    meshCenter n α - meshCenter n β = ((α:ℝ)-(β:ℝ))/n := by
  simp [meshCenter]
  ring

private theorem meshCenter_separated (n : ℕ) (hn : 1 ≤ n) (α β : Fin n) (hab : α ≠ β) :
    (1 : ℝ) / n ≤ |meshCenter n α - meshCenter n β| := by
  have hnpos : (0:ℝ) < n := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [meshCenter_sub, abs_div, abs_of_pos hnpos]
  have hval : (1:ℝ) ≤ |(α:ℝ) - (β:ℝ)| := by
    have hne : α.val ≠ β.val := fun h => hab (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hcast : (α:ℝ) < β := by exact_mod_cast hlt
      rw [abs_of_nonpos (by linarith)]
      have hsucc : (α.val:ℝ)+1 ≤ β := by exact_mod_cast (Nat.succ_le_of_lt hlt)
      linarith
    · have hcast : (β:ℝ) < α := by exact_mod_cast hgt
      rw [abs_of_nonneg (by linarith)]
      have hsucc : (β.val:ℝ)+1 ≤ α := by exact_mod_cast (Nat.succ_le_of_lt hgt)
      linarith
  have hvaln := mul_le_mul_of_nonneg_right hval hnpos.le
  exact (div_le_div_iff₀ hnpos hnpos).2 (by nlinarith [hvaln])

private theorem meshCell_subset (n : ℕ) (hn : 1 ≤ n) (α : Fin n) :
    lineCell (meshCenter n α) ((1:ℝ)/n) ⊆ lineCell 0 1 := by
  intro x hx
  have hnpos : (0:ℝ)<n := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hα0 : (0:ℝ)≤(α:ℝ) := by positivity
  have hαn : (α:ℝ)+1≤n := by
    have hh : α.val+1≤n := Nat.succ_le_of_lt α.isLt
    exact_mod_cast hh
  change |x 0-meshCenter n α| < ((1:ℝ)/n)/2 at hx
  change |x 0-(0:ℝ)| < (1:ℝ)/2
  rw [abs_lt] at hx ⊢
  have hmargin : ((1:ℝ)/n)/2 = (1/2:ℝ)/n := by ring
  rw [hmargin] at hx
  have hc_lo : -(1:ℝ)/2 + (1/2)/n ≤ meshCenter n α := by
    dsimp [meshCenter]
    have hprod : (1/2:ℝ) ≤ (α:ℝ)+1/2 := by linarith
    have hdiv : (1/2)/n ≤ ((α:ℝ)+1/2)/n :=
      (div_le_div_iff₀ hnpos hnpos).2 (by nlinarith)
    linarith
  have hc_hi : meshCenter n α ≤ (1:ℝ)/2 - (1/2)/n := by
    dsimp [meshCenter]
    have hprod : (α:ℝ)+1/2 ≤ (n:ℝ)-1/2 := by linarith
    have hdiv : ((α:ℝ)+1/2)/n ≤ ((n:ℝ)-1/2)/n :=
      (div_le_div_iff₀ hnpos hnpos).2 (by nlinarith)
    have hcancel : (((n:ℝ)-(1/2:ℝ))/(n:ℝ)) = (1:ℝ)-(1/2:ℝ)/(n:ℝ) := by
      calc
       ((n:ℝ)-(1/2:ℝ))/(n:ℝ) = (n:ℝ)/(n:ℝ)-(1/2:ℝ)/(n:ℝ) := by rw [sub_div]
       _ = (1:ℝ)-(1/2:ℝ)/(n:ℝ) := by rw [div_self hnpos.ne']
    rw [hcancel] at hdiv
    linarith
  constructor <;> linarith

private theorem lineCell_disjoint_of_sep (a b h:ℝ) (hab:h≤|a-b|) :
    Disjoint (lineCell a h) (lineCell b h) := by
  rw [Set.disjoint_left]
  intro x hx hy
  change |x 0-a|<h/2 at hx
  change |x 0-b|<h/2 at hy
  have hcenter : |a-b|≤|a-x 0|+|x 0-b| := by
    calc
      |a-b| = |(a-x 0)+(x 0-b)| := by congr 1 <;> ring
      _ ≤ |a-x 0|+|x 0-b| := abs_add_le _ _
  have hxa : |a-x 0|<h/2 := by simpa [abs_sub_comm] using hx
  nlinarith

private theorem cellVec_inner_zero_of_sep (a b h : ℝ) (_hh:0<h) (hab:h≤|a-b|) :
    inner ℝ (cellVec a h) (cellVec b h)=0 := by
  have hdis := lineCell_disjoint_of_sep a b h hab
  have hint : lineCell a h ∩ lineCell b h = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hdis
  simp only [cellVec, inner_smul_left, inner_smul_right]
  rw [MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp
    (𝕜 := ℝ) (hs := measurableSet_lineCell a h) (ht := measurableSet_lineCell b h)
    (hμs := volume_lineCell_ne_top a h) (hμt := volume_lineCell_ne_top b h) (1:ℝ) (1:ℝ)]
  simp [hint]

private abbrev meshGeometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (a : ι→ℝ) (L : ℝ) (hL : 0<L)
    (hsep : ∀ i j, i≠j → 4 ≤ L*|a i-a j|) : WellGeometry 1 ι where
  κ := 1+2*s
  hκ := by linarith [hs.1]
  R := 1
  hR := by norm_num
  D := lineCell 0 1
  hDm := measurableSet_lineCell 0 1
  hDR := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    have hx' : |x 0| < (1:ℝ)/2 := by simpa [lineCell] using hx
    have hsq : ‖x‖^2=(x 0)^2 := by rw [EuclideanSpace.real_norm_sq_eq]; simp
    have hn : ‖x‖=|x 0| := by nlinarith [norm_nonneg x, abs_nonneg (x 0), sq_abs (x 0)]
    rw [show x - (0:Eucl 1) = x by simp, hn]
    change |x 0| < 1
    linarith
  a := fun i => linePoint (a i)
  L := L
  hL := hL
  hsep := by
    intro i j hij
    rw [linePoint_sub_norm]
    nlinarith [hsep i j hij]

private noncomputable def meshCellDomain (s : ℝ) (hs : 0<s ∧ s<1/2)
    (n : ℕ) (hn : 1≤n) (α : Fin n) : formDomain (1+2*s) (lineCell 0 1) :=
  ⟨cellVec (meshCenter n α) (1/n),
   cellVec_mem_formDomain s hs (meshCenter n α) (1/n)
     (one_div_pos.mpr (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)))
     (lineCell 0 1) (meshCell_subset n hn α)⟩

private theorem meshTranslate_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j → 4≤L*|a i-a j|)
    (i : ι) (α : Fin n) :
    (((meshGeometry s hs a L hL hsep).Φ (meshCellDomain s hs n hn α) i :
       formDomain (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1) =
      cellVec (L*a i+meshCenter n α) (1/n) := by
  change translateL2 (L • linePoint (a i)) (cellVec (meshCenter n α) (1/n)) = _
  rw [linePoint_smul, cellVec_translate]

private theorem meshCenter_abs_lt_half (n : ℕ) (hn : 1 ≤ n) (α : Fin n) :
    |meshCenter n α| < (1:ℝ)/2 := by
  have hnpos : (0:ℝ)<n := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmem : linePoint (meshCenter n α) ∈ lineCell (meshCenter n α) (1/n) := by
    change |(linePoint (meshCenter n α)) 0 - meshCenter n α| < (1/n)/2
    have hwidth : 0 < (1:ℝ)/n/2 := div_pos (one_div_pos.mpr hnpos) (by norm_num)
    simpa [linePoint] using hwidth
  have h := meshCell_subset n hn α hmem
  change |(linePoint (meshCenter n α)) 0 - 0| < 1/2 at h
  simpa [linePoint] using h

private theorem meshCellCenters_separated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 1 ≤ n) (a : ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hsep : ∀ i j, i ≠ j → 4 ≤ L * |a i-a j|)
    (p q : ι × Fin n) (hpq : p ≠ q) :
    (1:ℝ)/n ≤ |(L*a p.1+meshCenter n p.2) -
      (L*a q.1+meshCenter n q.2)| := by
  by_cases hsite : p.1=q.1
  · have hcell : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hsite h)
    have heq : (L*a p.1+meshCenter n p.2) -
        (L*a q.1+meshCenter n q.2) =
        meshCenter n p.2-meshCenter n q.2 := by rw [hsite]; ring
    rw [heq]
    exact meshCenter_separated n hn p.2 q.2 hcell
  · have hsiteDist : 4 ≤ |L*a p.1 - L*a q.1| := by
      have h := hsep p.1 q.1 hsite
      have habs : |L*a p.1-L*a q.1| = L*|a p.1-a q.1| := by
        rw [show L*a p.1-L*a q.1 = L*(a p.1-a q.1) by ring,
          abs_mul, abs_of_pos hL]
      rw [habs]
      exact h
    have hcenter : |meshCenter n p.2-meshCenter n q.2| < 1 := by
      have hp := meshCenter_abs_lt_half n hn p.2
      have hq := meshCenter_abs_lt_half n hn q.2
      calc
        |meshCenter n p.2-meshCenter n q.2| ≤
            |meshCenter n p.2|+|meshCenter n q.2| := by
              simpa using (abs_sub_le (meshCenter n p.2) 0 (meshCenter n q.2))
        _ < 1 := by linarith
    have htri : |L*a p.1-L*a q.1| ≤
        |(L*a p.1+meshCenter n p.2)-
          (L*a q.1+meshCenter n q.2)|+
            |meshCenter n p.2-meshCenter n q.2| := by
      calc
        |L*a p.1-L*a q.1| =
            |((L*a p.1+meshCenter n p.2)-
              (L*a q.1+meshCenter n q.2))+
              (meshCenter n q.2-meshCenter n p.2)| := by
                congr 1 <;> ring
        _ ≤ |(L*a p.1+meshCenter n p.2)-
              (L*a q.1+meshCenter n q.2)|+
              |meshCenter n q.2-meshCenter n p.2| := abs_add_le _ _
        _ = |(L*a p.1+meshCenter n p.2)-
              (L*a q.1+meshCenter n q.2)|+
              |meshCenter n p.2-meshCenter n q.2| := by
                apply congrArg (fun z : ℝ =>
                  |(L*a p.1+meshCenter n p.2)-(L*a q.1+meshCenter n q.2)| + z)
                calc
                  |meshCenter n q.2-meshCenter n p.2| =
                      |-(meshCenter n p.2-meshCenter n q.2)| := by
                        congr 1 <;> ring
                  _ = |meshCenter n p.2-meshCenter n q.2| := by rw [abs_neg]
    have hnle : (1:ℝ)/n ≤ 1 := by
      have hnpos : (0:ℝ)<n := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
      have hncast : (1:ℝ) ≤ n := by exact_mod_cast hn
      exact (div_le_one hnpos).2 hncast
    linarith

private theorem meshGlobal_onorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j→4≤L*|a i-a j|) :
    Orthonormal ℝ (fun p : ι×Fin n =>
      (((meshGeometry s hs a L hL hsep).Φ (meshCellDomain s hs n hn p.2) p.1) : L2 1)) := by
  rw [orthonormal_iff_ite]
  intro p q
  rw [meshTranslate_cell s hs n hn a L hL hsep p.1 p.2,
    meshTranslate_cell s hs n hn a L hL hsep q.1 q.2]
  by_cases hpq : p=q
  · subst q
    simp only [if_pos rfl, real_inner_self_eq_norm_sq]
    have hnpos : (0:ℝ)<n := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    rw [norm_cellVec _ _ (one_div_pos.mpr hnpos)]
    norm_num
  · rw [if_neg hpq]
    exact cellVec_inner_zero_of_sep _ _ _ (one_div_pos.mpr
      (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)))
      (meshCellCenters_separated n hn a L hL hsep p q hpq)

private noncomputable def meshEmbed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j→4≤L*|a i-a j|) :
    EuclideanSpace ℝ (ι×Fin n) →ₗ[ℝ] formDomain (1+2*s)
      (meshGeometry s hs a L hL hsep).Ω where
  toFun z := ∑ p, z p •
    (meshGeometry s hs a L hL hsep).Φ (meshCellDomain s hs n hn p.2) p.1
  map_add' x y := by
    simp [Finset.sum_add_distrib, add_smul]
  map_smul' t x := by
    simp [Finset.smul_sum, smul_smul]

private theorem meshEmbed_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j→4≤L*|a i-a j|)
    (x y : EuclideanSpace ℝ (ι×Fin n)) :
    inner ℝ ((meshEmbed s hs n hn a L hL hsep x : formDomain
      (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1)
      ((meshEmbed s hs n hn a L hL hsep y : formDomain
      (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1) =
      inner ℝ x y := by
  classical
  let F : ι×Fin n → L2 1 := fun p =>
    ((meshGeometry s hs a L hL hsep).Φ
      (meshCellDomain s hs n hn p.2) p.1 : formDomain
        (1+2*s) (meshGeometry s hs a L hL hsep).Ω)
  have hON : Orthonormal ℝ F := by
    simpa [F] using meshGlobal_onorm s hs n hn a L hL hsep
  have hx : ((meshEmbed s hs n hn a L hL hsep x : formDomain
      (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1) =
      ∑ p, x p • F p := by
    simp [meshEmbed, F, Submodule.coe_sum, map_sum]
  have hy : ((meshEmbed s hs n hn a L hL hsep y : formDomain
      (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1) =
      ∑ p, y p • F p := by
    simp [meshEmbed, F, Submodule.coe_sum, map_sum]
  calc
    _ = ∑ p, x p * inner ℝ (F p) (∑ q, y q • F q) := by
      rw [hx, hy]
      simp [sum_inner, inner_smul_left]
    _ = ∑ p, x p * y p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hON.inner_right_fintype y p]
    _ = inner ℝ x y := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Real.inner_apply]

private theorem meshEmbed_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j→4≤L*|a i-a j|)
    (z : EuclideanSpace ℝ (ι×Fin n)) :
    ‖meshEmbed s hs n hn a L hL hsep z‖ = ‖z‖ := by
  change ‖((meshEmbed s hs n hn a L hL hsep z : formDomain
    (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1)‖ = ‖z‖
  have h := meshEmbed_inner s hs n hn a L hL hsep z z
  change inner ℝ ((meshEmbed s hs n hn a L hL hsep z : formDomain
    (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1)
    ((meshEmbed s hs n hn a L hL hsep z : formDomain
    (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1) =
      inner ℝ z z at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have hn1 : 0 ≤ ‖((meshEmbed s hs n hn a L hL hsep z : formDomain
      (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1)‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith [h]

private theorem meshPolar_sum {V α : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype α]
    (Q : QuadraticMap ℝ V ℝ) (e : α → V) (x y : α → ℝ) :
    QuadraticMap.polar Q (∑ i, x i • e i) (∑ j, y j • e j) =
      ∑ i, ∑ j, x i * y j * QuadraticMap.polar Q (e i) (e j) := by
  classical
  rw [← QuadraticMap.polarBilin_apply_apply, LinearMap.map_sum₂]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  ring

private theorem meshAssociated_diag {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (Q : QuadraticMap ℝ V ℝ) (x y : V) :
    (QuadraticMap.associatedHom ℝ Q) x y =
      QuadraticMap.polar Q x y / 2 := by
  rw [QuadraticMap.associated_apply]
  change (⅟(2 : Module.End ℝ ℝ)) (Q (x+y)-Q x-Q y) = _
  rw [QuadraticMap.half_moduleEnd_apply_eq_half_smul]
  simp only [QuadraticMap.polar, smul_eq_mul]
  norm_num
  ring

private theorem meshAssociated_self {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (Q : QuadraticMap ℝ V ℝ) (x : V) :
    (QuadraticMap.associatedHom ℝ Q) x x = Q x := by
  rw [meshAssociated_diag]
  rw [QuadraticMap.polar]
  have hq : Q (x+x)=4*Q x := by
    rw [show x+x=(2:ℝ) • x by module]
    rw [Q.map_smul]
    norm_num [smul_eq_mul]
  rw [hq]
  norm_num
  ring

private def meshMatrixQ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : QuadraticMap ℝ (EuclideanSpace ℝ ι) ℝ :=
  (Matrix.toQuadraticForm' A).comp (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap

private theorem meshMatrixQ_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    meshMatrixQ A x = ∑ i, ∑ j, x i * x j * A i j := by
  simp [meshMatrixQ, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply]
  congr 2 with i
  congr 2 with j
  ring

private theorem meshMatrixQ_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    meshMatrixQ A x = inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap x) x := by
  rw [meshMatrixQ_sum, EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.toEuclideanLin_apply, dotProduct, Matrix.mulVec_apply_eq_sum,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

private noncomputable def meshCellEmbed (s : ℝ) (hs : 0<s ∧ s<1/2)
    (n : ℕ) (hn : 1≤n) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      formDomain (1+2*s) (lineCell 0 1) where
  toFun z := ∑ α, z α • meshCellDomain s hs n hn α
  map_add' x y := by simp [Finset.sum_add_distrib, add_smul]
  map_smul' t x := by simp [Finset.smul_sum, smul_smul]

private theorem meshCellQ_eq_matrixQ (c s : ℝ)
    (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (z : EuclideanSpace ℝ (Fin n)) :
    formQ c (1+2*s) (lineCell 0 1)
      (meshCellEmbed s hs n hn z) =
      meshMatrixQ (oneWellGalerkin c s n) z := by
  classical
  let e : Fin n → formDomain (1+2*s) (lineCell 0 1) :=
    meshCellDomain s hs n hn
  have hentry (α β : Fin n) :
      QuadraticMap.polar (formQ c (1+2*s) (lineCell 0 1)) (e α) (e β) =
        2 * oneWellGalerkin c s n α β := by
    have h := formBilin_eq_polar c (1+2*s) (lineCell 0 1) (e α) (e β)
    have h' : formBilin c (1+2*s) (cellVec (meshCenter n α) (1/n))
          (cellVec (meshCenter n β) (1/n)) =
        QuadraticMap.polar (formQ c (1+2*s) (lineCell 0 1)) (e α) (e β) / 2 := by
      simpa [e, meshCellDomain] using h
    dsimp [oneWellGalerkin]
    rw [h']
    ring
  calc
    formQ c (1+2*s) (lineCell 0 1) (meshCellEmbed s hs n hn z) =
        QuadraticMap.polar (formQ c (1+2*s) (lineCell 0 1))
          (∑ α, z α • e α) (∑ β, z β • e β) / 2 := by
            rw [← meshAssociated_self, meshAssociated_diag]
            simp [meshCellEmbed, e]
    _ = (∑ α, ∑ β,
          z α * z β *
            QuadraticMap.polar (formQ c (1+2*s) (lineCell 0 1)) (e α) (e β)) / 2 := by
          rw [meshPolar_sum]
    _ = ∑ α, ∑ β, z α * z β * oneWellGalerkin c s n α β := by
          simp_rw [hentry]
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro α hα
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro β hβ
          ring
    _ = meshMatrixQ (oneWellGalerkin c s n) z :=
          (meshMatrixQ_sum _ _).symm


private noncomputable def meshBlockMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : ι) :
    EuclideanSpace ℝ (ι×Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun z := WithLp.toLp 2 (fun α : Fin n => z (i,α))
  map_add' x y := by ext α; simp
  map_smul' t x := by ext α; simp

private noncomputable def meshBlockQ0 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    QuadraticMap ℝ (EuclideanSpace ℝ (ι×Fin n)) ℝ :=
  ∑ i : ι, (meshMatrixQ A).comp (meshBlockMap n i)

private theorem meshEmbed_coe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j→4≤L*|a i-a j|)
    (z : EuclideanSpace ℝ (ι×Fin n)) :
    ((meshEmbed s hs n hn a L hL hsep z : formDomain
      (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1) =
      ∑ p, z p •
        (((meshGeometry s hs a L hL hsep).Φ
          (meshCellDomain s hs n hn p.2) p.1 : formDomain
            (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1) := by
  simp [meshEmbed, Submodule.coe_sum, map_sum]

private theorem meshWellMap_embed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j→4≤L*|a i-a j|)
    (i : ι) (z : EuclideanSpace ℝ (ι×Fin n)) :
    (meshGeometry s hs a L hL hsep).wellMap i
        (meshEmbed s hs n hn a L hL hsep z) =
      meshCellEmbed s hs n hn (meshBlockMap n i z) := by
  classical
  apply Subtype.ext
  change (meshGeometry s hs a L hL hsep).pieceL2 i
      ((meshEmbed s hs n hn a L hL hsep z : formDomain
        (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1) =
    ((meshCellEmbed s hs n hn (meshBlockMap n i z) : formDomain
      (1+2*s) (lineCell 0 1)) : L2 1)
  rw [meshEmbed_coe, map_sum]
  simp_rw [map_smul]
  rw [show ((meshCellEmbed s hs n hn (meshBlockMap n i z) :
      formDomain (1+2*s) (lineCell 0 1)) : L2 1) =
      ∑ α, (meshBlockMap n i z) α • (meshCellDomain s hs n hn α : L2 1) by
        simp [meshCellEmbed, Submodule.coe_sum, map_sum]]
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : ι, ∑ α : Fin n, z (j,α) •
        (meshGeometry s hs a L hL hsep).pieceL2 i
          ((meshGeometry s hs a L hL hsep).Φ
            (meshCellDomain s hs n hn α) j : L2 1)) =
      ∑ j : ι, if i = j then
        ∑ α : Fin n, z (j,α) • (meshCellDomain s hs n hn α : L2 1)
      else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i=j
        · subst j
          simp only [if_pos rfl]
          apply Finset.sum_congr rfl
          intro α hα
          rw [(meshGeometry s hs a L hL hsep).pieceL2_Φ
            (meshCellDomain s hs n hn α) i i]
          simp
        · rw [if_neg hij]
          apply Finset.sum_eq_zero
          intro α hα
          rw [(meshGeometry s hs a L hL hsep).pieceL2_Φ
            (meshCellDomain s hs n hn α) i j]
          simp [hij]
    _ = ∑ α : Fin n, (meshBlockMap n i z) α •
          (meshCellDomain s hs n hn α : L2 1) := by
          simp [meshBlockMap]

private theorem meshBlockQ0_eq_GQ0 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (c : ℝ) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j→4≤L*|a i-a j|)
    (z : EuclideanSpace ℝ (ι×Fin n)) :
    meshBlockQ0 (oneWellGalerkin c s n) z =
      (meshGeometry s hs a L hL hsep).Q0 c
        (meshEmbed s hs n hn a L hL hsep z) := by
  classical
  simp only [meshBlockQ0, WellGeometry.Q0, QuadraticMap.comp_apply,
    FunLike.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [meshWellMap_embed]
  exact (meshCellQ_eq_matrixQ c s hs n hn
    (meshBlockMap n i z)).symm

private theorem meshFormQ_eq_matrixQ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (c : ℝ) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j→4≤L*|a i-a j|)
    (z : EuclideanSpace ℝ (ι×Fin n)) :
    formQ c (1+2*s) (meshGeometry s hs a L hL hsep).Ω
        (meshEmbed s hs n hn a L hL hsep z) =
      meshMatrixQ (multiWellGalerkin c s n a L) z := by
  classical
  let G := meshGeometry s hs a L hL hsep
  let e : ι×Fin n → formDomain (1+2*s) G.Ω :=
    fun p => G.Φ (meshCellDomain s hs n hn p.2) p.1
  have hrepr : meshEmbed s hs n hn a L hL hsep z = ∑ p, z p • e p := by
    rfl
  calc
    formQ c (1+2*s) G.Ω (meshEmbed s hs n hn a L hL hsep z) =
        QuadraticMap.polar (formQ c (1+2*s) G.Ω)
          (∑ p, z p • e p) (∑ q, z q • e q) / 2 := by
            rw [← meshAssociated_self, meshAssociated_diag, hrepr]
    _ = (∑ p, ∑ q, z p * z q *
          QuadraticMap.polar (formQ c (1+2*s) G.Ω) (e p) (e q)) / 2 := by
          rw [meshPolar_sum]
    _ = ∑ p, ∑ q, z p * z q * multiWellGalerkin c s n a L p q := by
          have hentry (p q : ι×Fin n) :
              QuadraticMap.polar (formQ c (1+2*s) G.Ω) (e p) (e q) / 2 =
                multiWellGalerkin c s n a L p q := by
            have h := formBilin_eq_polar c (1+2*s) G.Ω (e p) (e q)
            have hp := meshTranslate_cell s hs n hn a L hL hsep p.1 p.2
            have hq := meshTranslate_cell s hs n hn a L hL hsep q.1 q.2
            rw [hp, hq] at h
            simpa [multiWellGalerkin] using h.symm
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro q hq
          calc
            z p * z q *
                QuadraticMap.polar (formQ c (1+2*s) G.Ω) (e p) (e q) / 2 =
              z p * z q *
                (QuadraticMap.polar (formQ c (1+2*s) G.Ω) (e p) (e q) / 2) := by ring
            _ = z p * z q * multiWellGalerkin c s n a L p q := by rw [hentry]
    _ = meshMatrixQ (multiWellGalerkin c s n a L) z :=
          (meshMatrixQ_sum _ _).symm


private theorem meshMatrixQ_polar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x y : EuclideanSpace ℝ ι) :
    QuadraticMap.polar (meshMatrixQ A) x y =
      2 * inner ℝ (Matrix.toEuclideanLin A x) y := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [QuadraticMap.polar, meshMatrixQ_inner, meshMatrixQ_inner,
    meshMatrixQ_inner]
  simp only [map_add, inner_add_left, inner_add_right]
  have hcross :
      inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap y) x =
        inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap x) y := by
    change inner ℝ (Matrix.toEuclideanLin A y) x =
      inner ℝ (Matrix.toEuclideanLin A x) y
    calc
      inner ℝ (Matrix.toEuclideanLin A y) x =
          inner ℝ x (Matrix.toEuclideanLin A y) := real_inner_comm _ _
      _ = inner ℝ (Matrix.toEuclideanLin A x) y := (hsym x y).symm
  rw [hcross]
  simp only [LinearMap.coe_toContinuousLinearMap']
  ring

private theorem meshMatrixQ_lower_on_orthogonal {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hcard : 2 ≤ Fintype.card ι)
    (φ x : EuclideanSpace ℝ ι)
    (hφnorm : ‖φ‖ = 1)
    (hgap : hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩) <
      hA.eigenvalues₀ (Fin.rev ⟨1, by omega⟩))
    (hφeig : Matrix.toEuclideanLin A φ =
      hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩) • φ)
    (horth : inner ℝ φ x = 0) :
    hA.eigenvalues₀ (Fin.rev ⟨1, by omega⟩) * ‖x‖ ^ 2 ≤ meshMatrixQ A x := by
  classical
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := Matrix.toEuclideanLin A
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι :=
    finrank_euclideanSpace
  let b : OrthonormalBasis (Fin (Fintype.card ι)) ℝ
      (EuclideanSpace ℝ ι) := hT.eigenvectorBasis hdim
  let k0 : Fin (Fintype.card ι) := Fin.rev ⟨0, by omega⟩
  let k1 : Fin (Fintype.card ι) := Fin.rev ⟨1, by omega⟩
  have hEval (j : Fin (Fintype.card ι)) :
      hT.eigenvalues hdim j = hA.eigenvalues₀ j := rfl
  have hB (j : Fin (Fintype.card ι)) :
      T (b j) = hA.eigenvalues₀ j • b j := by
    simpa [T, b, hEval j] using hT.apply_eigenvectorBasis hdim j
  have hindex (j : Fin (Fintype.card ι)) (hjk : j ≠ k0) : j ≤ k1 := by
    apply Fin.le_iff_val_le_val.mpr
    have hk0 : k0.val = Fintype.card ι - 1 := rfl
    have hk1 : k1.val = Fintype.card ι - 2 := rfl
    omega
  have hlow (j : Fin (Fintype.card ι)) (hjk : j ≠ k0) :
      hA.eigenvalues₀ k1 ≤ hA.eigenvalues₀ j :=
    hA.eigenvalues₀_antitone (hindex j hjk)
  have hcoefzero (j : Fin (Fintype.card ι)) (hjk : j ≠ k0) :
      inner ℝ (b j) φ = 0 := by
    have hs := hT φ (b j)
    rw [hφeig, hB j] at hs
    have heq : hA.eigenvalues₀ k0 * inner ℝ φ (b j) =
        hA.eigenvalues₀ j * inner ℝ φ (b j) := by
      simpa [real_inner_smul_left, real_inner_smul_right] using hs
    have hstrict : hA.eigenvalues₀ k0 < hA.eigenvalues₀ j := by
      exact lt_of_lt_of_le hgap (hlow j hjk)
    have hprod : (hA.eigenvalues₀ j - hA.eigenvalues₀ k0) *
        inner ℝ φ (b j) = 0 := by
      nlinarith [heq]
    have hneq : hA.eigenvalues₀ j - hA.eigenvalues₀ k0 ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt hstrict)
    have hz := (mul_eq_zero.mp hprod).resolve_left hneq
    rw [real_inner_comm]
    exact hz
  have hcoef0 : inner ℝ φ (b k0) ≠ 0 := by
    have hparse :
        1 = ∑ j, inner ℝ φ (b j) * inner ℝ (b j) φ := by
      calc
        1 = inner ℝ φ φ := by
          rw [real_inner_self_eq_norm_sq, hφnorm]
          norm_num
        _ = ∑ j, inner ℝ φ (b j) * inner ℝ (b j) φ :=
          (OrthonormalBasis.sum_inner_mul_inner b φ φ).symm
    have hcollapse :
        (∑ j, inner ℝ φ (b j) * inner ℝ (b j) φ) =
          inner ℝ φ (b k0) * inner ℝ (b k0) φ :=
      Finset.sum_eq_single_of_mem k0 (Finset.mem_univ k0) (by
        intro j hj hjne
        have hz := hcoefzero j hjne
        simp [hz, real_inner_comm])
    rw [hcollapse] at hparse
    intro hz
    have hz' : inner ℝ (b k0) φ = 0 := by
      rw [real_inner_comm]
      exact hz
    rw [hz, hz'] at hparse
    norm_num at hparse
  have hcoefx0 : inner ℝ (b k0) x = 0 := by
    have hexp := OrthonormalBasis.sum_inner_mul_inner b φ x
    rw [horth] at hexp
    have hcollapse :
        (∑ j, inner ℝ φ (b j) * inner ℝ (b j) x) =
          inner ℝ φ (b k0) * inner ℝ (b k0) x :=
      Finset.sum_eq_single_of_mem k0 (Finset.mem_univ k0) (by
        intro j hj hjne
        have hz : inner ℝ φ (b j) = 0 := by
          rw [real_inner_comm]
          exact hcoefzero j hjne
        simp [hz])
    rw [hcollapse] at hexp
    have hprod : inner ℝ φ (b k0) * inner ℝ (b k0) x = 0 := by
      simpa using hexp.symm
    exact (mul_eq_zero.mp hprod).resolve_left hcoef0
  have hEnergy :
      meshMatrixQ A x =
        ∑ j, hA.eigenvalues₀ j * inner ℝ (b j) x * inner ℝ (b j) x := by
    rw [meshMatrixQ_inner]
    calc
      inner ℝ (T x) x =
          ∑ j, inner ℝ (T x) (b j) * inner ℝ (b j) x :=
        (OrthonormalBasis.sum_inner_mul_inner b (T x) x).symm
      _ = ∑ j, hA.eigenvalues₀ j *
          inner ℝ (b j) x * inner ℝ (b j) x := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hT x (b j), hB j, inner_smul_right, real_inner_comm x (b j)]
  have hNorm :
      ‖x‖ ^ 2 = ∑ j, inner ℝ (b j) x * inner ℝ (b j) x := by
    calc
      ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
      _ = ∑ j, inner ℝ x (b j) * inner ℝ (b j) x :=
        (OrthonormalBasis.sum_inner_mul_inner b x x).symm
      _ = ∑ j, inner ℝ (b j) x * inner ℝ (b j) x := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [real_inner_comm x (b j)]
  have hterm (j : Fin (Fintype.card ι)) :
      hA.eigenvalues₀ k1 * inner ℝ (b j) x * inner ℝ (b j) x ≤
        hA.eigenvalues₀ j * inner ℝ (b j) x * inner ℝ (b j) x := by
    by_cases hj : j = k0
    · subst j
      simp [hcoefx0]
    · have hle := hlow j hj
      have hsquare : 0 ≤ (inner ℝ (b j) x) ^ 2 := sq_nonneg _
      calc
        hA.eigenvalues₀ k1 * inner ℝ (b j) x * inner ℝ (b j) x =
            hA.eigenvalues₀ k1 * (inner ℝ (b j) x) ^ 2 := by ring
        _ ≤ hA.eigenvalues₀ j * (inner ℝ (b j) x) ^ 2 :=
          mul_le_mul_of_nonneg_right hle hsquare
        _ = hA.eigenvalues₀ j * inner ℝ (b j) x * inner ℝ (b j) x := by ring
  calc
    hA.eigenvalues₀ k1 * ‖x‖ ^ 2 =
        ∑ j, hA.eigenvalues₀ k1 *
          inner ℝ (b j) x * inner ℝ (b j) x := by
      rw [hNorm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ j, hA.eigenvalues₀ j *
          inner ℝ (b j) x * inner ℝ (b j) x :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = meshMatrixQ A x := hEnergy.symm


private def meshGroundVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (φ : Fin n → ℝ) (i : ι) :
    EuclideanSpace ℝ (ι×Fin n) :=
  WithLp.toLp 2 (fun p : ι×Fin n => if p.1 = i then φ p.2 else 0)

private theorem meshGround_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (φ : Fin n → ℝ) (i : ι)
    (z : EuclideanSpace ℝ (ι×Fin n)) :
    inner ℝ (meshGroundVector n φ i) z =
      inner ℝ (WithLp.toLp 2 φ) (meshBlockMap n i z) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [meshGroundVector, meshBlockMap, Fintype.sum_prod_type, eq_comm]

private theorem meshGround_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (φ : Fin n → ℝ) (hφ : ∑ α, φ α ^ 2 = 1) :
    Orthonormal ℝ (fun i : ι => meshGroundVector n φ i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i=j
  · subst j
    rw [PiLp.inner_apply]
    simp [meshGroundVector, Fintype.sum_prod_type, hφ]
  · rw [PiLp.inner_apply]
    simp [meshGroundVector, Fintype.sum_prod_type, hij, eq_comm]

private noncomputable def meshPhi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (φ : Fin n → ℝ) :
    formDomain (1+2*s) (lineCell 0 1) :=
  meshCellEmbed s hs n hn (WithLp.toLp 2 φ)

private theorem meshEmbed_ground {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L) (hsep : ∀ i j, i≠j→4≤L*|a i-a j|)
    (φ : Fin n → ℝ) (i : ι) :
    meshEmbed s hs n hn a L hL hsep (meshGroundVector (ι := ι) n φ i) =
      (meshGeometry s hs a L hL hsep).Φ (meshPhi (ι := ι) s hs n hn φ) i := by
  classical
  apply Subtype.ext
  change ((meshEmbed s hs n hn a L hL hsep
      (meshGroundVector (ι := ι) n φ i) : formDomain
        (1+2*s) (meshGeometry s hs a L hL hsep).Ω) : L2 1) =
      translateL2 (L • linePoint (a i))
        ((meshPhi (ι := ι) s hs n hn φ : formDomain
          (1+2*s) (lineCell 0 1)) : L2 1)
  have hphiCoe :
      ((meshPhi (ι := ι) s hs n hn φ : formDomain
          (1+2*s) (lineCell 0 1)) : L2 1) =
        ∑ α, φ α • (meshCellDomain s hs n hn α : L2 1) := by
    simp [meshPhi, meshCellEmbed, Submodule.coe_sum, map_sum]
  rw [meshEmbed_coe, hphiCoe, map_sum]
  have htrans (α : Fin n) :
      translateL2 (L • linePoint (a i))
          (φ α • (meshCellDomain s hs n hn α : L2 1)) =
        φ α • cellVec (L*a i+meshCenter n α) (1/n) := by
    change translateL2 (L • linePoint (a i))
        (φ α • cellVec (meshCenter n α) (1/n)) = _
    rw [map_smul, linePoint_smul, cellVec_translate]
  simp_rw [htrans]
  simp_rw [meshTranslate_cell]
  rw [Fintype.sum_prod_type]
  simp only [meshGroundVector]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j hj hji
    simp [hji]


private theorem meshQuadraticMap_polar_sum {α M : Type*} [DecidableEq α]
    [AddCommGroup M] [Module ℝ M]
    (f : α → QuadraticMap ℝ M ℝ) (s : Finset α) (x y : M) :
    QuadraticMap.polar (s.sum f : QuadraticMap ℝ M ℝ) x y =
      s.sum (fun i => QuadraticMap.polar (f i) x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [QuadraticMap.polar]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, FunLike.coe_add, QuadraticMap.polar_add, ih,
        Finset.sum_insert hi]

private theorem meshQuadraticMap_polar_comp {M N : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (Q : QuadraticMap ℝ N ℝ) (f : M →ₗ[ℝ] N) (x y : M) :
    QuadraticMap.polar (Q.comp f) x y =
      QuadraticMap.polar Q (f x) (f y) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply]
  rw [f.map_add]

private theorem meshBlockMap_ground {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (φ : Fin n → ℝ) (i j : ι) :
    meshBlockMap n j (meshGroundVector (ι := ι) n φ i) =
      if j=i then WithLp.toLp 2 φ else 0 := by
  by_cases hji : j=i
  · subst j
    ext α
    simp [meshBlockMap, meshGroundVector]
  · ext α
    simp [meshBlockMap, meshGroundVector, hji]

private theorem meshBlockMap_norm_sq_sum {ι : Type*} [Fintype ι]
    [DecidableEq ι] {n : ℕ} (z : EuclideanSpace ℝ (ι×Fin n)) :
    ∑ i : ι, ‖meshBlockMap n i z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp [meshBlockMap, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]

private theorem meshBlockQ0_weak_eigen {ι : Type*} [Fintype ι]
    [DecidableEq ι] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (φ : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hφeig : Matrix.toEuclideanLin A φ = μ • φ)
    (i : ι) (z : EuclideanSpace ℝ (ι×Fin n)) :
    QuadraticMap.polar (meshBlockQ0 (ι := ι) A)
        (meshGroundVector (ι := ι) n φ.ofLp i) z =
      2 * μ * inner ℝ (meshGroundVector (ι := ι) n φ.ofLp i) z := by
  classical
  rw [meshBlockQ0, meshQuadraticMap_polar_sum]
  have hterm (j : ι) :
      QuadraticMap.polar ((meshMatrixQ A).comp (meshBlockMap n j))
        (meshGroundVector (ι := ι) n φ.ofLp i) z =
        if j=i then 2 * μ *
          inner ℝ (meshGroundVector (ι := ι) n φ.ofLp i) z else 0 := by
    rw [meshQuadraticMap_polar_comp, meshBlockMap_ground]
    by_cases hji : j=i
    · subst j
      simp only [if_pos rfl]
      calc
        QuadraticMap.polar (meshMatrixQ A) φ (meshBlockMap n i z) =
            2 * inner ℝ (Matrix.toEuclideanLin A φ) (meshBlockMap n i z) :=
          meshMatrixQ_polar A hA φ (meshBlockMap n i z)
        _ = 2 * μ * inner ℝ φ (meshBlockMap n i z) := by
          rw [hφeig, real_inner_smul_left]
          ring
        _ = 2 * μ *
            inner ℝ (meshGroundVector (ι := ι) n φ.ofLp i) z := by
          rw [meshGround_inner]
    · simp [hji]
  simp_rw [hterm]
  simp

private theorem meshBlockQ0_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hn : 2 ≤ n) (φ : EuclideanSpace ℝ (Fin n))
    (hgap : hA.eigenvalues₀ (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩) <
      hA.eigenvalues₀ (Fin.rev ⟨1, by simp [Fintype.card_fin]; omega⟩))
    (hφnorm : ‖φ‖ = 1)
    (hφeig : Matrix.toEuclideanLin A φ =
      hA.eigenvalues₀ (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩) • φ)
    (z : EuclideanSpace ℝ (ι×Fin n))
    (horth : ∀ i, inner ℝ (meshGroundVector (ι := ι) n φ.ofLp i) z = 0) :
    hA.eigenvalues₀ (Fin.rev ⟨1, by simp [Fintype.card_fin]; omega⟩) * ‖z‖ ^ 2 ≤
      meshBlockQ0 (ι := ι) A z := by
  classical
  let μ1 := hA.eigenvalues₀ (Fin.rev ⟨1, by simp [Fintype.card_fin]; omega⟩)
  have hlocal (i : ι) :
      μ1 * ‖meshBlockMap n i z‖ ^ 2 ≤ meshMatrixQ A (meshBlockMap n i z) :=
    meshMatrixQ_lower_on_orthogonal A hA (by
      simpa [Fintype.card_fin] using hn)
      φ (meshBlockMap n i z) hφnorm hgap hφeig (by
        rw [← meshGround_inner]
        exact horth i)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => hlocal i)
  change μ1 * ‖z‖ ^ 2 ≤ _
  calc
    μ1 * ‖z‖ ^ 2 =
        μ1 * ∑ i : ι, ‖meshBlockMap n i z‖ ^ 2 := by
      rw [meshBlockMap_norm_sq_sum]
    _ = ∑ i : ι, μ1 * ‖meshBlockMap n i z‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i : ι, meshMatrixQ A (meshBlockMap n i z) := hsum
    _ = meshBlockQ0 (ι := ι) A z := by
      simp [meshBlockQ0, FunLike.coe_sum, Finset.sum_apply,
        QuadraticMap.comp_apply]


private noncomputable def meshProfileFun {n : ℕ} (φ : Fin n → ℝ) :
    Eucl 1 → ℝ := fun x =>
  ∑ α : Fin n,
    φ α * ((1 / (n : ℝ)) ^ (-(1 / 2 : ℝ))) *
      (lineCell (meshCenter n α) (1 / (n : ℝ))).indicator (fun _ => (1:ℝ)) x

private theorem meshProfile_coe_ae (s : ℝ) (hs : 0<s ∧ s<1/2)
    (n : ℕ) (hn : 1≤n) (φ : Fin n → ℝ) :
    ((meshPhi (ι := Unit) s hs n hn φ : L2 1) : Eucl 1 → ℝ) =ᵐ[volume]
      meshProfileFun φ := by
  classical
  let h : ℝ := 1 / (n : ℝ)
  let S : Fin n → L2 1 := fun α => φ α • cellVec (meshCenter n α) h
  have hsumL2 : (meshPhi (ι := Unit) s hs n hn φ : L2 1) = ∑ α, S α := by
    simp [meshPhi, meshCellEmbed, meshCellDomain, S, h]
  have hsum :=
    Lp.coeFn_fun_finsetSum (μ := (volume : Measure (Eucl 1)))
      Finset.univ S
  have hsmulAll : ∀ᵐ x ∂(volume : Measure (Eucl 1)), ∀ α,
      (S α : Eucl 1 → ℝ) x =
        φ α * (cellVec (meshCenter n α) h : Eucl 1 → ℝ) x := by
    apply ae_all_iff.2
    intro α
    exact Lp.coeFn_smul (φ α) (cellVec (meshCenter n α) h)
  have hcellAll : ∀ᵐ x ∂(volume : Measure (Eucl 1)), ∀ α,
      (cellVec (meshCenter n α) h : Eucl 1 → ℝ) x =
        h ^ (-(1 / 2 : ℝ)) *
          (lineCell (meshCenter n α) h).indicator (fun _ => (1:ℝ)) x := by
    apply ae_all_iff.2
    intro α
    have hs := Lp.coeFn_smul (h ^ (-(1 / 2 : ℝ)))
      (indicatorConstLp 2 (measurableSet_lineCell (meshCenter n α) h)
        (volume_lineCell_ne_top (meshCenter n α) h) (1:ℝ))
    filter_upwards [hs, indicatorConstLp_coeFn
      (p := 2) (hs := measurableSet_lineCell (meshCenter n α) h)
      (hμs := volume_lineCell_ne_top (meshCenter n α) h) (c := (1:ℝ))] with x hsm hconst
    rw [cellVec]
    calc
      ((h ^ (-(1 / 2 : ℝ)) •
          indicatorConstLp 2 (measurableSet_lineCell (meshCenter n α) h)
            (volume_lineCell_ne_top (meshCenter n α) h) (1:ℝ) : L2 1) : Eucl 1 → ℝ) x =
          h ^ (-(1 / 2 : ℝ)) *
            (indicatorConstLp 2 (measurableSet_lineCell (meshCenter n α) h)
              (volume_lineCell_ne_top (meshCenter n α) h) (1:ℝ) : L2 1) x := by
        rw [hsm]
        rfl
      _ = h ^ (-(1 / 2 : ℝ)) *
          (lineCell (meshCenter n α) h).indicator (fun _ => (1:ℝ)) x := by
        rw [hconst]
  rw [hsumL2]
  filter_upwards [hsum, hsmulAll, hcellAll] with x hsumx hmul hcell
  rw [hsumx]
  simp only [meshProfileFun]
  apply Finset.sum_congr rfl
  intro α hα
  rw [hmul α, hcell α]
  simp only [h]
  ring



private theorem meshProfile_integrable {n : ℕ} (φ : Fin n → ℝ) :
    Integrable (meshProfileFun φ) (volume : Measure (Eucl 1)) := by
  classical
  have hind (α : Fin n) :
      Integrable
        ((lineCell (meshCenter n α) (1 / (n:ℝ))).indicator
          (fun _ : Eucl 1 => (1:ℝ))) (volume : Measure (Eucl 1)) := by
    rw [integrable_indicator_iff (measurableSet_lineCell _ _)]
    exact integrableOn_const
      (volume_lineCell_ne_top (meshCenter n α) (1 / (n:ℝ)))
  unfold meshProfileFun
  apply integrable_finsetSum
  intro α hα
  simpa [mul_assoc] using (hind α).const_mul
    (φ α * ((1 / (n:ℝ)) ^ (-(1/2:ℝ))) )

private theorem meshProfile_nonneg {n : ℕ} (φ : Fin n → ℝ)
    (hφ : ∀ α, 0 ≤ φ α) :
    ∀ x, 0 ≤ meshProfileFun φ x := by
  intro x
  unfold meshProfileFun
  apply Finset.sum_nonneg
  intro α hα
  have hnpos : 0 < n := Nat.zero_lt_of_lt α.isLt
  have hh : 0 < (1 / (n:ℝ)) := by positivity
  have hpow : 0 < ((1 / (n:ℝ)) ^ (-(1/2:ℝ))) :=
    Real.rpow_pos_of_pos hh _
  by_cases hx : x ∈ lineCell (meshCenter n α) (1/(n:ℝ))
  · simp only [Set.indicator_of_mem hx]
    have hφα : 0 ≤ φ α := hφ α
    positivity
  · have hx' : x ∉ lineCell (meshCenter n α) ((n:ℝ)⁻¹) := by
      simpa [one_div] using hx
    simp [Set.indicator, hx']

private theorem meshProfile_support {n : ℕ} (hn : 1≤n) (φ : Fin n → ℝ) :
    ∀ x, meshProfileFun φ x ≠ 0 → ‖x‖ ≤ 1 := by
  intro x hx
  by_contra hnot
  have hxD : x ∉ lineCell 0 1 := by
    intro hxD
    have hcoord : |x 0| < (1:ℝ)/2 := by
      simpa [lineCell] using hxD
    have hsq : ‖x‖^2=(x 0)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp
    have hnorm : ‖x‖ = |x 0| := by
      nlinarith [norm_nonneg x, abs_nonneg (x 0), sq_abs (x 0)]
    have hlt : ‖x‖ < 1 := by rw [hnorm]; linarith
    exact hnot hlt.le
  have hz : meshProfileFun φ x = 0 := by
    unfold meshProfileFun
    apply Finset.sum_eq_zero
    intro α hα
    have hcell : x ∉ lineCell (meshCenter n α) (1/(n:ℝ)) := by
      intro hxcell
      exact hxD (meshCell_subset n hn α hxcell)
    have hcell' : x ∉ lineCell (meshCenter n α) ((n:ℝ)⁻¹) := by
      simpa [one_div] using hcell
    simp [Set.indicator, hcell']
  exact hx hz

private theorem meshProfile_integral {n : ℕ} (hn : 1≤n) (φ : Fin n→ℝ) :
    ∫ x : Eucl 1, meshProfileFun φ x ∂(volume : Measure (Eucl 1)) =
      (1/(n:ℝ))^(1/2:ℝ) * ∑ α, φ α := by
  classical
  let h : ℝ := 1/(n:ℝ)
  have hh : 0<h := by
    dsimp [h]
    apply one_div_pos.mpr
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hvol (α : Fin n) :
      (volume : Measure (Eucl 1)).real (lineCell (meshCenter n α) h) = h := by
    change ((volume : Measure (Eucl 1))
      (lineCell (meshCenter n α) h)).toReal = h
    rw [volume_lineCell (meshCenter n α) h hh.le, ENNReal.toReal_ofReal hh.le]
  have htermint (α : Fin n) :
      Integrable
        (fun x : Eucl 1 => (φ α * h^(-(1/2:ℝ))) *
          (lineCell (meshCenter n α) h).indicator (fun _ => (1:ℝ)) x)
        (volume : Measure (Eucl 1)) := by
    have hind : Integrable
        ((lineCell (meshCenter n α) h).indicator
          (fun _ : Eucl 1 => (1:ℝ))) (volume : Measure (Eucl 1)) := by
      rw [integrable_indicator_iff (measurableSet_lineCell _ _)]
      exact integrableOn_const (volume_lineCell_ne_top _ _)
    exact hind.const_mul _
  calc
    ∫ x : Eucl 1, meshProfileFun φ x ∂(volume : Measure (Eucl 1)) =
        ∑ α : Fin n,
          ∫ x : Eucl 1, (φ α * h^(-(1/2:ℝ))) *
            (lineCell (meshCenter n α) h).indicator (fun _ => (1:ℝ)) x
              ∂(volume : Measure (Eucl 1)) := by
      unfold meshProfileFun
      rw [integral_finsetSum Finset.univ (fun α hα => htermint α)]
    _ = ∑ α : Fin n, (φ α * h^(-(1/2:ℝ))) * h := by
      apply Finset.sum_congr rfl
      intro α hα
      rw [integral_const_mul]
      rw [integral_indicator_const (1:ℝ) (measurableSet_lineCell _ _), hvol]
      simp
    _ = h^(1/2:ℝ) * ∑ α : Fin n, φ α := by
      have hrpow : h^(-(1/2:ℝ))*h = h^(1/2:ℝ) := by
        calc
          h^(-(1/2:ℝ))*h = h^(-(1/2:ℝ))*h^(1:ℝ) := by
            congr 1
            exact (Real.rpow_one h).symm
          _ = h^((-(1/2:ℝ))+1) := by rw [← Real.rpow_add hh]
          _ = h^(1/2:ℝ) := by congr 1 <;> norm_num
      calc
        ∑ α : Fin n, φ α * h^(-(1/2:ℝ)) * h =
            ∑ α : Fin n, h^(1/2:ℝ) * φ α := by
              apply Finset.sum_congr rfl
              intro α hα
              calc
                φ α * h^(-(1/2:ℝ)) * h =
                    φ α * (h^(-(1/2:ℝ))*h) := by ring
                _ = φ α * h^(1/2:ℝ) := by rw [hrpow]
                _ = h^(1/2:ℝ) * φ α := by ring
        _ = h^(1/2:ℝ) * ∑ α : Fin n, φ α :=
          (Finset.mul_sum _ _ _).symm
    _ = (1/(n:ℝ))^(1/2:ℝ) * ∑ α, φ α := by rfl


private theorem meshKernelPairing_congr_ae (K : Eucl 1 → Eucl 1 → ℝ)
    (u v : Eucl 1 → ℝ) (h : u =ᵐ[volume] v) :
    kernelCrossPairing K (volume : Measure (Eucl 1)) u u =
      kernelCrossPairing K (volume : Measure (Eucl 1)) v v := by
  unfold kernelCrossPairing
  have hf := (MeasureTheory.Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (Eucl 1))) (ν := (volume : Measure (Eucl 1)))).ae_eq_comp h
  have hs := (MeasureTheory.Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Eucl 1))) (ν := (volume : Measure (Eucl 1)))).ae_eq_comp h
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hf, hs] with z hz₁ hz₂
  have hz₁' : u z.1 = v z.1 := by simpa only [Function.comp_apply] using hz₁
  have hz₂' : u z.2 = v z.2 := by simpa only [Function.comp_apply] using hz₂
  rw [hz₁', hz₂']

private theorem meshCompression_congr_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ c L : ℝ) (a : ι → Eucl 1) (u v : Eucl 1 → ℝ)
    (h : u =ᵐ[volume] v) :
    multiWellCompressionMatrix (volume : Measure (Eucl 1)) κ c u a L =
      multiWellCompressionMatrix (volume : Measure (Eucl 1)) κ c v a L := by
  classical
  ext i j
  by_cases hij : i=j
  · simp [multiWellCompressionMatrix, hij]
  · simp only [multiWellCompressionMatrix_apply, if_neg hij]
    have hk := meshKernelPairing_congr_ae
      (multiWellCrossKernel κ ((L:ℝ) • (a i-a j))) u v h
    rw [hk]

private theorem effectiveInteractionMatrix_linePoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (c m κ : ℝ) :
    effectiveInteractionMatrix (fun i => linePoint (a i)) c m κ =
      effectiveInteractionMatrix a c m κ := by
  classical
  ext i j
  by_cases hij : i=j
  · simp [effectiveInteractionMatrix, hij]
  · simp only [effectiveInteractionMatrix_apply, if_neg hij]
    rw [linePoint_sub_norm]
    simp [Real.norm_eq_abs]

private theorem linePoint_injective : Function.Injective linePoint := by
  intro t u h
  have h0 := congrArg (fun x : Eucl 1 => x 0) h
  simpa [linePoint] using h0


private theorem meshLevel_eq_multiWell_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c s : ℝ) (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 1≤n)
    (a : ι→ℝ) (L : ℝ) (hL : 0<L)
    (hsep : ∀ i j, i≠j → 4≤L*|a i-a j|)
    (hH : (multiWellGalerkin c s n a L).IsHermitian)
    (k : Fin (Fintype.card (ι×Fin n))) :
    MinMax.level
      ((formQ c (1+2*s) (meshGeometry s hs a L hL hsep).Ω).comp
        (meshEmbed s hs n hn a L hL hsep)) k.val =
      hH.eigenvalues₀ (Fin.rev k) := by
  classical
  let E := EuclideanSpace ℝ (ι×Fin n)
  let b : OrthonormalBasis (ι×Fin n) ℝ E :=
    EuclideanSpace.basisFun (ι×Fin n) ℝ
  let e : ι×Fin n → E := b
  have he : Orthonormal ℝ e := b.orthonormal
  have hspan : Submodule.span ℝ (Set.range e) = ⊤ := by
    simpa [e] using b.toBasis.span_eq
  have hQeq :
      ((formQ c (1+2*s) (meshGeometry s hs a L hL hsep).Ω).comp
        (meshEmbed s hs n hn a L hL hsep)) = meshMatrixQ
          (multiWellGalerkin c s n a L) := by
    ext z
    exact meshFormQ_eq_matrixQ s hs c n hn a L hL hsep z
  have hsym : (multiWellGalerkin c s n a L).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp hH
  have hcoord (p q : ι×Fin n) :
      (Matrix.toEuclideanLin (multiWellGalerkin c s n a L) (b p)) q =
        multiWellGalerkin c s n a L q p := by
    rw [Matrix.toEuclideanLin_apply,
      EuclideanSpace.basisFun_apply (ι×Fin n) ℝ p]
    simp [Matrix.mulVec_apply_eq_sum, PiLp.ofLp_single, Pi.single_apply]
  have hinner (p q : ι×Fin n) :
      inner ℝ (Matrix.toEuclideanLin (multiWellGalerkin c s n a L) (b p)) (b q) =
        multiWellGalerkin c s n a L q p := by
    calc
      inner ℝ (Matrix.toEuclideanLin (multiWellGalerkin c s n a L) (b p)) (b q) =
          inner ℝ (Matrix.toEuclideanLin (multiWellGalerkin c s n a L) (b p))
            (EuclideanSpace.basisFun (ι×Fin n) ℝ q) := rfl
      _ = (Matrix.toEuclideanLin (multiWellGalerkin c s n a L) (b p)) q :=
        EuclideanSpace.inner_basisFun_real (ι×Fin n)
          (Matrix.toEuclideanLin (multiWellGalerkin c s n a L) (b p)) q
      _ = multiWellGalerkin c s n a L q p := hcoord p q
  have hAe (p q : ι×Fin n) :
      multiWellGalerkin c s n a L p q =
        QuadraticMap.polar
          ((formQ c (1+2*s) (meshGeometry s hs a L hL hsep).Ω).comp
            (meshEmbed s hs n hn a L hL hsep))
          (e p) (e q) / 2 := by
    rw [hQeq, meshMatrixQ_polar (multiWellGalerkin c s n a L) hH]
    change multiWellGalerkin c s n a L p q =
      2 * inner ℝ
        (Matrix.toEuclideanLin (multiWellGalerkin c s n a L) (b p)) (b q) / 2
    rw [hinner]
    calc
      multiWellGalerkin c s n a L p q =
          multiWellGalerkin c s n a L q p := hsym.apply q p
      _ = 2 * multiWellGalerkin c s n a L q p / 2 := by ring
  exact MinMax.level_eq_eigenvalues₀
    ((formQ c (1+2*s) (meshGeometry s hs a L hL hsep).Ω).comp
      (meshEmbed s hs n hn a L hL hsep))
    e he hspan (multiWellGalerkin c s n a L) hAe hH k

private theorem formBilin_symm (c κ : ℝ) (u v : L2 1) :
    formBilin c κ u v = formBilin c κ v u := by
  unfold formBilin
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  ring

theorem oneWellGalerkin_isHermitian (c s : ℝ) (n : ℕ) :
    (oneWellGalerkin c s n).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  refine Matrix.IsSymm.ext ?_
  intro α β
  simp only [oneWellGalerkin, Matrix.of_apply]
  exact formBilin_symm c (1+2*s) _ _

theorem multiWellGalerkin_isHermitian {ι : Type*} [Fintype ι]
    (c s : ℝ) (n : ℕ) (a : ι → ℝ) (L : ℝ) :
    (multiWellGalerkin c s n a L).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  refine Matrix.IsSymm.ext ?_
  intro p q
  simp only [multiWellGalerkin, Matrix.of_apply]
  exact formBilin_symm c (1+2*s) _ _

private theorem oneWell_offdiag_neg (c s : ℝ) (hc : 0<c)
    (hs : 0<s ∧ s<1/2) (n : ℕ) (hn : 2≤n)
    (α β : Fin n) (hab : α ≠ β) :
    oneWellGalerkin c s n α β < 0 := by
  have hnpos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hh : (0:ℝ)<(1:ℝ)/n := one_div_pos.mpr hnpos
  have hhcast : (1:ℝ)≤n := by exact_mod_cast (Nat.le_of_lt (by omega : 1<n))
  have hr : (1:ℝ)/n ≤ |meshCenter n α-meshCenter n β| :=
    meshCenter_separated n (by omega) α β hab
  have hq0 : 0 < 1-2*s := by linarith
  have hq1 : 1-2*s < 1 := by linarith
  let r : ℝ := |meshCenter n α-meshCenter n β|
  have hconc :
      (r-1/n)^(1-2*s) + (r+1/n)^(1-2*s) < 2*r^(1-2*s) := by
    have hx : 0 ≤ r-1/n := by dsimp [r]; linarith
    have hy : 0 ≤ r+1/n := by positivity
    have hxy : r-1/n ≠ r+1/n := by
      intro heq
      have : (1:ℝ)/n = 0 := by linarith
      linarith
    have hsconc := (Real.strictConcaveOn_rpow hq0 hq1).2
      (show r-1/n ∈ Set.Ici (0:ℝ) from hx)
      (show r+1/n ∈ Set.Ici (0:ℝ) from hy)
      hxy (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (1/2:ℝ)+(1/2)=1)
    have hmid : (1/2:ℝ)*(r-1/n)+(1/2)*(r+1/n)=r := by ring
    have hsconc' :
        (1/2:ℝ)*(r-1/n)^(1-2*s) + (1/2)*(r+1/n)^(1-2*s) <
          r^(1-2*s) := by
      change (1/2:ℝ)*(r-1/n)^(1-2*s) + (1/2)*(r+1/n)^(1-2*s) <
        ((1/2:ℝ)*(r-1/n)+(1/2)*(r+1/n))^(1-2*s) at hsconc
      rw [hmid] at hsconc
      exact hsconc
    nlinarith [hsconc']
  have hden : 0 < 2*s*(1-2*s) := mul_pos (mul_pos (by norm_num) hs.1) hq0
  have hnum : 0 <
      2*r^(1-2*s) - (r+1/n)^(1-2*s) - (r-1/n)^(1-2*s) := by
    linarith
  have hentry := cellMatrix_offdiag c s hs (meshCenter n α) (meshCenter n β)
    (1/n) hh (by simpa [r] using hr)
  have heq : oneWellGalerkin c s n α β =
      formBilin c (1+2*s) (cellVec (meshCenter n α) (1/n))
        (cellVec (meshCenter n β) (1/n)) := by
    rfl
  rw [heq,hentry]
  have hpos : 0 < c/(1/n) := div_pos hc hh
  have hratio : 0 <
      (2*r^(1-2*s)-(r+1/n)^(1-2*s)-(r-1/n)^(1-2*s))/(2*s*(1-2*s)) :=
    div_pos hnum hden
  have hrabs : |meshCenter n α-meshCenter n β| = r := rfl
  rw [hrabs]
  nlinarith [mul_pos hpos hratio]





set_option maxHeartbeats 1000000 in
private theorem fixedMesh_cluster_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (c s : ℝ) (hc : 0<c) (hs : 0<s ∧ s<1/2)
    (n : ℕ) (hn : 1≤n) (hn2 : 2≤n)
    (a : ι→ℝ) (ha : Function.Injective a)
    (hA : (oneWellGalerkin c s n).IsHermitian)
    (φE : EuclideanSpace ℝ (Fin n))
    (hφpos : ∀ α, 0<φE.ofLp α) (hφnorm : ‖φE‖=1)
    (hφeig : Matrix.toEuclideanLin (oneWellGalerkin c s n) φE =
      hA.eigenvalues₀ (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩) • φE)
    (hgap : hA.eigenvalues₀ (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩) <
      hA.eigenvalues₀ (Fin.rev ⟨1, by simp [Fintype.card_fin]; omega⟩)) :
    let μ := hA.eigenvalues₀ (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩)
    ∃ C L₁ : ℝ, ∀ L : ℝ, L₁≤L → ∀ k : Fin (Fintype.card ι),
      |(multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
          (Fin.rev ⟨k.val, by
            have hk := k.isLt
            rw [Fintype.card_prod, Fintype.card_fin]
            nlinarith⟩) -
        (μ + L ^ (-(1+2*s)) *
          effectiveInteractionTheta a c
            ((1/(n:ℝ))^(1/2:ℝ) * ∑ α, φE.ofLp α) (1+2*s) k)| ≤
        C * (L ^ (-3-2*s) + L ^ (-2-4*s)) := by
  classical
  let κ : ℝ := 1+2*s
  let μ : ℝ := hA.eigenvalues₀ (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩)
  let μ₂ : ℝ := hA.eigenvalues₀ (Fin.rev ⟨1, by simp [Fintype.card_fin]; omega⟩)
  let g : ℝ := μ₂-μ
  let φ : Fin n → ℝ := φE.ofLp
  have hnormSum : ∑ α : Fin n, φ α ^ 2 = 1 := by
    calc
      ∑ α : Fin n, φ α ^ 2 = ‖φE‖ ^ 2 := by
        simpa [φ] using (EuclideanSpace.real_norm_sq_eq φE).symm
      _ = 1 := by rw [hφnorm]; norm_num
  have hg : 0<g := by dsimp [g,μ,μ₂]; exact sub_pos.mpr hgap
  let sites : ι→Eucl 1 := fun i => linePoint (a i)
  have hne : ∀ i j : ι, i≠j → sites i ≠ sites j := by
    intro i j hij heq
    apply hij
    apply ha
    exact linePoint_injective heq
  let m : ℝ := (1/(n:ℝ))^(1/2:ℝ) * ∑ α, φ α
  have hsumpos : 0 < ∑ α : Fin n, φ α := by
    let α₀ : Fin n := ⟨0, by omega⟩
    have hle : φ α₀ ≤ ∑ α : Fin n, φ α :=
      Finset.single_le_sum (s := Finset.univ)
        (fun α hα => le_of_lt (hφpos α)) (Finset.mem_univ α₀)
    exact lt_of_lt_of_le (hφpos α₀) hle
  have hwidth : 0 < (1/(n:ℝ))^(1/2:ℝ) := by
    apply Real.rpow_pos_of_pos
    apply one_div_pos.mpr
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hm : 0<m := by dsimp [m]; exact mul_pos hwidth hsumpos
  have hvolD : (volume : Measure (Eucl 1)).real (lineCell 0 1) = 1 := by
    change ((volume : Measure (Eucl 1)) (lineCell 0 1)).toReal = 1
    rw [volume_lineCell 0 1 (by norm_num : (0:ℝ)≤1),
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1)]
  let A : TwoWellConstants :=
    { d := 1
      s := s
      hs := ⟨hs.1, by linarith [hs.2]⟩
      kappa := κ
      hkappa := by dsimp [κ]; norm_num
      c := c
      hc := hc
      R := 1
      hR := by norm_num
      volumeD := 1
      hvolumeD := by norm_num
      mu1 := μ
      mu2 := μ₂
      hgap := hg
      phiMass := m
      hphiMass := hm }
  have hcond := multiWellCondition_eventually A sites hne
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hcond
  let γc : ℝ := c * 2^κ * sigmaKappa sites κ
  let εc : ℝ := c * A.C * m^2 * sigmaKappa sites (κ+2)
  let C : ℝ := εc + 2*γc^2/g
  refine ⟨C, L₁, ?_⟩
  intro L hL k
  have hconditions := hL₁ L hL
  have hLpos : 0<L := hconditions.1
  have hsepSite : ∀ i j : ι, i≠j → 4*A.R ≤ L*‖sites i-sites j‖ :=
    hconditions.2.1
  have hsmall : multiWellGamma A sites L ≤ A.gap/4 := hconditions.2.2
  have hsep : ∀ i j, i≠j → 4≤L*|a i-a j| := by
    intro i j hij
    have h := hsepSite i j hij
    dsimp [A] at h
    rw [linePoint_sub_norm] at h
    nlinarith
  let G := meshGeometry s hs a L hLpos hsep
  let U := meshEmbed s hs n hn a L hLpos hsep
  let ψ : ι→EuclideanSpace ℝ (ι×Fin n) := fun i =>
    meshGroundVector n φ i
  have hψ : Orthonormal ℝ ψ := meshGround_orthonormal n φ hnormSum
  let Q₀ : QuadraticMap ℝ (EuclideanSpace ℝ (ι×Fin n)) ℝ :=
    meshBlockQ0 (oneWellGalerkin c s n)
  let Q : QuadraticMap ℝ (EuclideanSpace ℝ (ι×Fin n)) ℝ :=
    (formQ c κ G.Ω).comp U
  let w : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (ι×Fin n)) :=
    (G.interaction c).comp U U
  have hQ : ∀ z, Q z = Q₀ z + w z z := by
    intro z
    change formQ c κ G.Ω (U z) =
      meshBlockQ0 (oneWellGalerkin c s n) z + (G.interaction c) (U z) (U z)
    rw [G.formQ_eq c (U z)]
    rw [← meshBlockQ0_eq_GQ0 s hs c n hn a L hLpos hsep z]
  have hwsymm : ∀ x y, w x y = w y x := by
    intro x y
    change (G.interaction c) (U x) (U y) =
      (G.interaction c) (U y) (U x)
    exact G.interaction_symm c (U x) (U y)
  have hvolD' : (volume : Measure (Eucl 1)).real G.D = 1 := by
    simpa [G, meshGeometry] using hvolD
  have hgammaEq : multiWellGamma A sites L =
      c*2^κ * 1 * sigmaKappa sites κ * L^(-κ) := by
    simp [multiWellGamma, A, sites, κ]
  have hwb : ∀ x y, |w x y| ≤ multiWellGamma A sites L * ‖x‖ * ‖y‖ := by
    intro x y
    change |(G.interaction c) (U x) (U y)| ≤ _
    have hi := G.abs_interaction_le c hc.le (U x) (U y)
    have hnx : ‖((U x : formDomain κ G.Ω) : L2 1)‖ = ‖x‖ := by
      simpa [U, G, meshGeometry] using meshEmbed_norm s hs n hn a L hLpos hsep x
    have hny : ‖((U y : formDomain κ G.Ω) : L2 1)‖ = ‖y‖ := by
      simpa [U, G, meshGeometry] using meshEmbed_norm s hs n hn a L hLpos hsep y
    rw [hnx, hny] at hi
    have hv : (volume G.D).toReal = 1 := hvolD'
    rw [hv] at hi
    rw [hgammaEq]
    simpa [G, meshGeometry, sites, κ] using hi
  have hheig : ∀ i (z : EuclideanSpace ℝ (ι×Fin n)),
      QuadraticMap.polar Q₀ (ψ i) z =
        2*μ*inner ℝ (ψ i) z := by
    intro i z
    simpa [Q₀, ψ, φ, μ] using
      meshBlockQ0_weak_eigen (oneWellGalerkin c s n) hA φE μ hφeig i z
  have hqgap : ∀ z, (∀ i, inner ℝ (ψ i) z=0) →
      (μ+g)*‖z‖^2 ≤ Q₀ z := by
    intro z horth
    have horth' : ∀ i,
        inner ℝ (meshGroundVector n φE.ofLp i) z = 0 := by
      intro i
      simpa [φ] using horth i
    have hgap' := meshBlockQ0_gap (ι:=ι) (oneWellGalerkin c s n) hA
      hn2 φE hgap hφnorm hφeig z horth'
    simpa [Q₀, μ, g, μ₂] using hgap'
  have hdimN : Fintype.card ι + 1 ≤ Fintype.card ι * n := by
    have hcard : 1≤Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
    have hadd : Fintype.card ι + 1 ≤ Fintype.card ι + Fintype.card ι :=
      Nat.add_le_add_left hcard _
    calc
      Fintype.card ι + 1 ≤ Fintype.card ι + Fintype.card ι := hadd
      _ = Fintype.card ι * 2 := by omega
      _ ≤ Fintype.card ι * n := Nat.mul_le_mul_left _ hn2
  have hdimfull :
      ∃ W : Submodule ℝ (EuclideanSpace ℝ (ι×Fin n)),
        Module.finrank ℝ W = Fintype.card ι * n := by
    refine ⟨⊤, ?_⟩
    simp [Fintype.card_prod, Fintype.card_fin]
  have hdim := MinMax.exists_finrank_of_le hdimN hdimfull
  let φhat : formDomain κ G.D := meshPhi (ι := ι) s hs n hn φ
  have hprofAE :
      ((φhat : L2 1) : Eucl 1 → ℝ) =ᵐ[volume] meshProfileFun φ := by
    simpa [φhat, G, meshGeometry, φ, meshPhi] using (meshProfile_coe_ae s hs n hn φ)
  have hmass : ∫ x : Eucl 1, meshProfileFun φ x ∂(volume : Measure (Eucl 1)) = m := by
    simpa [m, φ] using meshProfile_integral hn φ
  have hsupp : ∀ x, meshProfileFun φ x ≠ 0 → ‖x‖ ≤ A.R := by
    simpa [A] using meshProfile_support hn φ
  have hint : Integrable (meshProfileFun φ) (volume : Measure (Eucl 1)) :=
    meshProfile_integrable φ
  have hnonneg : ∀ x, 0≤meshProfileFun φ x :=
    meshProfile_nonneg φ (fun α => (hφpos α).le)
  let T : Matrix ι ι ℝ :=
    multiWellCompressionMatrix (volume : Measure (Eucl 1)) κ c
      ((φhat : L2 1) : Eucl 1→ℝ) sites L
  have hT : T.IsHermitian := by
    simpa [T] using multiWellCompressionMatrix_isHermitian
      (volume : Measure (Eucl 1)) κ c ((φhat : L2 1) : Eucl 1→ℝ) sites L
  have hTw : ∀ i j, T i j = w (ψ i) (ψ j) := by
    intro i j
    change multiWellCompressionMatrix (volume : Measure (Eucl 1)) κ c
      ((φhat : L2 1) : Eucl 1→ℝ) sites L i j =
        (G.interaction c) (U (ψ i)) (U (ψ j))
    rw [meshEmbed_ground s hs n hn a L hLpos hsep φ i,
      meshEmbed_ground s hs n hn a L hLpos hsep φ j]
    exact (G.interaction_Φ c φhat i j).symm
  have hsepCompression : ∀ i j : ι, i≠j →
      4*A.R ≤ L*‖sites i-sites j‖ := hsepSite
  have hcompressBase := compression_norm_le_euclid A sites (meshProfileFun φ) L
    hLpos hsepCompression hsupp hint hmass hnonneg
  have hcompress : ‖T - L^(-κ) •
      effectiveInteractionMatrix a c m κ‖ ≤ multiWellEpsilon A sites L := by
    have hTae : T = multiWellCompressionMatrix
        (volume : Measure (Eucl 1)) κ c (meshProfileFun φ) sites L := by
      simpa [T] using meshCompression_congr_ae κ c L sites
        ((φhat : L2 1) : Eucl 1→ℝ) (meshProfileFun φ) hprofAE
    rw [hTae]
    have hbase : ‖multiWellCompressionMatrix
        (volume : Measure (Eucl 1)) κ c (meshProfileFun φ) sites L -
        L^(-κ) • effectiveInteractionMatrix sites c m κ‖ ≤
        multiWellEpsilon A sites L := by
      simpa [A, sites, κ] using hcompressBase
    rw [effectiveInteractionMatrix_linePoint a c m κ] at hbase
    exact hbase
  have hM : (effectiveInteractionMatrix a c m κ).IsHermitian :=
    effectiveInteractionMatrix_isHermitian a c m κ
  have hCM : (L^(-κ) • effectiveInteractionMatrix a c m κ).IsHermitian := by
    exact hM.smul (by rfl)
  have hδ : 0≤multiWellEpsilon A sites L :=
    multiWellEpsilon_nonneg A sites L hLpos.le
  have hcompressEig (k : Fin (Fintype.card ι)) :
      |(hT).eigenvalues₀ (Fin.rev k) -
        L^(-κ) * (effectiveInteractionMatrix_isHermitian a c m κ).eigenvalues₀
          (Fin.rev k)| ≤ multiWellEpsilon A sites L := by
    have h := matrix_eigenvalue_abs_le_of_opNorm T
      (L^(-κ) • effectiveInteractionMatrix a c m κ)
      hT hCM (multiWellEpsilon A sites L) hδ hcompress (Fin.rev k)
    rw [eigenvalues₀_smul (L^(-κ)) (effectiveInteractionMatrix a c m κ)
      hM hCM (Real.rpow_pos_of_pos hLpos _) (Fin.rev k)] at h
    simpa using h
  have hcardEq : Fintype.card (ι×Fin n) = Fintype.card ι * n := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have hcardLe : Fintype.card ι ≤ Fintype.card ι*n := by omega
  have hcluster := MinMax.cluster_levels Q₀ Q w hwsymm
    (multiWellGamma A sites L) hwb hQ ψ hψ μ g hg
    (by
      unfold multiWellGamma
      have hsigma := sigmaKappa_nonneg sites κ
      positivity)
    hsmall hheig hqgap hdim T hTw hT
  have hlevel (k : Fin (Fintype.card (ι×Fin n))) :
      MinMax.level Q k.val =
        (multiWellGalerkin_isHermitian c s n a L).eigenvalues₀ (Fin.rev k) := by
    simpa [Q, G, meshGeometry, κ, U] using
      meshLevel_eq_multiWell_eigenvalues c s hs n hn a L hLpos hsep
        (multiWellGalerkin_isHermitian c s n a L) k
  rcases hcluster with ⟨hcl, hEig, hnext⟩
  let kFull (k : Fin (Fintype.card ι)) : Fin (Fintype.card (ι×Fin n)) :=
    ⟨k.val, by rw [hcardEq]; exact lt_of_lt_of_le k.isLt hcardLe⟩
  have hclusterAt (k : Fin (Fintype.card ι)) :
      -(2*(multiWellGamma A sites L)^2/g) ≤
        (multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
            (Fin.rev (kFull k)) -
          (μ+(hT).eigenvalues₀ (Fin.rev k)) ∧
      (multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
            (Fin.rev (kFull k)) -
          (μ+(hT).eigenvalues₀ (Fin.rev k)) ≤ 0 := by
    have h := hcl k
    have hlev : MinMax.level Q k.val =
        (multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
          (Fin.rev (kFull k)) := by
      simpa [kFull] using hlevel (kFull k)
    rw [hlev] at h
    exact h
  have hgammaEq : multiWellGamma A sites L =
      γc * L^(-κ) := by
    simp [multiWellGamma, γc, A, sites, κ]
  have hepsEq : multiWellEpsilon A sites L =
      εc * L^(-κ-2) := by
    simp [multiWellEpsilon, εc, A, sites, κ, mul_assoc]
  have hgammaSq : (multiWellGamma A sites L)^2 =
      γc^2 * L^(-2*κ) := by
    rw [hgammaEq, mul_pow]
    rw [← Real.rpow_mul_natCast hLpos.le (-κ) 2]
    congr 1 <;> ring
  have hexp₁ : -κ-2 = -3-2*s := by dsimp [κ]; ring
  have hexp₂ : -2*κ = -2-4*s := by dsimp [κ]; ring
  have hrpow₁ : L^(-κ-2)=L^(-3-2*s) := congrArg (fun p : ℝ => L^p) hexp₁
  have hrpow₂ : L^(-2*κ)=L^(-2-4*s) := congrArg (fun p : ℝ => L^p) hexp₂
  have hcl := hclusterAt k
  have hδcl : 0≤2*(multiWellGamma A sites L)^2/g := by positivity
  have hclusterAbs :
      |(multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
          (Fin.rev (kFull k)) -
        (μ+(hT).eigenvalues₀ (Fin.rev k))| ≤
          2*(multiWellGamma A sites L)^2/g := by
    apply abs_le.mpr
    exact ⟨hcl.1, le_trans hcl.2 hδcl⟩
  have hcmp := hcompressEig k
  have htheta :
      (effectiveInteractionMatrix_isHermitian a c m κ).eigenvalues₀
          (Fin.rev k) =
        effectiveInteractionTheta a c m κ k := by
    simp [effectiveInteractionTheta]
  have hsumAbs :
      |(multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
          (Fin.rev (kFull k)) -
        (μ + L^(-κ)*effectiveInteractionTheta a c m κ k)| ≤
        2*(multiWellGamma A sites L)^2/g +
          multiWellEpsilon A sites L := by
    have hident :
        (multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
            (Fin.rev (kFull k)) -
          (μ + L^(-κ)*effectiveInteractionTheta a c m κ k) =
        ((multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
            (Fin.rev (kFull k)) -
          (μ+(hT).eigenvalues₀ (Fin.rev k)) ) +
        ((hT).eigenvalues₀ (Fin.rev k) -
          L^(-κ)*effectiveInteractionTheta a c m κ k) := by
      ring
    rw [hident]
    exact (abs_add_le _ _).trans
      (add_le_add hclusterAbs (by simpa [htheta] using hcmp))
  have htotalLE :
      2*(multiWellGamma A sites L)^2/g+multiWellEpsilon A sites L ≤
        C*(L^(-3-2*s)+L^(-2-4*s)) := by
    rw [hgammaSq, hepsEq, hrpow₁, hrpow₂]
    dsimp [C]
    have hsig : 0 ≤ sigmaKappa sites (κ+2) :=
      sigmaKappa_nonneg sites (κ+2)
    have hepsc : 0 ≤ εc := by
      dsimp [εc]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hc.le A.hC.le) (sq_nonneg m)) hsig
    have hsig0 : 0 ≤ sigmaKappa sites κ :=
      sigmaKappa_nonneg sites κ
    have hγc : 0 ≤ γc := by dsimp [γc]; positivity
    have hgcoef : 0 ≤ 2*γc^2/g := by positivity
    have hx : 0 ≤ L^(-3-2*s) :=
      (Real.rpow_pos_of_pos hLpos _).le
    have hy : 0 ≤ L^(-2-4*s) :=
      (Real.rpow_pos_of_pos hLpos _).le
    have hleft :
        2*(γc^2*L^(-2-4*s))/g =
          (2*γc^2/g)*L^(-2-4*s) := by ring
    rw [hleft]
    rw [← sub_nonneg]
    have hid :
        (εc+2*γc^2/g)*(L^(-3-2*s)+L^(-2-4*s)) -
            ((2*γc^2/g)*L^(-2-4*s)+εc*L^(-3-2*s)) =
          εc*L^(-2-4*s)+(2*γc^2/g)*L^(-3-2*s) := by ring
    rw [hid]
    positivity
  have htarget := hsumAbs.trans htotalLE
  simpa [κ, μ, m, φ, kFull] using htarget



private theorem bilin_polar_symm_fixed {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) (x y : V) :
    QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap B) x y = 2 * B x y := by
  change B (x+y) (x+y) - B x x - B y y = 2 * B x y
  have hfirst : B (x+y) = B x + B y := map_add B x y
  rw [hfirst]
  simp only [LinearMap.add_apply, map_add]
  rw [hB y x]
  ring

private theorem matrix_scalar_hermitian_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ℝ) : (Matrix.scalar ι x).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  refine Matrix.IsSymm.ext ?_
  intro i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.diagonal_apply_ne _ (Ne.symm hij)]

private theorem matrix_shift_eigenvalues_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (a : ℝ) :
    ∀ k : Fin (Fintype.card ι),
      (show (A - Matrix.scalar ι (-a)).IsHermitian from
        hA.sub (matrix_scalar_hermitian_fixed (-a))).eigenvalues₀ k =
        a + hA.eigenvalues₀ k := by
  intro k
  let B : Matrix ι ι ℝ := A - Matrix.scalar ι (-a)
  have hB : B.IsHermitian := hA.sub (matrix_scalar_hermitian_fixed (-a))
  have hchar : B.charpoly = A.charpoly.comp (Polynomial.X + Polynomial.C (-a)) := by
    dsimp [B]
    exact Matrix.charpoly_sub_scalar A (-a)
  have hroot : B.charpoly.roots = A.charpoly.roots.map (fun x => x + a) := by
    rw [hchar]
    rw [show Polynomial.X + Polynomial.C (-a) =
      Polynomial.C (1:ℝ) * Polynomial.X + Polynomial.C (-a) by simp]
    rw [Polynomial.roots_comp_C_mul_X_add_C _ _ _ isUnit_one]
    simp
  have hrootRe :
      (B.charpoly.roots.map RCLike.re) =
        (A.charpoly.roots.map RCLike.re).map (a + ·) := by
    rw [hroot]
    simp only [Multiset.map_map]
    congr 1
    funext x
    simp [add_comm]
  have hsortShift :
      ((A.charpoly.roots.map RCLike.re).sort (· ≥ ·)).map (a + ·) =
        ((A.charpoly.roots.map RCLike.re).map (a + ·)).sort (· ≥ ·) := by
    apply Multiset.map_sort
    intro x hx y hy
    constructor <;> intro h <;> nlinarith
  have hlist :
      List.ofFn hB.eigenvalues₀ =
        List.ofFn (fun i => a + hA.eigenvalues₀ i) := by
    calc
      List.ofFn hB.eigenvalues₀ =
          (B.charpoly.roots.map RCLike.re).sort (· ≥ ·) :=
            hB.sort_roots_charpoly_eq_eigenvalues₀.symm
      _ = ((A.charpoly.roots.map RCLike.re).map (a + ·)).sort (· ≥ ·) := by
            rw [hrootRe]
      _ = ((A.charpoly.roots.map RCLike.re).sort (· ≥ ·)).map (a + ·) :=
            hsortShift.symm
      _ = (List.ofFn hA.eigenvalues₀).map (a + ·) := by
            rw [hA.sort_roots_charpoly_eq_eigenvalues₀]
      _ = List.ofFn (fun i => a + hA.eigenvalues₀ i) := by
        rw [List.map_ofFn]
        congr 1
  have hf0 : hB.eigenvalues₀ = fun i => a + hA.eigenvalues₀ i :=
    List.ofFn_inj.mp hlist
  change hB.eigenvalues₀ k = a + hA.eigenvalues₀ k
  exact congrFun hf0 k

private theorem matrix_reindex_eigenvalues_fixed {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (A : Matrix α α ℝ) (hA : A.IsHermitian)
    (k : Fin (Fintype.card β)) :
    (hA.reindex e).eigenvalues₀ k =
      hA.eigenvalues₀ (Fin.cast (Fintype.card_congr e).symm k) := by
  let B : Matrix β β ℝ := A.reindex e e
  have hB : B.IsHermitian := hA.reindex e
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  have hlist :
      List.ofFn hB.eigenvalues₀ =
        List.ofFn (fun k : Fin (Fintype.card β) =>
          hA.eigenvalues₀ (Fin.cast hcard.symm k)) := by
    calc
      List.ofFn hB.eigenvalues₀ =
          (B.charpoly.roots.map RCLike.re).sort (· ≥ ·) :=
            hB.sort_roots_charpoly_eq_eigenvalues₀.symm
      _ = (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
            change (((A.reindex e e).charpoly.roots.map RCLike.re).sort (· ≥ ·)) = _
            rw [Matrix.charpoly_reindex]
      _ = List.ofFn hA.eigenvalues₀ :=
            hA.sort_roots_charpoly_eq_eigenvalues₀
      _ = List.ofFn (fun k : Fin (Fintype.card β) =>
            hA.eigenvalues₀ (Fin.cast hcard.symm k)) :=
            List.ofFn_congr hcard hA.eigenvalues₀
  have hf := List.ofFn_inj.mp hlist
  exact congrFun hf k

private theorem eig_fin_one_fixed (A : Matrix (Fin 1) (Fin 1) ℝ)
    (hA : A.IsHermitian) :
    hA.eigenvalues₀ (⟨0, by simp⟩ : Fin (Fintype.card (Fin 1))) = A 0 0 := by
  have ht := hA.trace_eq_sum_eigenvalues
  simp only [Matrix.trace_fin_one, Fin.sum_univ_one,
    Matrix.IsHermitian.eigenvalues] at ht
  let e : Fin (Fintype.card (Fin 1)) ≃ Fin 1 :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 1)))
  have hidx : e.symm (0:Fin 1) = (⟨0, by simp⟩ : Fin (Fintype.card (Fin 1))) := by
    apply e.injective
    simpa using (Subsingleton.elim (0:Fin 1) (e ⟨0, by simp⟩))
  have hteq : A 0 0 = hA.eigenvalues₀ (e.symm 0) := by
    simpa [e] using ht
  rw [hidx] at hteq
  exact hteq.symm

private theorem meshCenter_one_zero : meshCenter 1 (0 : Fin 1) = 0 := by
  norm_num [meshCenter]

private theorem meshPhi_one_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0<s ∧ s<1/2) :
    meshPhi (ι := ι) s hs 1 (by omega) (fun _ : Fin 1 => (1:ℝ)) =
      meshCellDomain s hs 1 (by omega) 0 := by
  apply Subtype.ext
  simp [meshPhi, meshCellEmbed, meshCellDomain, meshCenter_one_zero, meshCenter]

private theorem meshProfileFun_one_fixed :
    meshProfileFun (fun _ : Fin 1 => (1:ℝ)) =
      (lineCell 0 1).indicator (fun _ => (1:ℝ)) := by
  funext x
  norm_num [meshProfileFun, meshCenter]

private theorem eucl1_norm_coord_fixed (x : Eucl 1) : ‖x‖ = |x 0| := by
  have hx : x = linePoint (x 0) := by
    ext i
    fin_cases i
    rfl
  rw [hx]
  exact linePoint_norm _

private theorem meshOne_eigen_fixed (c s μ : ℝ)
    (hμ : μ = oneWellGalerkin c s 1 0 0) :
    (oneWellGalerkin c s 1).mulVec (fun _ : Fin 1 => (1:ℝ)) =
      μ • (fun _ : Fin 1 => (1:ℝ)) := by
  ext i
  fin_cases i
  rw [Matrix.mulVec_apply_eq_sum]
  simp [Fin.sum_univ_one, hμ]

private theorem meshOne_matrix_entry_decomp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c s : ℝ) (hs : 0<s ∧ s<1/2) (a : ι → ℝ) (L : ℝ)
    (hL : 0<L) (hsep : ∀ i j, i≠j → 4≤L*|a i-a j|)
    (hA : (oneWellGalerkin c s 1).IsHermitian) (μ : ℝ)
    (hμ : μ = oneWellGalerkin c s 1 0 0) :
    ∀ i j : ι,
      multiWellGalerkin c s 1 a L (i, (0:Fin 1)) (j, 0) =
        μ * (if i=j then 1 else 0) +
          multiWellCompressionMatrix (volume : Measure (Eucl 1)) (1+2*s) c
            ((meshCellDomain s hs 1 (by omega) 0 : L2 1) : Eucl 1 → ℝ)
            (fun i => linePoint (a i)) L i j := by
  classical
  let φ0 : Fin 1 → ℝ := fun _ => (1:ℝ)
  let φE : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 φ0
  have hφeig : Matrix.toEuclideanLin (oneWellGalerkin c s 1) φE = μ • φE := by
    have hh := congrArg (WithLp.toLp 2) (meshOne_eigen_fixed c s μ hμ)
    simpa [φE, Matrix.toEuclideanLin_apply] using hh
  let sites : ι → Eucl 1 := fun i => linePoint (a i)
  let G := meshGeometry s hs a L hL hsep
  let U := meshEmbed s hs 1 (by omega) a L hL hsep
  let φhat : formDomain (1+2*s) (lineCell 0 1) :=
    meshCellDomain s hs 1 (by omega) 0
  let ψ : ι → EuclideanSpace ℝ (ι×Fin 1) :=
    fun i => meshGroundVector 1 φ0 i
  let Q₀ : QuadraticMap ℝ (EuclideanSpace ℝ (ι×Fin 1)) ℝ :=
    meshBlockQ0 (oneWellGalerkin c s 1)
  let Q : QuadraticMap ℝ (EuclideanSpace ℝ (ι×Fin 1)) ℝ :=
    (formQ c (1+2*s) G.Ω).comp U
  let w : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (ι×Fin 1)) :=
    (G.interaction c).comp U U
  have hQeq : Q = Q₀ + LinearMap.BilinMap.toQuadraticMap w := by
    ext z
    change formQ c (1+2*s) G.Ω (U z) =
      meshBlockQ0 (oneWellGalerkin c s 1) z + (G.interaction c) (U z) (U z)
    rw [G.formQ_eq c (U z)]
    rw [← meshBlockQ0_eq_GQ0 s hs c 1 (by omega) a L hL hsep z]
  have hwsymm : ∀ x y, w x y = w y x := by
    intro x y
    change (G.interaction c) (U x) (U y) =
      (G.interaction c) (U y) (U x)
    exact G.interaction_symm c (U x) (U y)
  have hψnorm : ∑ α : Fin 1, φ0 α ^ 2 = 1 := by simp [φ0]
  have hψorth : Orthonormal ℝ ψ := meshGround_orthonormal 1 φ0 hψnorm
  have hU (i : ι) : U (ψ i) = G.Φ φhat i := by
    change meshEmbed s hs 1 (by omega) a L hL hsep
      (meshGroundVector 1 φ0 i) = G.Φ φhat i
    rw [meshEmbed_ground s hs 1 (by omega) a L hL hsep φ0 i]
    rw [meshPhi_one_fixed s hs]
  let T : Matrix ι ι ℝ := multiWellCompressionMatrix (volume : Measure (Eucl 1))
    (1+2*s) c ((φhat : L2 1) : Eucl 1 → ℝ) sites L
  have hTw (i j : ι) : T i j = w (ψ i) (ψ j) := by
    change multiWellCompressionMatrix (volume : Measure (Eucl 1))
        (1+2*s) c ((φhat : L2 1) : Eucl 1 → ℝ) sites L i j =
      (G.interaction c) (U (ψ i)) (U (ψ j))
    rw [hU i, hU j]
    exact (G.interaction_Φ c φhat i j).symm
  have hQpolar (i j : ι) :
      QuadraticMap.polar (formQ c (1+2*s) G.Ω) (U (ψ i)) (U (ψ j)) =
        2*μ*inner ℝ (ψ i) (ψ j) + 2*T i j := by
    have hq := congrArg
      (fun Q' : QuadraticMap ℝ (EuclideanSpace ℝ (ι×Fin 1)) ℝ =>
        QuadraticMap.polar Q' (ψ i) (ψ j)) hQeq
    have hpolarAdd :
        QuadraticMap.polar (Q₀ + LinearMap.BilinMap.toQuadraticMap w) (ψ i) (ψ j) =
          QuadraticMap.polar Q₀ (ψ i) (ψ j) +
            QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap w) (ψ i) (ψ j) := by
      change QuadraticMap.polar
        ((Q₀ : EuclideanSpace ℝ (ι×Fin 1) → ℝ) +
          (LinearMap.BilinMap.toQuadraticMap w : EuclideanSpace ℝ (ι×Fin 1) → ℝ))
        (ψ i) (ψ j) = _
      exact QuadraticMap.polar_add _ _ _ _
    have hq' :
        QuadraticMap.polar ((formQ c (1+2*s) G.Ω).comp U) (ψ i) (ψ j) =
          QuadraticMap.polar Q₀ (ψ i) (ψ j) +
            QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap w) (ψ i) (ψ j) := by
      calc
        QuadraticMap.polar ((formQ c (1+2*s) G.Ω).comp U) (ψ i) (ψ j) =
            QuadraticMap.polar Q (ψ i) (ψ j) := by rfl
        _ = QuadraticMap.polar (Q₀ + LinearMap.BilinMap.toQuadraticMap w)
              (ψ i) (ψ j) := hq
        _ = _ := hpolarAdd
    rw [meshQuadraticMap_polar_comp] at hq'
    have hblock :
        QuadraticMap.polar Q₀ (ψ i) (ψ j) =
          2*μ*inner ℝ (ψ i) (ψ j) := by
      simpa [Q₀, ψ, φ0, φE] using
        meshBlockQ0_weak_eigen (oneWellGalerkin c s 1) hA φE μ hφeig i (ψ j)
    have hwpol :=
      bilin_polar_symm_fixed w hwsymm (ψ i) (ψ j)
    rw [hblock, hwpol, ← hTw i j] at hq'
    exact hq'
  have hentryForm (i j : ι) :
      multiWellGalerkin c s 1 a L (i, (0:Fin 1)) (j, 0) =
        QuadraticMap.polar (formQ c (1+2*s) G.Ω)
          (G.Φ φhat i) (G.Φ φhat j) / 2 := by
    have h := formBilin_eq_polar c (1+2*s) G.Ω (G.Φ φhat i) (G.Φ φhat j)
    rw [meshTranslate_cell s hs 1 (by omega) a L hL hsep i 0,
      meshTranslate_cell s hs 1 (by omega) a L hL hsep j 0] at h
    simpa [multiWellGalerkin, meshCenter_one_zero] using h
  intro i j
  rw [hentryForm]
  rw [← hU i, ← hU j, hQpolar]
  have hψinner : ∀ i j, inner ℝ (ψ i) (ψ j) = if i=j then 1 else 0 :=
    orthonormal_iff_ite.mp hψorth
  have hinner : inner ℝ (ψ i) (ψ j) = if i=j then 1 else 0 := hψinner i j
  rw [hinner]
  ring


set_option maxHeartbeats 1000000 in
private theorem fixedMesh_one_cluster
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (c s : ℝ) (hc : 0<c) (hs : 0<s ∧ s<1/2)
    (a : ι→ℝ) (ha : Function.Injective a)
    (hA : (oneWellGalerkin c s 1).IsHermitian) (μ : ℝ)
    (hμ : μ = oneWellGalerkin c s 1 0 0) :
    ∃ C L₁ : ℝ, ∀ L : ℝ, L₁≤L → ∀ k : Fin (Fintype.card ι),
      |(multiWellGalerkin_isHermitian c s 1 a L).eigenvalues₀
          (Fin.rev ⟨k.val, by
            have hk := k.isLt
            rw [Fintype.card_prod, Fintype.card_fin]
            nlinarith⟩) -
        (μ + L ^ (-(1 + 2 * s)) *
          effectiveInteractionTheta a c 1 (1 + 2 * s) k)| ≤
          C * (L ^ (-3 - 2 * s) + L ^ (-2 - 4 * s)) := by
  classical
  let κ : ℝ := 1+2*s
  let sites : ι→Eucl 1 := fun i => linePoint (a i)
  have hne : ∀ i j : ι, i≠j → sites i ≠ sites j := by
    intro i j hij heq
    apply hij
    apply ha
    exact linePoint_injective heq
  let A : TwoWellConstants :=
    { d := 1
      s := s
      hs := ⟨hs.1, by linarith [hs.2]⟩
      kappa := κ
      hkappa := by dsimp [κ]; norm_num
      c := c
      hc := hc
      R := 1
      hR := by norm_num
      volumeD := 1
      hvolumeD := by norm_num
      mu1 := 0
      mu2 := 1
      hgap := by norm_num
      phiMass := 1
      hphiMass := by norm_num }
  let C : ℝ := c * A.C * (1:ℝ)^2 * sigmaKappa sites (κ+2)
  have hCnonneg : 0≤C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hc.le A.hC.le) (sq_nonneg (1:ℝ)))
      (sigmaKappa_nonneg sites (κ+2))
  have hcond := multiWellCondition_eventually A sites hne
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hcond
  refine ⟨C, L₁, ?_⟩
  intro L hL k
  have hconditions := hL₁ L hL
  have hLpos : 0<L := hconditions.1
  have hsepSite : ∀ i j : ι, i≠j → 4*A.R≤L*‖sites i-sites j‖ :=
    hconditions.2.1
  have hsepLine : ∀ i j, i≠j → 4≤L*|a i-a j| := by
    intro i j hij
    have h := hsepSite i j hij
    have hnorm : ‖sites i-sites j‖=|a i-a j| := by
      simp [sites, linePoint_sub_norm]
    rw [hnorm] at h
    dsimp [A] at h
    nlinarith
  let φ0 : Fin 1→ℝ := fun _ => (1:ℝ)
  let φhat : formDomain (1+2*s) (lineCell 0 1) :=
    meshCellDomain s hs 1 (by omega) 0
  let u : Eucl 1→ℝ := meshProfileFun φ0
  have huformula : u = (lineCell 0 1).indicator (fun _ => (1:ℝ)) := by
    exact meshProfileFun_one_fixed
  have hsupp : ∀ x, u x≠0 → ‖x‖≤A.R := by
    intro x hx
    have hx' : ((lineCell 0 1).indicator (fun _ => (1:ℝ))) x ≠ 0 := by
      rw [← huformula]
      exact hx
    have hxmem : x∈lineCell 0 1 := by
      by_contra hnot
      exact hx' (by simp [hnot])
    have hcoord : |x 0| < (1:ℝ)/2 := by
      simpa [lineCell] using hxmem
    rw [eucl1_norm_coord_fixed]
    dsimp [A]
    linarith [abs_nonneg (x 0)]
  have hint : Integrable u (volume : Measure (Eucl 1)) := by
    rw [huformula]
    exact (integrable_indicator_iff (measurableSet_lineCell 0 1)).2
      (integrableOn_const (volume_lineCell_ne_top 0 1))
  have hvol : (volume : Measure (Eucl 1)).real (lineCell 0 1)=1 := by
    change ((volume : Measure (Eucl 1)) (lineCell 0 1)).toReal=1
    rw [volume_lineCell 0 1 (by norm_num : (0:ℝ)≤1)]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1)]
  have hmass : ∫ x, u x= A.phiMass := by
    calc
      ∫ x, u x ∂(volume : Measure (Eucl 1)) =
          ∫ x, (lineCell 0 1).indicator (fun _ => (1:ℝ)) x
            ∂(volume : Measure (Eucl 1)) := by rw [huformula]
      _ = (volume : Measure (Eucl 1)).real (lineCell 0 1) :=
        integral_indicator_one (measurableSet_lineCell 0 1)
      _ = A.phiMass := by simpa [A] using hvol
  have hnonneg : ∀ x, 0≤u x := by
    intro x
    rw [huformula]
    by_cases hx : x ∈ lineCell 0 1 <;> simp [hx]
  have hprofAE :
      ((φhat : L2 1) : Eucl 1→ℝ) =ᵐ[volume] u := by
    have hphi := meshProfile_coe_ae s hs 1 (by omega) φ0
    have hphiEq := meshPhi_one_fixed (ι := Unit) s hs
    have hL2 := congrArg
      (fun z : formDomain (1+2*s) (lineCell 0 1) => (z : L2 1)) hphiEq
    dsimp [φhat,u]
    rw [← hL2]
    exact hphi
  have hsepCompression : ∀ i j : ι, i≠j → 4*A.R≤L*‖sites i-sites j‖ :=
    hsepSite
  have hcompressBase := compression_norm_le_euclid A sites u L
    hLpos hsepCompression hsupp hint hmass hnonneg
  let T : Matrix ι ι ℝ :=
    multiWellCompressionMatrix (volume : Measure (Eucl 1)) κ c
      ((φhat : L2 1) : Eucl 1→ℝ) sites L
  have hTae : T = multiWellCompressionMatrix (volume : Measure (Eucl 1))
      κ c u sites L := by
    simpa [T] using meshCompression_congr_ae κ c L sites
      ((φhat : L2 1) : Eucl 1→ℝ) u hprofAE
  have hbaseSite :
      ‖multiWellCompressionMatrix (volume : Measure (Eucl 1)) κ c u sites L -
        L^(-κ) • effectiveInteractionMatrix sites c 1 κ‖ ≤
        multiWellEpsilon A sites L := by
    simpa [A, κ] using hcompressBase
  rw [effectiveInteractionMatrix_linePoint a c 1 κ] at hbaseSite
  have hcompress : ‖T-L^(-κ) • effectiveInteractionMatrix a c 1 κ‖ ≤
      multiWellEpsilon A sites L := by
    rw [hTae]
    exact hbaseSite
  let H : Matrix (ι×Fin 1) (ι×Fin 1) ℝ := multiWellGalerkin c s 1 a L
  let hH : H.IsHermitian := multiWellGalerkin_isHermitian c s 1 a L
  let e : (ι×Fin 1) ≃ ι :=
    { toFun := fun p => p.1
      invFun := fun i => (i,0)
      left_inv := by intro p; ext <;> simp
      right_inv := by intro i; rfl }
  let H' : Matrix ι ι ℝ := H.reindex e e
  have hH' : H'.IsHermitian := hH.reindex e
  have hHdecomp : H' = Matrix.scalar ι μ + T := by
    ext i j
    change H (e.symm i) (e.symm j) = Matrix.scalar ι μ i j + T i j
    have hh := meshOne_matrix_entry_decomp c s hs a L hLpos hsepLine
      hA μ hμ i j
    simpa [H,T,e,Matrix.scalar_apply,Matrix.diagonal_apply] using hh
  let M : Matrix ι ι ℝ := effectiveInteractionMatrix a c 1 κ
  let Sc : Matrix ι ι ℝ := L^(-κ) • M
  have hM : M.IsHermitian := effectiveInteractionMatrix_isHermitian a c 1 κ
  have hSc : Sc.IsHermitian := by
    exact hM.smul (by rfl)
  let B : Matrix ι ι ℝ := Sc - Matrix.scalar ι (-μ)
  have hB : B.IsHermitian := by
    exact hSc.sub (matrix_scalar_hermitian_fixed (-μ))
  have hdiffEq : H'-B = T-Sc := by
    rw [hHdecomp]
    ext i j
    by_cases hij : i=j <;>
      simp [B,Sc,Matrix.add_apply,Matrix.sub_apply,Matrix.scalar_apply,
        Matrix.diagonal_apply,hij] <;> ring
  have hnorm : ‖H'-B‖≤multiWellEpsilon A sites L := by
    rw [hdiffEq]
    exact hcompress
  have hδ : 0≤multiWellEpsilon A sites L :=
    multiWellEpsilon_nonneg A sites L hLpos.le
  have hscalePos : 0<L^(-κ) := Real.rpow_pos_of_pos hLpos _
  have hshift (k : Fin (Fintype.card ι)) :
      hB.eigenvalues₀ k = μ+hSc.eigenvalues₀ k := by
    simpa [B,Sc] using matrix_shift_eigenvalues_fixed Sc hSc μ k
  have hθ (k : Fin (Fintype.card ι)) :
      hM.eigenvalues₀ (Fin.rev k)=effectiveInteractionTheta a c 1 κ k := by
    rfl
  have heps : multiWellEpsilon A sites L = C*L^(-κ-2) := by
    simp [multiWellEpsilon,C,A,κ,mul_assoc]
  have hexp : -κ-2=-3-2*s := by dsimp [κ]; ring
  have hpow : L^(-κ-2)=L^(-3-2*s) := congrArg (fun p : ℝ=>L^p) hexp
  let kfull : Fin (Fintype.card (ι×Fin 1)) :=
    ⟨k.val, by simpa [Fintype.card_prod,Fintype.card_fin] using k.isLt⟩
  have hcast :
      Fin.cast (Fintype.card_congr e).symm (Fin.rev k)=Fin.rev kfull := by
    apply Fin.ext
    simp [Fin.rev,kfull,Fintype.card_prod,Fintype.card_fin]
  have hrei :
      hH'.eigenvalues₀ (Fin.rev k)=hH.eigenvalues₀ (Fin.rev kfull) := by
    have hh := matrix_reindex_eigenvalues_fixed e H hH (Fin.rev k)
    rw [hcast] at hh
    exact hh
  have hpert :
      |hH'.eigenvalues₀ (Fin.rev k) -
          (μ+L^(-κ)*effectiveInteractionTheta a c 1 κ k)| ≤
        multiWellEpsilon A sites L := by
    have hh := matrix_eigenvalue_abs_le_of_opNorm H' B hH' hB
      (multiWellEpsilon A sites L) hδ hnorm (Fin.rev k)
    rw [hshift, eigenvalues₀_smul (L^(-κ)) M hM hSc hscalePos] at hh
    simpa only [effectiveInteractionTheta, M] using hh
  have htargetIndex :
      (Fin.rev kfull : Fin (Fintype.card (ι×Fin 1))) =
        Fin.rev ⟨k.val, by
          have hk := k.isLt
          rw [Fintype.card_prod,Fintype.card_fin]
          nlinarith⟩ := by
    apply Fin.ext
    rfl
  have hpert' :
      |(multiWellGalerkin_isHermitian c s 1 a L).eigenvalues₀
          (Fin.rev ⟨k.val, by
            have hk := k.isLt
            rw [Fintype.card_prod,Fintype.card_fin]
            nlinarith⟩) -
          (μ+L^(-κ)*effectiveInteractionTheta a c 1 κ k)| ≤
        multiWellEpsilon A sites L := by
    rw [← htargetIndex]
    rw [← hrei]
    simpa [H,hH,kfull] using hpert
  have hC : 0≤C := hCnonneg
  rw [heps,hpow] at hpert'
  have hx : 0≤L^(-3-2*s) := Real.rpow_nonneg hLpos.le _
  have hy : 0≤L^(-2-4*s) := Real.rpow_nonneg hLpos.le _
  have hsum :
      C*L^(-3-2*s) ≤ C*(L^(-3-2*s)+L^(-2-4*s)) := by
    nlinarith [mul_nonneg hC hy]
  exact hpert'.trans hsum



/-- **Paper Corollary 5.2** (`cor:discrete-cluster`).  `μ_{1,h}` is the lowest
eigenvalue of `A_h`, `φ` its positive normalized eigenvector,
`m_{1,h} = ∫ Σ_α φ_α e_α = h^{1/2} Σ_α φ_α`, and `θ_{k,h}` are the ordered
eigenvalues of the effective matrix with mass `m_{1,h}`. -/
theorem fixedMesh_cluster {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (c s : ℝ) (hc : 0 < c) (hs : 0 < s ∧ s < 1 / 2) (n : ℕ) (hn : 1 ≤ n)
    (a : ι → ℝ) (ha : Function.Injective a) :
    let μ := (oneWellGalerkin_isHermitian c s n).eigenvalues₀
      (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩)
    ∃ φ : Fin n → ℝ, (∀ α, 0 < φ α) ∧ ∑ α, φ α ^ 2 = 1 ∧
      (oneWellGalerkin c s n).mulVec φ = μ • φ ∧
      ∃ C L₁ : ℝ, ∀ L : ℝ, L₁ ≤ L → ∀ k : Fin (Fintype.card ι),
        |(multiWellGalerkin_isHermitian c s n a L).eigenvalues₀
            (Fin.rev ⟨k.val, by
              have hk := k.isLt
              rw [Fintype.card_prod, Fintype.card_fin]
              nlinarith⟩) -
          (μ + L ^ (-(1 + 2 * s)) *
            effectiveInteractionTheta a c
              ((1 / (n : ℝ)) ^ (1 / 2 : ℝ) * ∑ α, φ α) (1 + 2 * s) k)| ≤
          C * (L ^ (-3 - 2 * s) + L ^ (-2 - 4 * s)) := by
  classical
  let hA : (oneWellGalerkin c s n).IsHermitian :=
    oneWellGalerkin_isHermitian c s n
  let μ : ℝ := hA.eigenvalues₀
    (Fin.rev ⟨0, by simp [Fintype.card_fin]; omega⟩)
  by_cases hn2 : 2 ≤ n
  · have hN : 2 ≤ Fintype.card (Fin n) := by simpa using hn2
    have hoff : ∀ α β : Fin n, α ≠ β → oneWellGalerkin c s n α β < 0 := by
      intro α β hαβ
      exact oneWell_offdiag_neg c s hc hs n hn2 α β hαβ
    rcases ground_simple_of_neg_offdiag
        (oneWellGalerkin c s n) hA hN hoff with
      ⟨hgap, φ, hpos, hnorm, heig⟩
    let φE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 φ
    have hnormsq : ‖φE‖ ^ 2 = 1 := by
      calc
        ‖φE‖ ^ 2 = ∑ α : Fin n, φ α ^ 2 := by
          simpa [φE] using EuclideanSpace.real_norm_sq_eq φE
        _ = 1 := hnorm
    have hφnorm : ‖φE‖ = 1 := by
      nlinarith [norm_nonneg φE]
    have hφeig : Matrix.toEuclideanLin (oneWellGalerkin c s n) φE = μ • φE := by
      have hh := congrArg (WithLp.toLp 2) heig
      simpa [φE, μ, Matrix.toEuclideanLin_apply] using hh
    rcases fixedMesh_cluster_gap c s hc hs n hn hn2 a ha hA φE hpos
        hφnorm hφeig hgap with ⟨C, L₁, hbound⟩
    refine ⟨φ, hpos, hnorm, heig, ?_⟩
    refine ⟨C, L₁, ?_⟩
    intro L hL k
    simpa [φE] using hbound L hL k
  · have hn1 : n = 1 := by omega
    subst n
    let φ : Fin 1 → ℝ := fun _ => 1
    have hμvalue : μ = oneWellGalerkin c s 1 0 0 := by
      simpa [μ, Fin.rev] using
        eig_fin_one_fixed (oneWellGalerkin c s 1) hA
    have hpos : ∀ α : Fin 1, 0 < φ α := by
      intro α
      simp [φ]
    have hnorm : ∑ α : Fin 1, φ α ^ 2 = 1 := by simp [φ]
    have heig := meshOne_eigen_fixed c s μ hμvalue
    rcases fixedMesh_one_cluster c s hc hs a ha hA μ hμvalue with
      ⟨C, L₁, hbound⟩
    refine ⟨φ, hpos, hnorm, heig, ?_⟩
    refine ⟨C, L₁, ?_⟩
    intro L hL k
    simpa [φ, μ, hA] using hbound L hL k

end Tunneling
