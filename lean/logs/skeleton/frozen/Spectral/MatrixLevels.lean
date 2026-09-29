import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
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

/-- Finite-dimensional min--max: levels are the ordered Galerkin eigenvalues. -/
theorem level_eq_eigenvalues₀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticMap ℝ V ℝ) (e : ι → V) (he : Orthonormal ℝ e)
    (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    (A : Matrix ι ι ℝ) (hAe : ∀ i j, A i j = QuadraticMap.polar Q (e i) (e j) / 2)
    (hA : A.IsHermitian) (k : Fin (Fintype.card ι)) :
    level Q k = hA.eigenvalues₀ (Fin.rev k) := by
  sorry

end MinMax
end Tunneling
