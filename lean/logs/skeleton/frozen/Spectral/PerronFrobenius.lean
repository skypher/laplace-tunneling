import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Ground states of symmetric matrices with negative off-diagonal entries

Paper Corollaries 4.7 and 5.2 use the Rayleigh-quotient form of the
Perron--Frobenius argument: for a real symmetric matrix whose off-diagonal
entries are strictly negative, the lowest eigenvalue is simple and has an
eigenvector with strictly positive entries.
-/

namespace Tunneling

/-- The lowest eigenvalue `hA.eigenvalues₀ (Fin.rev 0)` of a real symmetric
matrix with strictly negative off-diagonal entries is simple and has a
normalized eigenvector with strictly positive entries. -/
theorem ground_simple_of_neg_offdiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hN : 2 ≤ Fintype.card ι)
    (hoff : ∀ i j, i ≠ j → A i j < 0) :
    hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩) < hA.eigenvalues₀ (Fin.rev ⟨1, by omega⟩) ∧
      ∃ z : ι → ℝ, (∀ i, 0 < z i) ∧ ∑ i, z i ^ 2 = 1 ∧
        A.mulVec z = hA.eigenvalues₀ (Fin.rev ⟨0, by omega⟩) • z := by
  sorry

end Tunneling
