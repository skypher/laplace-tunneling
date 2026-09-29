import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Tunneling.Spectral.MinMax

/-!
# The isolated spectral-cluster bound

This file formalizes paper Lemma 4.2 (`lem:cluster`) in the Courant--Fischer
language of `Tunneling.MinMax`.  The unperturbed form `Q₀` has the `N`
orthonormal vectors `φ i` as eigenvectors with eigenvalue `μ` (weak
eigen-equation `heig`) and the gap `hgap` on their orthogonal complement.  The
perturbation is a bounded symmetric bilinear form `w`, and the compression of
`w` to `span φ` is the matrix `T`.
-/

namespace Tunneling
namespace MinMax

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Paper Lemma 4.2, equations `eq:cluster-bound` and `eq:cluster-separation`.
The eigenvalues of `T` are listed increasingly as
`hT.eigenvalues₀ (Fin.rev k)`. -/
theorem cluster_levels
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q₀ Q : QuadraticMap ℝ V ℝ) (w : LinearMap.BilinForm ℝ V)
    (hwsymm : ∀ x y : V, w x y = w y x)
    (b : ℝ) (hwb : ∀ x y : V, |w x y| ≤ b * ‖x‖ * ‖y‖)
    (hQ : ∀ v : V, Q v = Q₀ v + w v v)
    (φ : ι → V) (hφ : Orthonormal ℝ φ) (μ g : ℝ)
    (hg : 0 < g) (hb0 : 0 ≤ b) (hb : b ≤ g / 4)
    (heig : ∀ (i : ι) (v : V),
      QuadraticMap.polar Q₀ (φ i) v = 2 * μ * inner ℝ (φ i) v)
    (hgap : ∀ v : V, (∀ i, inner ℝ (φ i) v = 0) → (μ + g) * ‖v‖ ^ 2 ≤ Q₀ v)
    (hdim : ∃ W : Submodule ℝ V, Module.finrank ℝ W = Fintype.card ι + 1)
    (T : Matrix ι ι ℝ) (hTw : ∀ i j, T i j = w (φ i) (φ j)) (hT : T.IsHermitian) :
    (∀ k : Fin (Fintype.card ι),
      -(2 * b ^ 2 / g) ≤ level Q k - (μ + hT.eigenvalues₀ (Fin.rev k)) ∧
        level Q k - (μ + hT.eigenvalues₀ (Fin.rev k)) ≤ 0) ∧
      (∀ k : Fin (Fintype.card ι), |hT.eigenvalues₀ k| ≤ b) ∧
      μ + g - b ≤ level Q (Fintype.card ι) := by
  sorry

end MinMax
end Tunneling
