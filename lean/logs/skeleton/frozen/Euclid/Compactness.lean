import Tunneling.Euclid.CellAverage

/-!
# Compactness of the form embedding on bounded sets

For a bounded set `D ⊆ ℝ^d`, bounded subsets of `H^s_0(D)` are relatively
compact in `L²(ℝ^d)`.  This replaces the citation
[DiNezzaPalatucciValdinoci2012, Theorem 7.1] in paper Section 2 and is proved
by averaging over cubes of side `ε`: on a cube `Q` of diameter `√d ε`,

  `∫_Q |u - ⨍_Q u|² = (2|Q|)⁻¹ ∬_{Q×Q} |u(x)-u(y)|²
                     ≤ (√d ε)^κ (2 ε^d)⁻¹ ∬_{Q×Q} |u(x)-u(y)|² |x-y|^{-κ}`,

so the cube-average projection, whose range is finite dimensional on
functions supported in a bounded set, approximates `u` within
`C ε^s [u]`.  Lower semicontinuity of the Gagliardo energy follows from Fatou's
lemma along an a.e. convergent subsequence.
-/

namespace Tunneling

open MeasureTheory

variable {d : ℕ}

/-- Energy-bounded subsets of `H^s_0(D)` are totally bounded in `L²`. -/
theorem totallyBounded_energySublevel (s : ℝ) (hs : 0 < s ∧ s < 1)
    (R : ℝ) (D : Set (Eucl d)) (hDR : D ⊆ Metric.closedBall 0 R) (M : ℝ) :
    TotallyBounded {f : L2 d | f ∈ formDomain ((d : ℝ) + 2 * s) D ∧ ‖f‖ ≤ 1 ∧
      gagliardoSeminormSq ((d : ℝ) + 2 * s) (volume : Measure (Eucl d))
        (f : Eucl d → ℝ) ≤ M} := by
  sorry

/-- Every energy-bounded sequence in `H^s_0(D)` has an `L²`-convergent
subsequence. -/
theorem exists_tendsto_subseq (s : ℝ) (hs : 0 < s ∧ s < 1)
    (R : ℝ) (D : Set (Eucl d)) (hDR : D ⊆ Metric.closedBall 0 R)
    (f : ℕ → L2 d) (hf : ∀ n, f n ∈ formDomain ((d : ℝ) + 2 * s) D)
    (hnorm : ∀ n, ‖f n‖ ≤ 1) (M : ℝ)
    (hM : ∀ n, gagliardoSeminormSq ((d : ℝ) + 2 * s) (volume : Measure (Eucl d))
      (f n : Eucl d → ℝ) ≤ M) :
    ∃ g : L2 d, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => f (φ n)) Filter.atTop (nhds g) := by
  sorry

/-- Lower semicontinuity of the Gagliardo energy and closedness of the
zero-exterior condition under `L²` convergence. -/
theorem mem_formDomain_of_tendsto (κ : ℝ) (D : Set (Eucl d))
    (f : ℕ → L2 d) (g : L2 d) (hf : ∀ n, f n ∈ formDomain κ D)
    (hlim : Filter.Tendsto f Filter.atTop (nhds g)) (a : ℝ)
    (ha : ∀ᶠ n in Filter.atTop,
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (f n : Eucl d → ℝ) ≤ a) :
    g ∈ formDomain κ D ∧
      gagliardoSeminormSq κ (volume : Measure (Eucl d)) (g : Eucl d → ℝ) ≤ a := by
  sorry

end Tunneling
