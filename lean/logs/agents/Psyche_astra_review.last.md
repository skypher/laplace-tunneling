**R1 verdict, commit `4e00c18`:** The main tunnelling estimates and current Lean formalization withstand this review. I found one substantive **GAP** in the paper’s justification after removing Lipschitz regularity: the cited ground-state theorem uses a different form domain. I found no incorrect splitting constant, eigenvalue index, or active Lean capstone. `Spectrum.lean` genuinely establishes identification with weak eigenvalues, including multiplicities. The remaining findings concern a vacuous superseded interface and scope/documentation details. The 27-theorem axiom audit passed, and a numerical rerun reproduced both tables to their displayed precision.

**A. Paper mathematics**

1. **GAP — The general-domain ground-state citation does not directly apply.**  
   **Locations:** [paper.tex:326](/home/yang/tunnel/paper.tex:326), [paper.tex:668](/home/yang/tunnel/paper.tex:668), and [paper.tex:1070](/home/yang/tunnel/paper.tex:1070).

   **Failure:** The paper defines its form domain by vanishing **almost everywhere** outside the open set. Brasco–Parini instead define their space as the completion of C∞₍c₎(D); their Theorem 2.8 concerns that space. These spaces need not coincide for arbitrary bounded open sets. [Brasco–Parini, §2.2 and Theorem 2.8](https://arxiv.org/pdf/1409.6284v2).

   For example, take d = 1, s > 1/2, and D = (−1,1) ∖ {0}. Removing the point does not change the paper’s space. It therefore contains a smooth bump with value 1 at zero. Every function in the completion of C∞₍c₎(D), however, has value zero there, because point evaluation is continuous in Hˢ(ℝ). Thus the assertion that the cited theorem “apply[ies] unchanged” needs an additional argument.

   **Fix:** Prove the required ground-state facts for the paper’s actual space, or cite a theorem formulated for that space. Compactness, minimization, and the strict energy decrease under absolute values supply nonnegativity and simplicity; these suffice for the tunnelling proofs. If strict positivity is retained, justify it separately. Lean already independently proves the nonnegative ground-state facts needed by the estimates.

**B. Lean formalization**

2. **MINOR — A superseded interface is uninhabitable, beyond its documented regional-form mismatch.**  
   **Locations:** [Final.lean:1070](/home/yang/tunnel/lean/Tunneling/Final.lean:1070), particularly fields at lines 1098–1100; [Final.lean:1809](/home/yang/tunnel/lean/Tunneling/Final.lean:1809).

   **Failure:** `L2TwoWellAux` simultaneously requires a real inner-product space containing a unit vector `direction` and `∀ x : X, ‖x‖ ≤ A.R`. Substituting `(A.R + 1) • direction` gives `A.R + 1 ≤ A.R`. I compiled a Lean proof of `L2TwoWellAux A X mu → False`.

   Consequently, `FinalTheoremL2` is vacuous. Its local description as an interface for the paper’s form is inaccurate. The module is explicitly superseded, and this does **not** compromise the current Table 3 results.

   **Fix:** Explicitly document the inconsistent hypotheses and retire this obsolete interface. If it is retained for use, impose boundedness on the well/support inside an ambient space, rather than on every vector of that space.

**C. Section 6 and Table 3 consistency**

3. **OVERCLAIM — “Every bounded open set” omits nonemptiness.**  
   **Locations:** [paper.tex:1302](/home/yang/tunnel/paper.tex:1302), [paper.tex:1312](/home/yang/tunnel/paper.tex:1312); compare [Spectrum.lean:955](/home/yang/tunnel/lean/Tunneling/Euclid/Spectrum.lean:955) and [GroundState.lean:193](/home/yang/tunnel/lean/Tunneling/Euclid/GroundState.lean:193).

   **Mismatch:** The spectral and ground-state theorems require `G.Nonempty` or `D.Nonempty`. For the empty open set, the form domain is zero and there is no normalized ground state or eigenvalue sequence. The unrestricted min–max definition can still return default real infimum values.

   **Fix:** Add “nonempty” to the global well assumptions and Section 6’s spectral claims. Lemma 2.1 itself does not need this restriction.

4. **MINOR — Table 3 omits the declaration covering the N-dimensional case of Lemma 4.3.**  
   **Locations:** [paper.tex:1337](/home/yang/tunnel/paper.tex:1337); [Cluster.lean:267](/home/yang/tunnel/lean/Tunneling/Spectral/Cluster.lean:267), [Cluster.lean:521](/home/yang/tunnel/lean/Tunneling/Spectral/Cluster.lean:521).

   **Mismatch:** Listed declaration `MinMax.cluster_levels` requires an `(N+1)`-dimensional trial subspace. The paper also asserts the cluster bound when the entire space has dimension N. That case is correctly supplied by `MinMax.cluster_levels_bounds`, which is already included in the axiom audit.

   **Fix:** List both declarations in the row.

5. **MINOR — Several Lean comments retain obsolete paper numbering.**  
   **Locations and mismatches:** [Main.lean:318](/home/yang/tunnel/lean/Tunneling/Euclid/Main.lean:318) calls current Theorem 4.6 “Theorem 4.3”; [Cluster.lean:264](/home/yang/tunnel/lean/Tunneling/Spectral/Cluster.lean:264) calls current Lemma 4.3 “Lemma 4.2”; [Corollaries.lean:701](/home/yang/tunnel/lean/Tunneling/Euclid/Corollaries.lean:701) calls current Corollary 4.8 “Corollary 4.6.”

   **Fix:** Refresh numbered references throughout the Lean documentation, preferably retaining the stable LaTeX labels alongside them. The declaration meanings are correct.

**Items checked and outcomes**

“Pass” below means no additional defect found; the paper’s general-domain ground-state input remains subject to finding 1.

| Item | Checks and outcome |
|---|---|
| Lemma 2.1 / compactness row | **Pass.** Cube variance identity, finite-dimensional approximation, and coefficient d^(κ/2)ε^(2s)/c are correct. No boundary regularity is used. Lean proves the stated qualitative compactness. |
| Lemmas 2.2, 3.1, 3.2 | **Pass.** Central symmetry supports the reflected reduction and even ground state; cross-term signs, perturbation estimate, Hessian bound, C₍κ,R₎, and βL check out. Section 6 correctly excludes these lemmas as stated. |
| Ground-state row | **Pass in Lean.** Existence, uniqueness, positive mass, μ₁ < μ₂, and the orthogonal-complement gap are derived. `IsPositiveGroundState` means normalized, nonnegative minimizer; strict positivity is explicitly excluded from the formalization. |
| Weak-eigenvalue row | **Pass.** Spectrum proves attainment by orthonormal families, monotonicity and divergence, exhaustion of all nonzero weak eigenfunctions, and finite eigenspace dimension equal to the number of matching indices. The multiplicity claim is substantive. |
| Theorem 3.3 | **Pass.** All three terms of L₀, strict threshold inequalities including L = L₀, remainder constants, simplicity, third-level separation, and limiting gap match the formal conclusions. |
| Corollary 3.4 | **Pass.** Upper-branch coefficient is c m₁²; Brasco–Parini normalization is correctly rescaled by c/2. Lean proves the rate; the HKS minimizing interpretation comes from the cited literature. |
| Lemma 4.2 | **Pass.** Exact translated block decomposition, absence of an extra diagonal correction, and maximal-row-sum interaction bound agree with the closed-form Lean version. |
| Lemma 4.3 | **Pass mathematically.** The added dimension condition is sufficient and necessary for the next-level assertion. The comparison-block ordering and N-dimensional cluster-only case are correct. Finding 4 concerns only the table map. |
| Lemma 4.5 | **Pass.** First moments cancel for identical translates without symmetry. The quadratic Taylor remainder and operator-norm εL bound agree. |
| Theorem 4.6 | **Pass.** Exact compression comparison, γL and εL constants, ordered effective eigenvalues, cluster edges, and fixed-site limits match. Lean uses indices N−1 and N for paper indices N and N+1. |
| Corollary 4.7 | **Pass.** Separation factor r^(−κ), remainder orders, and limiting splitting agree. |
| Corollary 4.8 | **Pass.** JL has the stated kernel; compression eigenvalues are −cJL and +cJL. The cited exact comparison, separation estimate, L₀ conditions, remainder identity, and simplicity argument all support their uses. |
| Corollary 4.9 | **Pass**, subject to finding 1 for the paper’s continuum simplicity citation. Matrix sign/simplicity and eventual spectral inequalities match Lean. |
| Corollary 4.10 | **Pass.** Gram-matrix dimension bound and spectrum of −w(J−I) are correct. The continuum shifts follow from the main estimate. |
| Proposition 5.1 | **Pass.** Full-space bilinear form, normalized indicators, diagonal/off-diagonal factors, touching-cell case, and range 0 < s < 1/2 agree. |
| Corollary 5.2 | **Pass.** Actual Galerkin matrices and mass normalization match. Quantifiers keep the mesh and ground vector fixed before L varies. The one-cell case is handled separately without assuming a nonexistent second one-cell eigenvalue. |

I also checked the requested domain, geometry, constant, matrix, conclusion, and limit definitions. The active results use genuine full-space integrals with proved integrability; finite-dimensional Rayleigh suprema are bounded; trial families of every required dimension are constructed; finite row suprema, positive denominators, real-power bases, and natural-number indices are controlled. I found no active default-value or hidden-assumption shortcut.

The source scan found no `sorry`, custom axiom, `native_decide`, `unsafe`, or `implemented_by` in the library. The heartbeat settings only increase computation budgets; the private instance proves `1 ≤ 2`. All 27 audited theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Consumer examples connecting ground-state existence to the actual two-well limit compiled successfully.

Paper/Lean sources match the stated release tag. Code-availability files and numerical outputs are consistent. Section 6’s exclusions and the AI disclosure reveal no further mathematical verification overclaim. This was read-only; I used existing build artifacts for Lean checks rather than performing a fresh build.