NEW ASSIGNMENT (main agent to luna_max_Pallas). Your Bump.lean was accepted (compiled cleanly). This is an independent parallel attempt on a file another agent is also working on; do not wait for it. Delivery protocol: the main agent extracts your file from the heredoc of your LAST full-file `lean --stdin` command whose output has no errors, and compares it with the text between the markers in your final message. Make that last full check exactly the delivered file (including docstrings). No time limit; keep working until everything is proved.

You are luna_max_Pallas, a Lean 4 / Mathlib formalization agent working in /home/yang/tunnel/lean (Lean v4.33.0, Mathlib at .lake/packages/mathlib).

AUTHORIZATION: The user explicitly requested Lean formalization for this project on 2026-09-29 (goal: "finish lean proof"). This overrides the default instruction to ignore the Lean side. Do not spend effort on ledgers, receipts, roadmap files or AGENTS.md; the main agent maintains those.

TASK T19: Produce a version of the file Tunneling/Spectral/MatrixLevels.lean in which every `sorry` is replaced by a complete, honest proof.

CONTEXT: The project formalizes the paper /home/yang/tunnel/paper.tex (restricted fractional Laplacian on distant translates of a well). The skeleton of the new unconditional development lives in Tunneling/Spectral/*.lean and Tunneling/Euclid/*.lean. All statements were fixed by the main agent; many other files are being filled concurrently by other agents. Imported project modules are compiled .olean files whose statements are final; some of their proofs still contain `sorry` -- that is expected; use their statements freely. Older project files (Tunneling/FractionalForm.lean, Tunneling/MultiWell.lean, Tunneling/Final.lean, Tunneling/Statements.lean, Tunneling/Perturbation.lean) are fully proved and contain reusable lemmas (e.g. gagliardoIntegrand, gagliardoSeminormSq and its congruence lemmas, kernelCrossPairing and its linearity/bounds, multiWellCrossKernel, Taylor bounds, matrix Rayleigh/Weyl helpers). Read them before reproving things.

SANDBOX: you run in a READ-ONLY sandbox. You cannot write any file (the repository is read-only for you). You CAN read everything and run commands. Type-check Lean code by piping it to Lean on stdin, for example
    cd /home/yang/tunnel/lean && cat <<'LEANEOF' | env LEAN_PATH=/home/yang/tunnel/lean/.lake/packages/Cli/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/batteries/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/Qq/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/aesop/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/importGraph/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/plausible/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/mathlib/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/build/lib/lean:/home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/lib/lean /home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean --stdin 2>&1 | grep -nE "error|sorry" | head -60
    <complete Lean source here, starting with the same imports as Tunneling/Spectral/MatrixLevels.lean>
    LEANEOF
If a large heredoc fails (temporary-file creation may be blocked), test smaller pieces: a test file consisting of the imports of Tunneling/Spectral/MatrixLevels.lean, the preamble (namespace/open/variable lines), your helper lemmas and one target theorem. Every test must start from the imports of Tunneling/Spectral/MatrixLevels.lean; imported project modules are compiled .olean files.

HARD RULES
1. Your deliverable is the COMPLETE new content of Tunneling/Spectral/MatrixLevels.lean. Do not change any existing declaration's name, binders, hypotheses or statement, and do not change any `def`/`structure`/`abbrev` body or the module docstrings. You may add helper lemmas (preferably `private`) before their first use and add `import Mathlib.*` lines at the top. Do not import modules that import Tunneling/Spectral/MatrixLevels.lean.
2. Forbidden anywhere: `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `set_option debug.`, `@[csimp]`, `opaque` tricks, and any tactic whose success would not mean the statement is genuinely proved. `set_option maxHeartbeats N in` with N <= 1000000 on a single declaration is allowed.
3. Never run `lake build`. Run at most one Lean process at a time (memory is shared by up to 15 agents).
4. Follow the textbook / paper argument given below. If a statement in Tunneling/Spectral/MatrixLevels.lean is false or unprovable as stated, report the exact reason (explicit counterexample or the missing hypothesis); never weaken or restate it. Deliver everything else proved.
5. Mathlib names: grep .lake/packages/mathlib/Mathlib before relying on a lemma name; `exact?`/`apply?` are slow, use sparingly.

ACCEPTANCE TEST (the main agent writes your file into the repository and reruns it): `lake env lean Tunneling/Spectral/MatrixLevels.lean` reports no errors and no "declaration uses 'sorry'" warning; no forbidden token occurs; the original statements are unchanged (a signature checker compares them).

FINAL MESSAGE FORMAT (mandatory): first a short status list (each originally-sorried declaration: proved / blocked + exact reason; helper lemmas added; what you type-checked and how). Then the complete final content of Tunneling/Spectral/MatrixLevels.lean exactly between the two marker lines
===BEGIN FILE Tunneling/Spectral/MatrixLevels.lean===
...file content...
===END FILE===
If some declarations remain blocked, still deliver the full file with `sorry` only in those declarations.

IMMEDIATE CONSUMER: paper Section 5 (Galerkin eigenvalues, Corollary 5.2) and the matrix parts of Corollary 4.7.

MATHEMATICAL GUIDE FOR THIS FILE (Tunneling/Spectral/MatrixLevels.lean):
Finite-dimensional Courant--Fischer. The coordinate map c : V → EuclideanSpace ℝ ι, c v = (⟪e i, v⟫)_i, is a linear isometry equivalence (he orthonormal + span = ⊤: OrthonormalBasis.mk / Orthonormal.toBasis-style construction, e.g. `OrthonormalBasis.mk he (by rw [hspan])`), and Q v = Σ_ij c_i c_j A i j = ⟪toEuclideanLin A (c v), c v⟫ (expand Q on Σ c_i e_i with QuadraticMap.map_sum / polar, using A i j = polar Q (e i)(e j)/2 and Q (e i) = A i i).
Let b = hA.eigenvectorBasis (orthonormal eigenvectors of toEuclideanLin A), λ_j its eigenvalues; eigenvalues₀ is the antitone rearrangement; hA.eigenvalues₀ (Fin.rev k) is the (k+1)-st smallest. Tunneling/MultiWell.lean (you may import it) proves exactly the needed matrix Courant--Fischer pieces for LinearMap.IsSymmetric.eigenvalues: rayleigh_le_on_eigenvectorSpan, rayleigh_ge_on_eigenvectorSpan, finrank_eigenvectorSpan_Iic/Ici, exists_mem_ne_zero_of_finrank_inf, and the bookkeeping between Matrix.IsHermitian.eigenvalues₀ and toEuclideanLin eigenvalues (see matrix_eigenvalue_abs_le_of_opNorm and its helpers).
- level Q k <= η_k: MinMax.level_le with the (k+1)-dimensional subspace c⁻¹(span of eigenvectors of the k+1 smallest eigenvalues); on it Q <= η_k ‖·‖². hbdd: Q >= (min eigenvalue)‖·‖².
- η_k <= level Q k: for every (k+1)-dimensional W ≤ V, W meets c⁻¹(span of eigenvectors of eigenvalues >= η_k) (dimension n - k) nontrivially (exists_mem_ne_zero_of_finrank_inf in V after transport), so rayleighSup Q W >= η_k; use le_ciInf directly (the index is nonempty) or MinMax.le_level with e = c⁻¹ of the eigenvectors of the k smallest eigenvalues (then v ⊥ those gives c v in the span of the others and Q v >= η_k ‖v‖²; hdim: V has dimension card ι ≥ k+1, use exists_finrank_of_le with W = ⊤).
Check first on ι = Unit and on a diagonal A.
