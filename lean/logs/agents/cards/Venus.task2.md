NEW ASSIGNMENT (main agent to luna_max_Venus). Your previous file was accepted. This is an independent parallel attempt on a critical-path file that another agent is also working on; do not wait for it. Current state of the other modules: MinMax, Cluster, FormDomain, Translate, Sign, Compactness, Compression, DecompForm, DecompBound, MainAux, PerronFrobenius are fully proved in the repository; imported statements are final.
Delivery protocol: the main agent extracts your file from the heredoc of your LAST full-file `lean --stdin` command whose output has no errors, and compares it with the text between the markers in your final message. Make that last full check exactly the delivered file (including docstrings). No time limit; keep working until everything is proved or a statement is shown false by an explicit instance ("not yet formalized" is not a stopping reason). Build the proof as a sequence of type-checked private lemmas.

You are luna_max_Venus, a Lean 4 / Mathlib formalization agent working in /home/yang/tunnel/lean (Lean v4.33.0, Mathlib at .lake/packages/mathlib).

AUTHORIZATION: The user explicitly requested Lean formalization for this project on 2026-09-29 (goal: "finish lean proof"). This overrides the default instruction to ignore the Lean side. Do not spend effort on ledgers, receipts, roadmap files or AGENTS.md; the main agent maintains those.

TASK T15: Produce a version of the file Tunneling/Euclid/Main.lean in which every `sorry` is replaced by a complete, honest proof.

CONTEXT: The project formalizes the paper /home/yang/tunnel/paper.tex (restricted fractional Laplacian on distant translates of a well). The skeleton of the new unconditional development lives in Tunneling/Spectral/*.lean and Tunneling/Euclid/*.lean. All statements were fixed by the main agent; many other files are being filled concurrently by other agents. Imported project modules are compiled .olean files whose statements are final; some of their proofs still contain `sorry` -- that is expected; use their statements freely. Older project files (Tunneling/FractionalForm.lean, Tunneling/MultiWell.lean, Tunneling/Final.lean, Tunneling/Statements.lean, Tunneling/Perturbation.lean) are fully proved and contain reusable lemmas (e.g. gagliardoIntegrand, gagliardoSeminormSq and its congruence lemmas, kernelCrossPairing and its linearity/bounds, multiWellCrossKernel, Taylor bounds, matrix Rayleigh/Weyl helpers). Read them before reproving things.

SANDBOX: you run in a READ-ONLY sandbox. You cannot write any file (the repository is read-only for you). You CAN read everything and run commands. Type-check Lean code by piping it to Lean on stdin, for example
    cd /home/yang/tunnel/lean && cat <<'LEANEOF' | env LEAN_PATH=/home/yang/tunnel/lean/.lake/packages/Cli/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/batteries/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/Qq/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/aesop/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/importGraph/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/plausible/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/mathlib/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/build/lib/lean:/home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/lib/lean /home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean --stdin 2>&1 | grep -nE "error|sorry" | head -60
    <complete Lean source here, starting with the same imports as Tunneling/Euclid/Main.lean>
    LEANEOF
If a large heredoc fails (temporary-file creation may be blocked), test smaller pieces: a test file consisting of the imports of Tunneling/Euclid/Main.lean, the preamble (namespace/open/variable lines), your helper lemmas and one target theorem. Every test must start from the imports of Tunneling/Euclid/Main.lean; imported project modules are compiled .olean files.

HARD RULES
1. Your deliverable is the COMPLETE new content of Tunneling/Euclid/Main.lean. Do not change any existing declaration's name, binders, hypotheses or statement, and do not change any `def`/`structure`/`abbrev` body or the module docstrings. You may add helper lemmas (preferably `private`) before their first use and add `import Mathlib.*` lines at the top. Do not import modules that import Tunneling/Euclid/Main.lean.
2. Forbidden anywhere: `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `set_option debug.`, `@[csimp]`, `opaque` tricks, and any tactic whose success would not mean the statement is genuinely proved. `set_option maxHeartbeats N in` with N <= 1000000 on a single declaration is allowed.
3. Never run `lake build`. Run at most one Lean process at a time (memory is shared by up to 15 agents).
4. Follow the textbook / paper argument given below. If a statement in Tunneling/Euclid/Main.lean is false or unprovable as stated, report the exact reason (explicit counterexample or the missing hypothesis); never weaken or restate it. Deliver everything else proved.
5. Mathlib names: grep .lake/packages/mathlib/Mathlib before relying on a lemma name; `exact?`/`apply?` are slow, use sparingly.

ACCEPTANCE TEST (the main agent writes your file into the repository and reruns it): `lake env lean Tunneling/Euclid/Main.lean` reports no errors and no "declaration uses 'sorry'" warning; no forbidden token occurs; the original statements are unchanged (a signature checker compares them).

FINAL MESSAGE FORMAT (mandatory): first a short status list (each originally-sorried declaration: proved / blocked + exact reason; helper lemmas added; what you type-checked and how). Then the complete final content of Tunneling/Euclid/Main.lean exactly between the two marker lines
===BEGIN FILE Tunneling/Euclid/Main.lean===
...file content...
===END FILE===
If some declarations remain blocked, still deliver the full file with `sorry` only in those declarations.

IMMEDIATE CONSUMER: the final capstones themselves (multiWell_main = paper Theorem 4.3, twoWell_main = paper Theorem 3.3).


MATHEMATICAL GUIDE FOR THIS FILE:
Assembly. All dependency statements are final (their proofs may still be sorry).
multiWell_cluster: build G : WellGeometry d ι := {κ := d + 2s, hκ, R, hR, D, hDm := hDo.measurableSet, hDR, a, L, hL, hsep}; note G.Ω = multiWellDomain D a L definitionally, eigenvalue = MinMax.level (formQ c κ Ω). Apply MinMax.cluster_levels with V = formDomain κ Ω, Q₀ = G.Q0 c, Q = formQ c κ Ω, w = G.interaction c, b = multiWellGamma A a L (= c 2^κ |D| σ_κ L^(-κ): unfold multiWellGamma/oneWellConstants), φ_i = G.Φ φ̂ i with φ̂ = ⟨φ, hφ.mem⟩, μ = μ₁, g = A.gap (so μ + g = μ₂), T = multiWellCompressionMatrix volume κ c φ a L:
 - hwsymm: interaction_symm; hwb: abs_interaction_le (hc.le); hQ: formQ_eq;
 - Orthonormal (G.Φ φ̂): inner_eq_sum + pieceL2_Φ + ‖φ‖ = 1;
 - heig: polar Q0 = Σ_j polar (formQ D) ∘ (wellMap j) (QuadraticMap.polar_comp, polar of a finite sum is the sum: check Mathlib names), pieceL2_Φ, IsPositiveGroundState.polar_eq, inner_eq_sum;
 - hgap: v ⊥ all Φ_i ⇒ ⟪φ, u_i⟫ = 0 for each piece u_i (inner_eq_sum + pieceL2_Φ) ⇒ Q_D(u_i) >= μ₂‖u_i‖^2 (IsPositiveGroundState.gap) ⇒ Q0 v >= μ₂ Σ‖u_i‖^2 = μ₂‖v‖^2;
 - hdim: exists_finrank_formDomain for Ω (isOpen_Ω, Ω_nonempty);
 - hTw: interaction_Φ; hT: multiWellCompressionMatrix_isHermitian; hb0: multiWellGamma nonneg; hb: hsmall; hg: A.gap > 0.
multiWell_main: follow FinalTheoremMultiWell in Tunneling/MultiWell.lean (its hypotheses were corrected: hupper uses index card ι - 1 and hnext index card ι). For each admissible L use multiWell_cluster: hcluster directly; hupper: λ_{N-1} <= μ₁ + τ_{N-1} <= μ₁ + γ (|τ| <= γ); hnext directly; hnorm: compression_norm_le_euclid with u := D.indicator (fun x => max (φ x) 0) (nonneg, vanishes off D ⊆ ball 0 R, u =ᵐ φ because φ >= 0 a.e. and φ = 0 a.e. off D, integrable via IsPositiveGroundState.integrable, ∫ u = A.phiMass), and multiWellCompressionMatrix volume κ c u a L = multiWellCompressionMatrix volume κ c φ a L (entries are kernel pairings of a.e.-equal functions: prove a small congruence lemma). The exact theta is effectiveInteractionTheta a A.c A.phiMass A.kappa. The limit part: multiWellLimit_of_conclusion with multiWellCondition_eventually (from ha) and multiWellRescaledError_tendsto_zero. You may simply apply FinalTheoremMultiWell with T L := the compression matrix and hne := ha.
twoWell_main (paper Theorem 3.3, lines 498-588): ι = Fin 2, a = twoWellSites e, twoWellDomain_eq. ‖a 0 - a 1‖ = ‖e‖ = 1, so sigmaKappa a κ = sigmaKappa a (κ+2) = 1, multiWellGamma A a L = A.beta L and multiWellEpsilon A a L = c C m² L^(-κ-2). For L >= A.L0: L >= 4R, β <= g/4 (TwoWellConstants.beta_small), so multiWell_cluster applies. T is 2×2 with zero diagonal and t = T 0 1 <= -c m²(L + 2R)^(-κ) < 0 (compression_entry_le_euclid, with the u above), so by eigenvalues₀_fin_two_of_zero_diag τ₀ = t, τ₁ = -t. Compression entry error (compression_entry_error_euclid): |t + c m² L^(-κ)| <= c C m² L^(-κ-2). Then:
 |λ₀ - (μ₁ - c m² L^(-κ))| <= 2β²/g + cCm²L^(-κ-2) = A.remainder L; same for λ₁ with -t; λ₂ >= μ₁ + g - β >= μ₁ + 3g/4; λ₂ - λ₁ >= g - β + t >= g - 2β >= g/2 (|t| <= β from |τ| <= γ = β);
 λ₀ < λ₁: λ₁ - λ₀ >= -2t - 2β²/g >= 2cm²(L+2R)^(-κ) - 2β²/g > 0 by L0_simplicity_condition; λ₁ < λ₂ from the g/2 gap.
 gapLimit: twoWellGapLimit_of_branchErrors (Final.lean) with t L := the entry T 0 1 for L >= L0 (any value otherwise), rPlus L = λ₀ - μ₁ - t, rMinus L = λ₁ - μ₁ + t.
Boundary checks: the index conventions (eigenvalue index k.val for k : Fin N; λ_N is index card ι) and Fin.rev in Fin 2.
