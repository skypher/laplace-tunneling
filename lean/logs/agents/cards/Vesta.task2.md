NEW ASSIGNMENT (main agent to luna_max_Vesta). Your previous file was accepted. This is an independent parallel attempt on a critical-path file that another agent is also working on; do not wait for it. Current state of the other modules: MinMax, Cluster, FormDomain, Translate, Sign, Compactness, Compression, DecompForm, DecompBound, MainAux, PerronFrobenius are fully proved in the repository; imported statements are final.
Delivery protocol: the main agent extracts your file from the heredoc of your LAST full-file `lean --stdin` command whose output has no errors, and compares it with the text between the markers in your final message. Make that last full check exactly the delivered file (including docstrings). No time limit; keep working until everything is proved or a statement is shown false by an explicit instance ("not yet formalized" is not a stopping reason). Build the proof as a sequence of type-checked private lemmas.

You are luna_max_Vesta, a Lean 4 / Mathlib formalization agent working in /home/yang/tunnel/lean (Lean v4.33.0, Mathlib at .lake/packages/mathlib).

AUTHORIZATION: The user explicitly requested Lean formalization for this project on 2026-09-29 (goal: "finish lean proof"). This overrides the default instruction to ignore the Lean side. Do not spend effort on ledgers, receipts, roadmap files or AGENTS.md; the main agent maintains those.

TASK T10: Produce a version of the file Tunneling/Euclid/Decomp.lean in which every `sorry` is replaced by a complete, honest proof.

CONTEXT: The project formalizes the paper /home/yang/tunnel/paper.tex (restricted fractional Laplacian on distant translates of a well). The skeleton of the new unconditional development lives in Tunneling/Spectral/*.lean and Tunneling/Euclid/*.lean. All statements were fixed by the main agent; many other files are being filled concurrently by other agents. Imported project modules are compiled .olean files whose statements are final; some of their proofs still contain `sorry` -- that is expected; use their statements freely. Older project files (Tunneling/FractionalForm.lean, Tunneling/MultiWell.lean, Tunneling/Final.lean, Tunneling/Statements.lean, Tunneling/Perturbation.lean) are fully proved and contain reusable lemmas (e.g. gagliardoIntegrand, gagliardoSeminormSq and its congruence lemmas, kernelCrossPairing and its linearity/bounds, multiWellCrossKernel, Taylor bounds, matrix Rayleigh/Weyl helpers). Read them before reproving things.

SANDBOX: you run in a READ-ONLY sandbox. You cannot write any file (the repository is read-only for you). You CAN read everything and run commands. Type-check Lean code by piping it to Lean on stdin, for example
    cd /home/yang/tunnel/lean && cat <<'LEANEOF' | env LEAN_PATH=/home/yang/tunnel/lean/.lake/packages/Cli/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/batteries/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/Qq/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/aesop/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/importGraph/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/plausible/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/mathlib/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/build/lib/lean:/home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/lib/lean /home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean --stdin 2>&1 | grep -nE "error|sorry" | head -60
    <complete Lean source here, starting with the same imports as Tunneling/Euclid/Decomp.lean>
    LEANEOF
If a large heredoc fails (temporary-file creation may be blocked), test smaller pieces: a test file consisting of the imports of Tunneling/Euclid/Decomp.lean, the preamble (namespace/open/variable lines), your helper lemmas and one target theorem. Every test must start from the imports of Tunneling/Euclid/Decomp.lean; imported project modules are compiled .olean files.

HARD RULES
1. Your deliverable is the COMPLETE new content of Tunneling/Euclid/Decomp.lean. Do not change any existing declaration's name, binders, hypotheses or statement, and do not change any `def`/`structure`/`abbrev` body or the module docstrings. You may add helper lemmas (preferably `private`) before their first use and add `import Mathlib.*` lines at the top. Do not import modules that import Tunneling/Euclid/Decomp.lean.
2. Forbidden anywhere: `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `set_option debug.`, `@[csimp]`, `opaque` tricks, and any tactic whose success would not mean the statement is genuinely proved. `set_option maxHeartbeats N in` with N <= 1000000 on a single declaration is allowed.
3. Never run `lake build`. Run at most one Lean process at a time (memory is shared by up to 15 agents).
4. Follow the textbook / paper argument given below. If a statement in Tunneling/Euclid/Decomp.lean is false or unprovable as stated, report the exact reason (explicit counterexample or the missing hypothesis); never weaken or restate it. Deliver everything else proved.
5. Mathlib names: grep .lake/packages/mathlib/Mathlib before relying on a lemma name; `exact?`/`apply?` are slow, use sparingly.

ACCEPTANCE TEST (the main agent writes your file into the repository and reruns it): `lake env lean Tunneling/Euclid/Decomp.lean` reports no errors and no "declaration uses 'sorry'" warning; no forbidden token occurs; the original statements are unchanged (a signature checker compares them).

FINAL MESSAGE FORMAT (mandatory): first a short status list (each originally-sorried declaration: proved / blocked + exact reason; helper lemmas added; what you type-checked and how). Then the complete final content of Tunneling/Euclid/Decomp.lean exactly between the two marker lines
===BEGIN FILE Tunneling/Euclid/Decomp.lean===
...file content...
===END FILE===
If some declarations remain blocked, still deliver the full file with `sorry` only in those declarations.

IMMEDIATE CONSUMER: Tunneling/Euclid/DecompForm.lean, DecompBound.lean and Main.lean (paper Lemma 4.1).


MATHEMATICAL GUIDE FOR THIS FILE:
Geometry: D ⊆ ball 0 R, wells D_j = {x | x - L•a j ∈ D}, Ω = ⋃ D_j; for i ≠ j and x ∈ D_i, y ∈ D_j: ‖x - y‖ >= L‖a i - a j‖ - 2R >= 2R > 0; in particular the wells are pairwise disjoint.
- pieceL2_mem: u_j = 1_D · τ_{-L a_j} ψ, i.e. u_j(x) = 1_D(x) ψ(x + L a_j) a.e. (translateL2_ae, indicatorL2_ae). It vanishes off D. Its Gagliardo integrand is integrable: translate back (τ_{L a_j} u_j = 1_{D_j} ψ, energy is translation invariant — gagliardoSeminormSq_translateL2 / translateL2_mem_formDomain for integrability) and bound pointwise the integrand of ψ_j := 1_{D_j} ψ: for (x,y) with x, y ∈ D_j or with x ∈ D_j, y ∉ Ω (where ψ(y) = 0 a.e.) it equals the integrand of ψ; for x ∈ D_j, y ∈ D_i (i ≠ j) it is ψ(x)^2 ‖x-y‖^(-κ) <= (2R)^(-κ) ψ(x)^2 1_{D_i}(y), which is integrable because D_i has finite volume and ψ ∈ L²; symmetric cases likewise; otherwise 0. So integrand(ψ_j) <= integrand(ψ) + (2R)^(-κ)(ψ(x)^2 1_{bounded}(y) + ψ(y)^2 1_{bounded}(x)) a.e.
- inner_eq_sum: ⟪ψ,χ⟫ = ∫ ψ χ = Σ_j ∫_{D_j} ψ χ (ψ, χ vanish a.e. off Ω, wells disjoint and measurable: integral over a finite disjoint union), and ∫_{D_j} ψ χ = ∫ u_j v_j after translating (integral_translateL2-type change of variables). L2.inner_def gives the integral form.
- translate_mem_Ω: translateL2_mem_formDomain gives membership for the well {x | x - L•a j ∈ D} ⊆ Ω; formDomain is monotone in the set.
- pieceL2_Φ: τ_{-L a_i} τ_{L a_j} φ = τ_{L(a_j - a_i)} φ vanishes a.e. on D when i ≠ j (its support is in D + L(a_j - a_i), disjoint from D by the separation), and equals φ when i = j (indicatorL2_of_ae_zero since φ vanishes off D). Use Lp.ext with a.e. equalities.
- interactionFun_add_left/smul_left/add_right/smul_right: crossPair i j u v = kernelCrossPairing K volume u v is linear in u and v for u, v ∈ L² vanishing off D: the integrand u(x) v(y) K(x,y) is integrable because on the support (x, y ∈ D) K = ‖L(a_i - a_j) + x - y‖^(-κ) <= (L‖a_i - a_j‖ - 2R)^(-κ) <= (2R)^(-κ) and u, v ∈ L¹(D). Reuse kernelCrossPairing_add_left/_smul_left/_add_right/_smul_right from FractionalForm.lean, the a.e. equalities for ⇑(f+g), ⇑(t•f), and linearity of pieceL2. Then sum and multiply by -c.
- isOpen_Ω: union of preimages of the open D under continuous maps. Ω_nonempty: x₀ + L•a j for x₀ ∈ D.
