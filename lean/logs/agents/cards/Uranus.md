You are luna_max_Uranus, a Lean 4 / Mathlib formalization agent working in /home/yang/tunnel/lean (Lean v4.33.0, Mathlib at .lake/packages/mathlib).

AUTHORIZATION: The user explicitly requested Lean formalization for this project on 2026-09-29 (goal: "finish lean proof"). This overrides the default instruction to ignore the Lean side. Do not spend effort on ledgers, receipts, roadmap files or AGENTS.md; the main agent maintains those.

TASK T11: Produce a version of the file Tunneling/Euclid/DecompForm.lean in which every `sorry` is replaced by a complete, honest proof.

CONTEXT: The project formalizes the paper /home/yang/tunnel/paper.tex (restricted fractional Laplacian on distant translates of a well). The skeleton of the new unconditional development lives in Tunneling/Spectral/*.lean and Tunneling/Euclid/*.lean. All statements were fixed by the main agent; many other files are being filled concurrently by other agents. Imported project modules are compiled .olean files whose statements are final; some of their proofs still contain `sorry` -- that is expected; use their statements freely. Older project files (Tunneling/FractionalForm.lean, Tunneling/MultiWell.lean, Tunneling/Final.lean, Tunneling/Statements.lean, Tunneling/Perturbation.lean) are fully proved and contain reusable lemmas (e.g. gagliardoIntegrand, gagliardoSeminormSq and its congruence lemmas, kernelCrossPairing and its linearity/bounds, multiWellCrossKernel, Taylor bounds, matrix Rayleigh/Weyl helpers). Read them before reproving things.

SANDBOX: you run in a READ-ONLY sandbox. You cannot write any file (the repository is read-only for you). You CAN read everything and run commands. Type-check Lean code by piping it to Lean on stdin, for example
    cd /home/yang/tunnel/lean && cat <<'LEANEOF' | env LEAN_PATH=/home/yang/tunnel/lean/.lake/packages/Cli/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/batteries/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/Qq/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/aesop/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/importGraph/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/plausible/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/mathlib/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/build/lib/lean:/home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/lib/lean /home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean --stdin 2>&1 | grep -nE "error|sorry" | head -60
    <complete Lean source here, starting with the same imports as Tunneling/Euclid/DecompForm.lean>
    LEANEOF
If a large heredoc fails (temporary-file creation may be blocked), test smaller pieces: a test file consisting of the imports of Tunneling/Euclid/DecompForm.lean, the preamble (namespace/open/variable lines), your helper lemmas and one target theorem. Every test must start from the imports of Tunneling/Euclid/DecompForm.lean; imported project modules are compiled .olean files.

HARD RULES
1. Your deliverable is the COMPLETE new content of Tunneling/Euclid/DecompForm.lean. Do not change any existing declaration's name, binders, hypotheses or statement, and do not change any `def`/`structure`/`abbrev` body or the module docstrings. You may add helper lemmas (preferably `private`) before their first use and add `import Mathlib.*` lines at the top. Do not import modules that import Tunneling/Euclid/DecompForm.lean.
2. Forbidden anywhere: `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `set_option debug.`, `@[csimp]`, `opaque` tricks, and any tactic whose success would not mean the statement is genuinely proved. `set_option maxHeartbeats N in` with N <= 1000000 on a single declaration is allowed.
3. Never run `lake build`. Run at most one Lean process at a time (memory is shared by up to 15 agents).
4. Follow the textbook / paper argument given below. If a statement in Tunneling/Euclid/DecompForm.lean is false or unprovable as stated, report the exact reason (explicit counterexample or the missing hypothesis); never weaken or restate it. Deliver everything else proved.
5. Mathlib names: grep .lake/packages/mathlib/Mathlib before relying on a lemma name; `exact?`/`apply?` are slow, use sparingly.

ACCEPTANCE TEST (the main agent writes your file into the repository and reruns it): `lake env lean Tunneling/Euclid/DecompForm.lean` reports no errors and no "declaration uses 'sorry'" warning; no forbidden token occurs; the original statements are unchanged (a signature checker compares them).

FINAL MESSAGE FORMAT (mandatory): first a short status list (each originally-sorried declaration: proved / blocked + exact reason; helper lemmas added; what you type-checked and how). Then the complete final content of Tunneling/Euclid/DecompForm.lean exactly between the two marker lines
===BEGIN FILE Tunneling/Euclid/DecompForm.lean===
...file content...
===END FILE===
If some declarations remain blocked, still deliver the full file with `sorry` only in those declarations.

IMMEDIATE CONSUMER: Tunneling/Euclid/Main.lean (hQ : Q = Q₀ + w in cluster_levels; symmetry hwsymm).


MATHEMATICAL GUIDE FOR THIS FILE:
Paper Lemma 4.1 proof (lines 656-707 of paper.tex), exact form identity.
Write ψ_j = 1_{D_j} ψ = τ_{L a_j} u_j (a.e.), so ψ = Σ_j ψ_j a.e. (ψ vanishes off Ω, wells disjoint). For i ≠ j the supports are disjoint, hence pointwise
 (ψ(x) - ψ(y))^2 = Σ_j (ψ_j(x) - ψ_j(y))^2 + Σ_{i≠j} (ψ_i(x) - ψ_i(y))(ψ_j(x) - ψ_j(y)),
 (ψ_i(x) - ψ_i(y))(ψ_j(x) - ψ_j(y)) = -ψ_i(x)ψ_j(y) - ψ_i(y)ψ_j(x)   (i ≠ j).
Multiply by K(x,y) = ‖x - y‖^(-κ) and integrate: each Gagliardo integrand of ψ_j is integrable (pieceL2_mem + translation invariance), each cross term ψ_i(x)ψ_j(y)K is integrable (kernel bounded by (2R)^(-κ) on D_i × D_j, ψ_i, ψ_j ∈ L¹). By the swap symmetry of volume.prod volume (integral_prod_swap) the two cross terms have equal integrals. Hence
 formQ Ω ψ = (c/2)[ψ]^2 = Σ_j (c/2)[ψ_j]^2 - c Σ_{i≠j} ∬ ψ_i(x) ψ_j(y) ‖x - y‖^(-κ).
Translation: (c/2)[ψ_j]^2 = (c/2)[u_j]^2 = formQ D (wellMap j ψ) (gagliardoSeminormSq_translateL2, formQ_apply), and with x = x' + L a_i, y = y' + L a_j (measure preserving on the product) ∬ ψ_i(x)ψ_j(y)‖x-y‖^(-κ) = ∬ u_i(x')u_j(y') ‖L(a_i - a_j) + x' - y'‖^(-κ) = crossPair i j u_i u_j. Finally Q0 c ψ = Σ_j formQ D (wellMap j ψ) (QuadraticMap sum/comp application lemmas), and interaction c ψ ψ = interactionFun c ψ ψ (interaction_apply).
interaction_symm: crossPair i j u v = crossPair j i v u by integral_prod_swap and ‖center + x - y‖ = ‖-center + y - x‖ (MultiWell.lean has multiWellCrossKernel_neg_center_swap and kernelCrossPairing_multiWell_swap); then exchange the order of the double sum (Finset.sum_comm) with the if i = j condition.
