NEW ASSIGNMENT (main agent to luna_max_Haumea). Your Compression.lean was accepted. Delivery protocol (changed): the main agent extracts your file from the heredoc of your LAST full-file `lean --stdin` command whose output has no errors, and compares it with the text between the markers in your final message. Make your last full-file check exactly the delivered file (including docstrings). No time limit: keep working until proved.

You are luna_max_Haumea, a Lean 4 / Mathlib formalization agent working in /home/yang/tunnel/lean (Lean v4.33.0, Mathlib at .lake/packages/mathlib).

AUTHORIZATION: The user explicitly requested Lean formalization for this project on 2026-09-29 (goal: "finish lean proof"). This overrides the default instruction to ignore the Lean side. Do not spend effort on ledgers, receipts, roadmap files or AGENTS.md; the main agent maintains those.

TASK T18: Produce a version of the file Tunneling/Euclid/CellMatrix.lean in which every `sorry` is replaced by a complete, honest proof.

CONTEXT: The project formalizes the paper /home/yang/tunnel/paper.tex (restricted fractional Laplacian on distant translates of a well). The skeleton of the new unconditional development lives in Tunneling/Spectral/*.lean and Tunneling/Euclid/*.lean. All statements were fixed by the main agent; many other files are being filled concurrently by other agents. Imported project modules are compiled .olean files whose statements are final; some of their proofs still contain `sorry` -- that is expected; use their statements freely. Older project files (Tunneling/FractionalForm.lean, Tunneling/MultiWell.lean, Tunneling/Final.lean, Tunneling/Statements.lean, Tunneling/Perturbation.lean) are fully proved and contain reusable lemmas (e.g. gagliardoIntegrand, gagliardoSeminormSq and its congruence lemmas, kernelCrossPairing and its linearity/bounds, multiWellCrossKernel, Taylor bounds, matrix Rayleigh/Weyl helpers). Read them before reproving things.

SANDBOX: you run in a READ-ONLY sandbox. You cannot write any file (the repository is read-only for you). You CAN read everything and run commands. Type-check Lean code by piping it to Lean on stdin, for example
    cd /home/yang/tunnel/lean && cat <<'LEANEOF' | env LEAN_PATH=/home/yang/tunnel/lean/.lake/packages/Cli/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/batteries/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/Qq/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/aesop/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/importGraph/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/plausible/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/mathlib/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/build/lib/lean:/home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/lib/lean /home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean --stdin 2>&1 | grep -nE "error|sorry" | head -60
    <complete Lean source here, starting with the same imports as Tunneling/Euclid/CellMatrix.lean>
    LEANEOF
If a large heredoc fails (temporary-file creation may be blocked), test smaller pieces: a test file consisting of the imports of Tunneling/Euclid/CellMatrix.lean, the preamble (namespace/open/variable lines), your helper lemmas and one target theorem. Every test must start from the imports of Tunneling/Euclid/CellMatrix.lean; imported project modules are compiled .olean files.

HARD RULES
1. Your deliverable is the COMPLETE new content of Tunneling/Euclid/CellMatrix.lean. Do not change any existing declaration's name, binders, hypotheses or statement, and do not change any `def`/`structure`/`abbrev` body or the module docstrings. You may add helper lemmas (preferably `private`) before their first use and add `import Mathlib.*` lines at the top. Do not import modules that import Tunneling/Euclid/CellMatrix.lean.
2. Forbidden anywhere: `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `set_option debug.`, `@[csimp]`, `opaque` tricks, and any tactic whose success would not mean the statement is genuinely proved. `set_option maxHeartbeats N in` with N <= 1000000 on a single declaration is allowed.
3. Never run `lake build`. Run at most one Lean process at a time (memory is shared by up to 15 agents).
4. Follow the textbook / paper argument given below. If a statement in Tunneling/Euclid/CellMatrix.lean is false or unprovable as stated, report the exact reason (explicit counterexample or the missing hypothesis); never weaken or restate it. Deliver everything else proved.
5. Mathlib names: grep .lake/packages/mathlib/Mathlib before relying on a lemma name; `exact?`/`apply?` are slow, use sparingly.

ACCEPTANCE TEST (the main agent writes your file into the repository and reruns it): `lake env lean Tunneling/Euclid/CellMatrix.lean` reports no errors and no "declaration uses 'sorry'" warning; no forbidden token occurs; the original statements are unchanged (a signature checker compares them).

FINAL MESSAGE FORMAT (mandatory): first a short status list (each originally-sorried declaration: proved / blocked + exact reason; helper lemmas added; what you type-checked and how). Then the complete final content of Tunneling/Euclid/CellMatrix.lean exactly between the two marker lines
===BEGIN FILE Tunneling/Euclid/CellMatrix.lean===
...file content...
===END FILE===
If some declarations remain blocked, still deliver the full file with `sorry` only in those declarations.

IMMEDIATE CONSUMER: paper Proposition 5.1 (prop:cell-matrix, paper.tex lines 1043-1076); later the fixed-mesh Corollary 5.2.

MATHEMATICAL GUIDE FOR THIS FILE:
d = 1, Eucl 1 = EuclideanSpace ℝ (Fin 1); a point x has coordinate x 0. lineCell a h = {x | |x 0 - a| < h/2}. The map x ↦ x 0 is a measure-preserving equivalence Eucl 1 ≃ ℝ (compose PiLp.volume_preserving_ofLp with the volume-preserving equivalence (Fin 1 → ℝ) ≃ ℝ, e.g. MeasurableEquiv.funUnique / volume_preserving_funUnique); use it to transfer all integrals to ℝ, where lineCell a h is Set.Ioo (a - h/2) (a + h/2) and volume = ofReal h. Write q = 1 - 2s ∈ (0,1), κ = 1 + 2s, gagliardoKernel κ x y = ‖x - y‖^(-κ) = |x 0 - y 0|^(-1-2s).
- measurableSet / volume / ne_top: preimage of an open interval; volume via the transfer.
- norm_cellVec: ‖indicatorConstLp 2 s 1‖ = volume(s)^(1/2) (norm_indicatorConstLp), times h^(-1/2).
- cellVec_mem_formDomain: vanishes off the cell ⊆ G; the Gagliardo integrand of 1_I is (1/h)·1 on (I × Iᶜ) ∪ (Iᶜ × I) times |x-y|^(-1-2s) and 0 elsewhere; its integral is 2 ∫_I ∫_{ℝ∖I} |x-y|^(-1-2s) dy dx = 2·2h^q/(2sq)·... finite because s < 1/2 (inner integral (dist to boundary)^(-2s)/(2s), integrable on I since 2s < 1).
- formBilin_eq_polar: formQ_polar (FormDomain.lean, PROVED).
- cellMatrix_diag: B(e,e) = (c/2)(1/h) ∬ (1_I(x) - 1_I(y))² K = (c/h) ∫_I ∫_{ℝ∖I} |x - y|^(-1-2s) dy dx; for I = (a-h/2, a+h/2): ∫_{y>a+h/2} (y-x)^(-1-2s) dy = (a+h/2-x)^(-2s)/(2s), and ∫_I (a+h/2-x)^(-2s) dx = h^q/q; the left side contributes the same, total 2h^q/(2sq). Use integral_rpow / integral_comp_sub_left type lemmas (grep "integral_rpow", "integrableOn_Ioi_rpow", "integral_Ioi_rpow"), and interval integrals (intervalIntegral.integral_rpow, integral_Ioi_rpow_of_lt).
- cellMatrix_offdiag: disjoint cells (|a - b| ≥ h): (1_I(x) - 1_I(y))(1_J(x) - 1_J(y)) = -1_I(x)1_J(y) - 1_I(y)1_J(x), so B = -c (1/h) ∬_{I×J} |x - y|^(-1-2s). With r = |a - b| (WLOG b > a by symmetry of the kernel), ∫_J (y - x)^(-1-2s) dy = ((r - h/2 - (x - a))^(-2s) - (r + h/2 - (x - a))^(-2s))/(2s) and then ∫_I gives (r^q - (r-h)^q)/q - ((r+h)^q - r^q)/q, so ∬ = (2r^q - (r+h)^q - (r-h)^q)/(2sq). When r = h the term (r-h)^q = 0^q = 0 (q > 0, Real.zero_rpow).
