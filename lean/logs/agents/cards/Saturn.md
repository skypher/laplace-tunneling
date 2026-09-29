You are luna_max_Saturn, a Lean 4 / Mathlib formalization agent working in /home/yang/tunnel/lean (Lean v4.33.0, Mathlib at .lake/packages/mathlib).

AUTHORIZATION: The user explicitly requested Lean formalization for this project on 2026-09-29 (goal: "finish lean proof"). This overrides the default instruction to ignore the Lean side. Do not spend effort on ledgers, receipts, roadmap files or AGENTS.md; the main agent maintains those.

TASK T08: Produce a version of the file Tunneling/Euclid/Sign.lean in which every `sorry` is replaced by a complete, honest proof.

CONTEXT: The project formalizes the paper /home/yang/tunnel/paper.tex (restricted fractional Laplacian on distant translates of a well). The skeleton of the new unconditional development lives in Tunneling/Spectral/*.lean and Tunneling/Euclid/*.lean. All statements were fixed by the main agent; many other files are being filled concurrently by other agents. Imported project modules are compiled .olean files whose statements are final; some of their proofs still contain `sorry` -- that is expected; use their statements freely. Older project files (Tunneling/FractionalForm.lean, Tunneling/MultiWell.lean, Tunneling/Final.lean, Tunneling/Statements.lean, Tunneling/Perturbation.lean) are fully proved and contain reusable lemmas (e.g. gagliardoIntegrand, gagliardoSeminormSq and its congruence lemmas, kernelCrossPairing and its linearity/bounds, multiWellCrossKernel, Taylor bounds, matrix Rayleigh/Weyl helpers). Read them before reproving things.

SANDBOX: you run in a READ-ONLY sandbox. You cannot write any file (the repository is read-only for you). You CAN read everything and run commands. Type-check Lean code by piping it to Lean on stdin, for example
    cd /home/yang/tunnel/lean && cat <<'LEANEOF' | env LEAN_PATH=/home/yang/tunnel/lean/.lake/packages/Cli/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/batteries/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/Qq/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/aesop/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/importGraph/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/plausible/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/packages/mathlib/.lake/build/lib/lean:/home/yang/tunnel/lean/.lake/build/lib/lean:/home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/lib/lean /home/yang/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean --stdin 2>&1 | grep -nE "error|sorry" | head -60
    <complete Lean source here, starting with the same imports as Tunneling/Euclid/Sign.lean>
    LEANEOF
If a large heredoc fails (temporary-file creation may be blocked), test smaller pieces: a test file consisting of the imports of Tunneling/Euclid/Sign.lean, the preamble (namespace/open/variable lines), your helper lemmas and one target theorem. Every test must start from the imports of Tunneling/Euclid/Sign.lean; imported project modules are compiled .olean files.

HARD RULES
1. Your deliverable is the COMPLETE new content of Tunneling/Euclid/Sign.lean. Do not change any existing declaration's name, binders, hypotheses or statement, and do not change any `def`/`structure`/`abbrev` body or the module docstrings. You may add helper lemmas (preferably `private`) before their first use and add `import Mathlib.*` lines at the top. Do not import modules that import Tunneling/Euclid/Sign.lean.
2. Forbidden anywhere: `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `set_option debug.`, `@[csimp]`, `opaque` tricks, and any tactic whose success would not mean the statement is genuinely proved. `set_option maxHeartbeats N in` with N <= 1000000 on a single declaration is allowed.
3. Never run `lake build`. Run at most one Lean process at a time (memory is shared by up to 15 agents).
4. Follow the textbook / paper argument given below. If a statement in Tunneling/Euclid/Sign.lean is false or unprovable as stated, report the exact reason (explicit counterexample or the missing hypothesis); never weaken or restate it. Deliver everything else proved.
5. Mathlib names: grep .lake/packages/mathlib/Mathlib before relying on a lemma name; `exact?`/`apply?` are slow, use sparingly.

ACCEPTANCE TEST (the main agent writes your file into the repository and reruns it): `lake env lean Tunneling/Euclid/Sign.lean` reports no errors and no "declaration uses 'sorry'" warning; no forbidden token occurs; the original statements are unchanged (a signature checker compares them).

FINAL MESSAGE FORMAT (mandatory): first a short status list (each originally-sorried declaration: proved / blocked + exact reason; helper lemmas added; what you type-checked and how). Then the complete final content of Tunneling/Euclid/Sign.lean exactly between the two marker lines
===BEGIN FILE Tunneling/Euclid/Sign.lean===
...file content...
===END FILE===
If some declarations remain blocked, still deliver the full file with `sorry` only in those declarations.

IMMEDIATE CONSUMER: Tunneling/Euclid/GroundState.lean (nonnegative ground state, simplicity).


MATHEMATICAL GUIDE FOR THIS FILE:
Pointwise: (a - b)^2 - (|a| - |b|)^2 = 2(|a||b| - a b) >= 0, and it is 0 iff a b >= 0.
- absL2_ae: MemLp.coeFn_toLp and Real.norm_eq_abs. norm_absL2: Lp norm of |f| equals that of f (eLpNorm_norm / norm congr). absL2_nonneg: from absL2_ae.
- absL2_mem_formDomain: zero-exterior from |f x| = 0 ⇔ f x = 0; integrand of |f| is dominated pointwise by the integrand of f (|‖a‖ - ‖b‖| <= ‖a - b‖), so it is integrable (Integrable.mono' with a.e. congruence on the product; see FractionalForm.lean helpers for lifting a.e. equalities from Eucl d to the product).
- gagliardoSeminormSq_absL2_le: integral_mono_ae with the pointwise domination.
- ae_nonneg_or_nonpos_of_gagliardoSeminormSq_absL2_eq: the difference of the two integrals is ∫ 2(|f x||f y| - f x f y) K(x,y) = 0 with nonnegative integrand, so the integrand vanishes a.e. on the product (integral_eq_zero_iff_of_nonneg_ae). K(x,y) = ‖x - y‖^(-κ) > 0 for x ≠ y, and the diagonal {x = y} is null for volume.prod volume when d >= 1 (volume on EuclideanSpace ℝ (Fin d) has no atoms when d >= 1; Measure.prod of the diagonal via measure_prod_null / lintegral of measure of singletons). Hence f x * f y >= 0 for a.e. (x,y). With P = {f > 0}, N = {f < 0} (measurable up to null sets: use an AEStronglyMeasurable/measurable representative, Lp.aestronglyMeasurable, AEStronglyMeasurable.mk), the product set P ×ˢ N is null, and (volume.prod volume)(P ×ˢ N) = volume P * volume N (Measure.prod_prod), so volume P = 0 or volume N = 0, i.e. f <= 0 a.e. or f >= 0 a.e.
