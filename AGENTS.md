# Project goal

Develop a paper proof of algebraic spectral tunnelling for the restricted
fractional Laplacian on finitely many distant congruent domains.

The final paper theorem has three parts:

1. an explicit two-well doublet splitting with a quantified remainder;
2. a finite-dimensional effective interaction matrix for finitely many wells;
3. a source-audited comparison with the nonlocal Hong--Krahn--Szegő limit and
   numerical checks of the proved asymptotics.

All three parts have passed the end-to-end theorem, source, numerical, and
release checks recorded in `notes/final_audit.md`.  The final manuscript is
`paper.pdf`, and the deterministic submission source is
`dist/laplace-tunneling-arxiv.tar.gz`.

## Mathematical conventions

- The operator is the restricted fractional Laplacian associated with the
  zero-exterior Gagliardo form.
- The fractional order is `s in (0,1)` and the kernel exponent is
  `kappa = d + 2s`.
- `c_{d,s}` denotes the normalization in the singular-integral definition.
- For the first theorem, the reference component `D` is bounded, Lipschitz,
  centrally symmetric, and contained in a ball of radius `R`.
- Novelty priority claims use the bounded wording supported by the completed
  literature audit.  Mathematical claims may be stated unconditionally only
  when their proofs and cited inputs are present in the manuscript.

## Priority order

1. Close and check the two-well splitting theorem.  **Closed.**
2. Prove the multi-well effective matrix theorem.  **Closed.**
3. Perform the full novelty and citation audit.  **Closed.**
4. Add reproducible numerical illustrations and complete journal formatting.
   **Closed.**

This is a paper-proof project.  Do not introduce Lean formalization unless the
user explicitly requests it.
