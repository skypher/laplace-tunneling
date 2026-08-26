# Tunnel project roadmap

Overall progress is measured only by the following final-facing theorem
buckets.  Structural files and literature lists do not earn percentage credit.

| Bucket | Weight | Acceptance condition | Status |
|---|---:|---|---|
| Two-well splitting | 35% | Exact block reduction, coefficient, sign, and remainder compile in the manuscript | closed |
| Multi-well effective Hamiltonian | 30% | The spectral cluster is reduced to an explicit finite matrix with a norm-controlled error | closed |
| Applications and source audit | 20% | Quantitative Hong--Krahn--Szegő corollary, interval/ball examples, and priority search are checked | closed |
| Integration | 15% | Full manuscript compiles, notation is consistent, and every cited use is source-specific | closed |

Overall theorem-slot closure: **100%**.  The basis is the 14 numbered results
and proofs in `paper.tex`, the source records in `notes/literature_audit.md`,
the numerical output in `numerics/asymptotics_180.txt`, and the final checks in
`notes/final_audit.md`.

## Closed hard target

**Theorem T2W.**  For two reflected copies of a bounded centrally symmetric
domain separated by distance `L`, prove

`lambda_1 = mu_1 - c m_1^2 L^(-d-2s) + controlled remainder`,

`lambda_2 = mu_1 + c m_1^2 L^(-d-2s) + controlled remainder`,

where `m_1` is the integral of the normalized one-well ground state.

Intended work class: **closure**.

Acceptance evidence: Theorem 3.3 and its supporting Lemmas 2.1, 3.1, and 3.2
in `paper.tex`; the proof checks in `notes/proof_audit.md` and
`notes/final_audit.md`.

## Closed hard target

**Theorem TNW.**  For finitely many translated copies centered at `L a_j`,
prove that the ground-state spectral cluster is approximated, with an
operator-norm remainder, by the matrix whose off-diagonal entries are

`-c m_1^2 |a_i-a_j|^(-d-2s) L^(-d-2s)`.

Intended work class: **closure**.

Acceptance evidence: Theorem 4.6 and its supporting Lemmas 4.2, 4.3, and 4.5
in `paper.tex`; the proof checks in `notes/proof_audit.md` and
`notes/final_audit.md`.

## Closed hard target

**Theorem/Application TSA.**  Complete the quantitative distant-ball and
interval applications, reproduce numerical checks of the proved scaling, and
audit the priority claim against source-specific literature evidence.

Intended work class: **source-audited theorem completion**.

Acceptance evidence: Corollaries 3.4 and 5.2 and Proposition 5.1 in
`paper.tex`; exact table output in `numerics/asymptotics_180.txt`; the primary
source search in `notes/literature_audit.md`; and the passing release audit
recorded in `notes/final_audit.md`.

## Closed integration target

The final manuscript has 50 resolved labels, seven source-specific cited
works, 14 numbered results paired with 14 proofs, and a reproducible 12-page
PDF.  The deterministic source archive is `dist/tunnel-arxiv.tar.gz`.
