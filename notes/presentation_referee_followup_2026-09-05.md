**Revision status:** the edits are implemented in `paper-2026-09-05-r2`.
The response at the end records the changes and release checks. The review
below describes the preceding release, and its source links are pinned to
that version.

This report reviews *Algebraic tunneling for the restricted fractional
Laplacian on distant domains*, dated 5 September 2026, release
`paper-2026-09-05`. It concerns presentation, wording, bibliography, and arXiv
packaging. The mathematical proofs and numerical algorithms were not
reassessed. Locations refer to the current 16-page PDF and its source.

Double-check before recording the recommendation: I reread the source passages
identified below after inspecting all 16 rendered pages; compared the 13
bibliographic identities against primary records; checked the final LaTeX and
BibTeX logs; ran the existing mechanical release audit; compared all seven
archived files with their working sources; and built the extracted archive
once in a fresh directory. That build has clean final logs, and its generated
bibliography and layout-preserving PDF text match the supplied copies.

**Recommendation on presentation alone: suitable for arXiv, with minor
copyedits recommended.** The current revision has a clear title, an explicit
abstract, a sensible progression from two wells to finitely many wells, and
readable tables. I found no remaining malformed notation glyph, broken
cross-reference, or incorrect bibliographic identity in the material checked.
The changes below improve precision and navigation; they do not call for
reorganizing the paper or changing its mathematical scope.

This is a fresh review of the revised release. The earlier report,
`notes/presentation_referee_report_2026-09-05.md`, principally concerns the
4 September manuscript and includes its revision response. Its corrected
items are not outstanding requests in this report. At the time of the review,
the manuscript, PDF, bibliography, numerical output, and submission archive
were left unchanged.

1. **State the limiting regime in the abstract. Recommended.**

   Location: p. 1, [paper.tex:131](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L131).

   Neither abstract expansion explicitly says “as L → ∞.” “Distant” and the
   error terms make the intention understandable, but an abstract should state
   the limit without requiring the reader to infer it. This matters especially
   when the abstract is read separately on arXiv.

   Change the lead-in to the displayed formula to:

   > For Ω_L = (D − Le/2) ∪ (D + Le/2), with e a fixed unit vector, we prove,
   > as L → ∞, …

   In the later sentence, “For fixed N ≥ 2 and distinct sites a₁, …, a_N”
   would also make the fixed-configuration convention explicit. The current
   phrase “fixed distinct sites” already points in this direction; this is a
   clarification, not a change in the asserted uniformity.

   Retain the present order: the general two-well expansion first, followed
   by the additional decomposition available under central symmetry. There
   is no need to rewrite the abstract wholesale or introduce κ just to save
   a few characters. The existing abstract is 1,407 characters under the
   release audit's whitespace-normalized counting convention.

2. **Define gₕ beside the numerical size check. Recommended.**

   Location: p. 15, [paper.tex:1159](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L1159).

   The symbol gₕ occurs in the comparison with 0.22424 without an explicit
   definition. Table 1 displays μ₂,ₕ − μ₁,ₕ, and Corollary 5.2's proof refers
   to the discrete gap in words, so the intended meaning is recoverable.
   Supplying the definition removes an unnecessary lookup. The same paragraph
   also invokes R without recalling its value for the unit interval.

   A compact replacement for the numerical comparison is:

   > Here gₕ = μ₂,ₕ − μ₁,ₕ and R = 1/2. At L = 3, the bound γ_L in (4.4)
   > is 0.10858 for two wells and 0.21716 for three wells, while
   > gₕ/4 = 0.22424.

   The surrounding explanation can then continue as written. Identifying
   (4.4) also tells the reader which bound is being applied to the Galerkin
   matrices; a new mesh-dependent γ symbol is unnecessary.

   Table 2 itself is now clear. Its headings identify scaled shifts, its
   caption states the order, domain, mesh, and configurations, and equation
   (5.4) defines the error. The sentence about rounding explains why subtracting
   displayed values need not reproduce every last error digit. Retain these
   improvements.

3. **Make the code reference identifiable in plain text. Recommended.**

   Location: p. 15, [paper.tex:1217](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L1217).

   The visible hyperlink is only `paper-2026-09-05`. A reader using a printed
   copy or extracted text cannot tell which repository contains that tag.
   The link works: the GitHub release page returned HTTP 200, and the raw
   manuscript at that tag byte-matches the reviewed source. This is a
   discoverability edit, not a broken-link report.

   Give the repository name as visible text, for example:

   > The manuscript source and numerical files are also available in
   > skypher/laplace-tunneling, tag paper-2026-09-05.

   Link the repository name and tag to the current tagged URL. This makes the
   destination recognizable without printing a long URL.

   The opening sentence can also assign the files clearer roles:

   > The ancillary files provide check_asymptotics.py to reproduce Tables 1
   > and 2, requirements-numerics.txt with the pinned dependencies, and
   > asymptotics_180.txt with the reference output.

   Preserve the environment versions and the statement that the files are
   archived with the manuscript. The ancillary README already gives the
   reproduction commands, so repeating those commands in the paper would add
   little.

4. **Add direct definition references to the principal quantitative theorem.
   Optional, useful for readers consulting the result in isolation.**

   Location: p. 11, [paper.tex:831](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L831); also
   p. 10, [paper.tex:791](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L791).

   Theorem 4.6 sends readers to the beginning of the section and Definition
   4.1, while γ_L, ε_L, and θₖ are defined in three other places. These symbols
   are defined; the issue is the amount of searching needed to use the main
   estimate.

   Add a short sentence such as:

   > Let γ_L and ε_L be given by (4.4) and (4.10), and let θ₁, …, θ_N be
   > the eigenvalues in Definition 4.4.

   At the first use of C₍κ,R₎ in Lemma 4.5, a reference back to (3.2) would
   serve the same purpose. This is preferable to adding a separate notation
   table to a paper of this length.

5. **Name the symmetry operation explicitly on first use. Optional.**

   Locations: p. 1, [paper.tex:137](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L137), and
   p. 2, [paper.tex:184](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L184).

   “Symmetric and antisymmetric sectors” is understandable after Section 2,
   but before that point it leaves the transformation unnamed. Write
   “symmetric and antisymmetric sectors under central inversion,” or add
   “under x ↦ −x” once in the introduction. This connects the early overview
   directly to Lemma 2.1 and avoids an unintended suggestion of symmetry
   across a hyperplane. One clarification is enough.

6. **Remove the one-line proof ending at the top of p. 14 if the final
   copyedits allow it. Optional layout polish.**

   Location: pp. 13–14, [paper.tex:1074](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L1074).

   The final sentence of Proposition 5.1's proof occupies the first line of
   p. 14, followed immediately by Corollary 5.2. It is legible, but the isolated
   tail is the only page break I would actively improve. Keep the last display
   with its concluding sentence, or recover a line through a local prose edit.
   Recheck the resulting pages after the other edits; a global font or margin
   change would be disproportionate.

The following smaller wording choices are discretionary. They should not
delay submission or displace the three recommended edits above.

| Location | Current wording | Possible revision and reason |
| --- | --- | --- |
| p. 2, [line 188](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L188) | “Both arguments are self-contained after the standard one-well spectral facts.” | “The proofs use the one-well spectral facts recalled in Section 2, together with elementary perturbation estimates.” This is more idiomatic and gives a concrete pointer. |
| p. 12, [line 935](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L935) | Corollary 4.8, “Recovery of the doublet” | “Agreement of the two-well remainder bounds.” The statement compares the remainder expressions; the more specific title helps distinguish it from Corollary 4.7 immediately before it. Retain the numbered statement and proof. |
| p. 13, [line 1024](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L1024) | “Reproducible fixed-mesh checks on intervals” | “Numerical illustrations on intervals.” The first two sentences already specify the fixed mesh and the exact assembly. The existing heading is accurate and can also be retained. |
| p. 14, [line 1144](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L1144) | “fixed-mesh effective-matrix spectra, indexed by the fixed sites” | “For these fixed sites, the effective matrices on this mesh have eigenvalues …” This avoids the stack of modifiers. |
| p. 15, [line 1220](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-05/paper.tex#L1220) | “The output was reproduced using …” | “The calculation was reproduced using …” This more directly describes the reproduction being reported. |

The introduction now gives the contribution before the literature discussion.
The explanation for retaining both the centrally symmetric two-well treatment
and the general finite-well treatment is in the right place. The literature
paragraphs are dense but specific; their operator distinctions are useful.
The bounded priority sentence at lines 229–230 is appropriately cautious in
its wording. I would retain it rather than add another novelty paragraph or
strengthen it to an absolute priority claim.

The title identifies the restricted operator explicitly, and the first
paragraph explains the meaning of tunneling used here. The terminology is
consistent with that explanation. American spellings in the manuscript are
consistent. There is no need to change them to match spellings in repository
notes or cited titles. The AI disclosure identifies the activities involved
and the author's responsibility clearly; I have no presentation objection to
that paragraph. No change to its historical account is proposed.

For the bibliography, I compared the displayed entries and their source fields
with the primary records below before recording these findings. The citation
set, BibTeX set, and generated bibliography each contain the same 13 entries.
The table concerns bibliographic identity, publication details, and reference
presentation; it does not represent a new check of every cited theorem.

| Entry | Primary record and finding |
| --- | --- |
| AFN20 | [Publisher-deposited metadata](https://api.crossref.org/works/10.1142/S0219199719500718) and the [authors' institutional record](https://boa.unimib.it/handle/10281/285117) match the authors, title, journal, volume 22(8), article 1950071, and DOI. The 2020 volume year is appropriate despite online publication in 2019. The bibliography visibly identifies arXiv v2. |
| BDVV23 | The [publisher's recommended citation](https://www.aimspress.com/article/doi/10.3934/mine.2023014) matches volume 5(1), pages 1–25, and year 2023. It uses **Szegö** in the title. Preserve that spelling in this reference while retaining Szegő in the manuscript's own prose. The online date is in 2022, and the Crossref record has imperfect date and author fields; the publisher's explicit citation controls here. |
| BP16 | [Publisher-deposited metadata](https://api.crossref.org/works/10.1515/acv-2015-0007) match the authors, title, volume 9(4), pages 323–355, year 2016, and DOI. The [arXiv v2 record](https://arxiv.org/abs/1409.6284v2) identifies the linked version. |
| DFW21 | The [publisher's article](https://link.springer.com/article/10.1007/s00526-021-02094-3) and [deposited metadata](https://api.crossref.org/works/10.1007/s00526-021-02094-3) match the authors, title, volume 60(6), article 231, year 2021, and DOI. The later arXiv revision does not change the journal year. |
| DNPV12 | [Publisher-deposited metadata](https://api.crossref.org/works/10.1016/j.bulsci.2011.12.004) match the authors, title, volume 136(5), pages 521–573, year 2012, and DOI. “Di Nezza” and the journal accent are rendered correctly. |
| DPLSV26 | The [arXiv v1 record](https://arxiv.org/abs/2602.18035v1) matches the four authors, title, identifier, category, and date, 20 February 2026. The entry is correctly presented as a preprint. |
| GS19 | [Publisher-deposited metadata](https://api.crossref.org/works/10.1090/proc/14542) match the authors, title, volume 147(10), pages 4315–4327, year 2019, and DOI. “Of combination between” belongs to the original title; do not repair its grammar in the bibliography. |
| Kwa12 | [Publisher-deposited metadata](https://api.crossref.org/works/10.1016/j.jfa.2011.12.004) match the author, title, volume 262(5), pages 2379–2402, year 2012, and DOI. The spelling Kwaśnicki and the title's “Laplace operator” are correct. |
| LR23 | The [publisher's article](https://link.springer.com/article/10.1007/s00526-022-02374-6) matches the published title, author pair, volume 62, article 30, and year 2023. The [arXiv record](https://arxiv.org/abs/2004.14771) carries the earlier title *Properties of steady states for a class of non-local Fisher-KPP equations in disconnected domains*. The title difference and the 2022 online publication date do not call for changing the current journal citation. |
| PS20 | [Publisher-deposited metadata](https://api.crossref.org/works/10.1002/mana.201800234) and the [arXiv record](https://arxiv.org/abs/1806.01165) match the identity, volume 293(11), pages 2208–2232, year 2020, and DOI. The arXiv author list supplies the full given names. |
| Wu26 | The [publisher's indexed article](https://www.sciencedirect.com/science/article/abs/pii/S009630032600247X) and [deposited metadata](https://api.crossref.org/works/10.1016/j.amc.2026.130195) match the author, title, volume 531, article 130195, year 2026, and DOI. The assigned issue date is December 2026. That future issue date does not make the already available reference erroneous. |
| Zah26 | The [publisher's article](https://link.springer.com/article/10.1007/s00526-026-03270-z) and [deposited metadata](https://api.crossref.org/works/10.1007/s00526-026-03270-z) match Alvis Zahl, the title, volume 65(3), article 98, year 2026, and DOI. |
| Zha26 | The [arXiv v1 record](https://arxiv.org/abs/2608.23457v1) matches Cheng Zhang, the title, identifier, category, and date, 24 August 2026. The preprint entry matches the record accessed. |

The author/year labels, full given names, journal names, and linked identifiers
are consistently presented. Article numbers appear after a colon in the same
style as page ranges; this is understandable and is used consistently.
Changing the bibliography style before this submission is unnecessary.
The similar labels Zah26 and Zha26 are distinct and resolve correctly.

The two page-specific citations now explicitly identify arXiv v2 in the text.
Retain those version qualifiers: they tell readers why the locator is p. 2 or
p. 3 even when the entry also supplies a journal reference. The Wu citation to
the Introduction is suitable for locating the descriptive literature claim;
the publisher's accessible introduction explicitly states the relationship to
Zahl's conjecture. This review does not supply a replacement theorem number.
The interval references are now introduced as high-index background, so they
are no longer easily mistaken for estimates of the tabulated ground state.

The rendered-page inspection gives the following presentation assessment.

| Pages | Assessment |
| --- | --- |
| 1–2 | The title and author block are readable. The abstract is dense but usable and contains the main coefficients. The result overview and literature comparison have a clear order. |
| 3–4 | The defining form renders as calligraphic Q. The exact block reduction and its proof have readable displays and consistent notation. |
| 5–7 | Lemma 3.2 and Theorem 3.3 each have an intact statement. The explicit threshold and two shift bounds fit within the text area. |
| 8–12 | Definitions, compression estimates, and theorem references are legible. Theorem 4.6 and Corollary 4.7 have intact statements. The navigation edit in item 4 would help readers entering at the theorem. |
| 13–14 | The formulas and Table 1 are legible. Corollary 5.2 is kept together. The one-line ending of the preceding proof is the minor layout issue in item 6. |
| 15 | Table 2 fits and its two configurations are clearly separated. The disclosure and code paragraph are readable. The gₕ definition and visible repository name are the useful text edits. |
| 16 | All 13 bibliography entries fit without clipping or overlapping. Author accents, DOI lines, and arXiv version suffixes are readable. |

The final local release checks are evidence about the supplied files, not a
run of arXiv's own processing service:

- The mechanical audit reports 13 citations, 56 labels, 15 result/proof
  environment pairs, 11 saved numerical rows, 1,407 abstract characters, and
  16 PDF pages. The result/proof count is a structural count. The numerical
  check compares saved output with manuscript text; no eigensolve was rerun.
- The supplied and freshly built final LaTeX/BibTeX logs have no warnings,
  unresolved references, or overfull/underfull box diagnostics. All fonts
  listed by `pdffonts` are embedded Type 1 fonts.
- Direct inspection of PDF destinations puts Theorem 4.6 on p. 11 and all
  13 citation destinations on p. 16. The PDF contains the expected 24 external
  URL annotations: 11 DOI links, 12 arXiv links, and the tagged repository link.
- The archive contains `paper.tex`, `paper.bbl`, and `references.bib` at its
  root and four files in `anc/`. All seven files byte-match their working
  sources. The fresh build reproduces the bibliography and extracted PDF
  text. I do not claim that the PDF bytes are identical across builds.
- The public tagged repository page returns HTTP 200, and its raw
  `paper.tex` byte-matches the reviewed source.

The archive's bibliography and ancillary layout agree with arXiv's current
[TeX instructions](https://info.arxiv.org/help/submit_tex.html) and
[ancillary-file instructions](https://info.arxiv.org/help/ancillary_files.html).
For the abstract field, copy the prose and formulas, omitting the environment,
keywords, MSC block, and layout commands. Its present length is below the
1,920-character maximum in arXiv's
[metadata instructions](https://info.arxiv.org/help/prep.html#abstract-required).
Inspect the accent in Hong–Krahn–Szegő and the mathematical expressions in the
submission preview. A suitable comments field for the present layout is:
“16 pages, 2 tables; numerical code and reference output included as ancillary
files.” Update the count if edits change the layout.

If the copyedits are adopted, regenerate
`dist/laplace-tunneling-arxiv.tar.gz` and inspect the resulting PDF before
upload. The current package corresponds to the current, unedited manuscript.

Artifact identities at the time of this review:

```text
e7870fb44f690e4d30c39a761f7fa20d0319dba059a6c42670a4be107aa01961  paper.tex
b19abc921fcb63981896953cc481a0c2ffc5a4354aaded87b107c49f9735f86c  paper.pdf
2ae142793fba1f411c3960066311cb73c4875b4f83201e32e86aef73ee522eac  references.bib
7de3edad1d926fb28f2f79b380a429bd47224706cec10892ca0d1390ac2b2fad  dist/laplace-tunneling-arxiv.tar.gz
```

**Revision response — `paper-2026-09-05-r2`.**

| Review item | Implemented change |
| --- | --- |
| 1. Abstract | Added the explicit limit L → ∞ and fixed N ≥ 2. |
| 2. Numerical notation | Defined gₕ = μ₂,ₕ − μ₁,ₕ, recalled R = 1/2, and linked γ_L to equation (4.4). |
| 3. Code availability | Identified the script, dependencies, and reference output separately. Both the repository name and the new release tag are visible hyperlink text. |
| 4. Theorem navigation | Theorem 4.6 now points directly to the geometry, effective matrix, and error-bound definitions. Lemma 4.5 points to the definition of C₍κ,R₎ in (3.2). |
| 5. Symmetry wording | The abstract names central inversion as the symmetry operation. |
| 6. Page break | Moved the normalization explanation before the final integral in Proposition 5.1's proof and placed the end-of-proof symbol with that display. The proof now ends on p. 13; Corollary 5.2 starts p. 14. |
| Discretionary copyedits | Revised the introduction's explanation of the proof ingredients, shortened the numerical section heading and effective-spectrum sentence, renamed Corollary 4.8 “Two-well remainder comparison,” and clarified the reproduction wording. |

Checks completed immediately before recording this response: all 16 final
pages were inspected; the final LaTeX and BibTeX logs are clean; the release
audit passes with 13 citations, 56 labels, 15 result/proof pairs, 11 saved
numerical rows, and 1,462 abstract characters. The 79 displayed-mathematics
blocks match the preceding source after normalization of whitespace and the
end-of-proof marker. The bibliography, numerical script, and saved output
are unchanged.

The first layout pass exposed two spacing diagnostics in the code paragraph
and a bibliography overflow. The final wording removes those diagnostics and
keeps the bibliography on p. 16. Theorem 4.6's concluding proof paragraph was
tightened while retaining its inequalities and cited equation numbers.

The regenerated archive contains seven files, each matching its working
source. A fresh build of the extracted archive reproduces the bibliography
and layout-preserving PDF text; its final logs are clean. Repacking the
payload with the fixed release metadata reproduces the archive bytes. The
current artifact hashes are recorded in `notes/final_audit.md`.
