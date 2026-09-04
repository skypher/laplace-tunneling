# Presentation and bibliography referee report

Date: 5 September 2026. Manuscript: *Algebraic tunneling for the restricted
fractional Laplacian on distant domains*, dated 4 September 2026, release
`paper-2026-09-04-r5`.

**Revision status:** the editorial changes are applied in
`paper-2026-09-05`.  The response at the end of this report records the
changes and subsequent release checks.  Sections 1–10 preserve the review
of the earlier release.

This review concerns presentation, wording, bibliography, and submission
packaging. It does not reassess the mathematical proofs or repeat the numerical
computations. Page numbers below refer to the reviewed 16-page PDF; source
links and line numbers refer to `paper-2026-09-04-r5`.

Evidence checked before the recommendation: I read the complete manuscript
source and bibliography, inspected all 16 rendered pages, compared the
bibliographic records listed below, ran the existing release audit, and built
the extracted submission archive in a fresh directory. The final build log has
no LaTeX warnings or overfull/underfull box diagnostics; BibTeX reports no
warnings. The rebuilt bibliography and layout-preserving PDF text match the
working copies. The typesetting defect described in item 1 appears in both
the supplied PDF and the fresh build.

**Recommendation: minor editorial revision before upload.** The paper has a
clear subject, a useful explicit abstract, and an appropriate level of detail
for a short analysis paper. The title identifies the operator correctly. The
main editorial problems are one malformed notation glyph, an abstract that
underemphasizes the more general result already in the paper, repeated novelty
comparisons, and a few imprecise descriptions of the numerical tables. I found
no incorrect reference identity or DOI/arXiv identifier in the records checked.

At the time of this review, the manuscript and submission archive had not
been edited.  The original report records the proposed revisions.

## 1. Correct before upload: the quadratic-form symbol

**Location:** p. 3, equation (2.1), and subsequent occurrences on pp. 3–4 and
13; [paper.tex:258](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L258).

The source uses `\mathcal q`. With the loaded fonts, this produces the symbol
**⨿**, not a calligraphic letter q. The defect is visible in the rendered
equation, and independent PDF text extraction gives `⨿G [u]`. A source search
finds eight occurrences, at lines 258, 272, 338, 339, 371 (three occurrences),
and 1045. Compilation does not warn about this.

Use `\mathcal{Q}` consistently for the form. A plain `q` or `\mathfrak{q}`
would also render as a letter, but uppercase calligraphic Q gives a clear
distinction from the scalar q introduced in Section 5. Adding braces around
the existing lowercase letter, as in `\mathcal{q}`, would not fix the glyph.

This is the first revision I would make: it affects the notation for the
paper's defining quadratic form.

## 2. Clarify the abstract's definitions and emphasis

**Location:** p. 1; [paper.tex:127](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L127).

The abstract introduces φ₁ as positive and L²-normalized without explicitly
saying it is the eigenfunction corresponding to μ₁. Because its integral
determines the leading coefficient, state the relationship directly:

> Let μ₁ be the one-well ground-state eigenvalue and φ₁ its positive,
> L²-normalized eigenfunction, and set m₁ = ∫ᴅ φ₁.

The larger editorial issue is the order of generality. The opening requires
central symmetry, the multi-well sentence later relaxes it, and Corollary 4.7
on p. 11 supplies the two-well asymptotic without symmetry. A reader who scans
only the first formula may therefore remember an unnecessarily restricted
version of the result.

Introduce the general bounded Lipschitz reference set first. Present the
two-well asymptotic at the generality of Corollary 4.7, then explain that
central symmetry permits the additional exact sector decomposition and
explicit threshold of Theorem 3.3. This changes the exposition, not the
theorems or the scope of the paper. A smaller edit would retain the current
order and explicitly say that the later result removes the symmetry
assumption also for the two-well formula.

The long sentence beginning “We also consider” currently reintroduces D with
changed assumptions. Split it into two sentences and give the assumptions
before the formula. “Translates of D” already specifies the common
orientation; explain that convention once and avoid repeatedly expanding it
into “identically oriented translates of a common well.”

Two further refinements:

- Replace “a second-order expansion of the interaction kernel” with “a Taylor
  expansion with a quadratic remainder.” The latter describes the displayed
  leading-term estimate without suggesting that a second correction
  coefficient is being stated.
- Identify c₍d,s₎ as the singular-integral normalization in a short clause if
  space permits. Its full formula can remain in Section 2.

The existing abstract is not over arXiv's length limit: the release audit
counts 1,537 characters after whitespace normalization, excluding the keywords
and MSC block. The reason to revise it is emphasis and readability.

## 3. Rebalance the introduction and contribution paragraph

**Location:** pp. 1–2;
[paper.tex:173](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L173) and
[paper.tex:219](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L219).

The introduction contains a useful, specific bibliography. Its presentation
nevertheless makes the reader pass through two dense literature paragraphs
before reaching the contribution paragraph. Move a short statement of the
main results immediately after the opening explanation of nonlocal coupling.
The detailed comparisons can then answer a question the reader already
understands.

There are four nearby negative novelty formulations: the qualification after
Léculier–Roquejoffre, the summary beginning “Together these works,” the
sentence beginning “The cited works do not derive,” and the final statement
that no earlier result is known. They partly repeat one another. Retain the
specific distinctions between the different operators and the bounded final
priority statement, and consolidate the general negative summaries. The
current wording “We are not aware of an earlier result” is appropriately
limited; it should not be strengthened into an absolute firstness claim.

The three-part contribution paragraph also gives the numerical illustrations
the same billing as the two principal theorems, while omitting the
Hong–Krahn–Szegő rate corollary from that paragraph. The rate is a clearer
third mathematical consequence to highlight. For example:

> Theorem 3.3 gives explicit bounds for the two eigenvalue shifts in the
> centrally symmetric case. Theorem 4.6 approximates the first N eigenvalues
> for a fixed family of translates by the spectrum of an explicit interaction
> matrix; Corollary 4.7 gives the two-well asymptotic without central symmetry.
> For two equal balls, Corollary 3.4 identifies the leading rate along the
> Hong–Krahn–Szegő minimizing sequence. Section 5 illustrates the two- and
> three-well asymptotics by Galerkin computations at fixed mesh.

Keep a brief explanation of why both the symmetric two-well treatment and
the general finite-well treatment appear. The last introduction paragraph
already provides this explanation; bring its symmetry distinction forward
instead of making a reader discover it after the contribution list.

## 4. Make the numerical section and captions unambiguous

**Locations:** pp. 13–15;
[paper.tex:1026](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L1026),
[paper.tex:1148](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L1148), and
[paper.tex:1193](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L1193).

The explicit fixed-mesh scope is useful and should remain. The beginning of
Section 5 can be more direct about which statement the tables illustrate:

> We illustrate the fixed-mesh cluster asymptotic of Corollary 5.2 using
> conforming Galerkin matrices assembled from exact cell integrals. The mesh
> is held fixed as L increases; no discretization-error estimate as h → 0 is
> asserted.

At line 1148, “The direct Galerkin eigenvalues are shown in Table 2” is not
what the table displays. Its columns contain scaled differences from the
one-well eigenvalue. Replace that sentence with:

> Table 2 lists the scaled shifts computed from the Galerkin eigenvalues.

Define the last column explicitly, preferably immediately before the table:

> Eₕ(L) = max₁≤k≤N |L³ᐟ²(λₖ,ₕ(L) − μ₁,ₕ) − θₖ,ₕ|.

Then label the column Eₕ(L), or “maximum scaled-shift error.” The current
“maximum error” is understandable with the surrounding prose, but a table
read in isolation does not say whether the comparison is with a continuum
eigenvalue, a discrete eigenvalue, or a scaled leading coefficient. The
caption should include s = 1/4 and the unit reference interval as well as
the mesh and configurations.

For the two lists of effective-matrix eigenvalues immediately before Table 2,
label the configurations by the fixed sites (−1/2, 1/2) and (−1, 0, 1).
The current labels (−L/2, L/2) and (−L, 0, L) are physical centers and can
obscure why the listed effective coefficients are independent of L.

The ten decimal places in Table 1 are legitimate output from finite matrices,
but are visually disproportionate to the six decimal places in Table 2.
Reducing Table 1 to six or seven decimal places is an optional improvement;
retain the full output in the ancillary file. This is a display recommendation,
not a criticism of the calculations or a claim of continuum accuracy.

At line 1123, replace “The stabilization of m₁,ₕ is the relevant check” with
“The table also records the dependence on mesh size of m₁,ₕ, which enters
the interaction coefficient.” This avoids giving a qualitative observation
more evidential weight than the section intends.

## 5. Bibliographic identity and publication data

The manuscript cites 13 entries, and all 13 appear in both `references.bib`
and the generated `paper.bbl`. I compared the author/title records and the
publication or preprint details against the primary records below. Some
publisher pages reject direct access; author-maintained institutional records
and publisher-deposited DOI metadata supplied the indicated alternatives.

| Citation | Records consulted and bibliographic finding |
| --- | --- |
| AFN20 | The [authors' institutional record](https://boa.unimib.it/handle/10281/285117) gives *Communications in Contemporary Mathematics* 22(8), article 1950071 (2020), with the manuscript's title and DOI. The [arXiv record](https://arxiv.org/abs/1902.03550) matches the author list and linked preprint. |
| BDVV23 | The [publisher's citation](https://www.aimspress.com/article/doi/10.3934/mine.2023014) gives *Mathematics in Engineering* 5(1), 1–25 (2023). It explicitly uses **Szegö** in the title. Keep that spelling in this reference even though the manuscript uses Szegő for the named inequality. The publisher lists an online publication date in 2022, but its recommended volume citation uses 2023. |
| BP16 | The [publisher's record](https://www.degruyterbrill.com/document/doi/10.1515/acv-2015-0007/html) gives *Advances in Calculus of Variations* 9(4), 323–355 (2016). The [linked arXiv version](https://arxiv.org/abs/1409.6284v2) is v2. Keep the journal year 2016 despite the earlier online date. |
| DFW21 | The [publisher's record](https://link.springer.com/article/10.1007/s00526-021-02094-3) gives *Calculus of Variations and Partial Differential Equations* 60, article 231 (2021). The [arXiv record](https://arxiv.org/abs/2002.07719) has a later v2; the journal year remains 2021. |
| DNPV12 | The [publisher's record](https://www.sciencedirect.com/science/article/pii/S0007449711001254) gives *Bulletin des Sciences Mathématiques* 136(5), 521–573 (2012), with the stated DOI. The [arXiv author list](https://arxiv.org/abs/1104.4345) matches; “Di Nezza” is rendered correctly in the bibliography. |
| DPLSV26 | The [arXiv record](https://arxiv.org/abs/2602.18035v1) matches the four authors, title, identifier, category, and submission date of 20 February 2026. Its treatment as a preprint matches the record accessed. |
| GS19 | The [publisher-deposited DOI metadata](https://api.crossref.org/works/10.1090/proc/14542) gives *Proceedings of the American Mathematical Society* 147(10), 4315–4327 (2019). The awkward wording “of combination between” is part of the actual title and should not be copyedited. The [arXiv record](https://arxiv.org/abs/1901.03444) also uses K. Sreenadh. |
| Kwa12 | The [publisher-deposited DOI metadata](https://api.crossref.org/works/10.1016/j.jfa.2011.12.004) gives *Journal of Functional Analysis* 262(5), 2379–2402 (2012). The [arXiv record](https://arxiv.org/abs/1012.1133) matches the title and the spelling Kwaśnicki. |
| LR23 | The [publisher's record](https://link.springer.com/article/10.1007/s00526-022-02374-6) matches the manuscript's title and gives volume 62, article 30 (2023). Its online date is November 2022. The [arXiv version](https://arxiv.org/abs/2004.14771) has the earlier title *Properties of steady states for a class of non-local Fisher-KPP equations in disconnected domains*. That difference is not an incorrect reference. |
| PS20 | The [publisher's record](https://onlinelibrary.wiley.com/doi/abs/10.1002/mana.201800234) gives *Mathematische Nachrichten* 293(11), 2208–2232 (2020), matching the bibliography. The [arXiv record](https://arxiv.org/abs/1806.01165) matches the authors and title. |
| Wu26 | The [publisher's indexed record](https://www.sciencedirect.com/science/article/abs/pii/S009630032600247X) gives *Applied Mathematics and Computation* 531, article 130195 (2026), with the stated title and DOI. The issue is dated 15 December 2026, but publication details are already assigned. This does not call for replacing the entry by an invented preprint citation. Direct access to the full article was unavailable in this review. |
| Zah26 | The [publisher's record](https://link.springer.com/article/10.1007/s00526-026-03270-z) gives *Calculus of Variations and Partial Differential Equations* 65, article 98 (2026). The [arXiv record](https://arxiv.org/abs/2504.09840) matches the author and title. |
| Zha26 | The [arXiv record](https://arxiv.org/abs/2608.23457v1) matches Cheng Zhang, the title, identifier, category, and submission date of 24 August 2026. Its treatment as a preprint matches the record accessed. |

The two preprint entries already distinguish versions explicitly. Full given
names, protected capitalization of mathematical proper names, DOI links, and
arXiv links are otherwise presented consistently. The alphabetic citation
style is acceptable; changing the entire bibliography style is not a necessary
pre-submission revision.

## 6. Improve citation locators and context

**Version-dependent pages.** The citation at
[paper.tex:271](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L271) refers to “[BP16, Section 1.1,
p. 2].” The coefficient definition is on p. 2 of
[arXiv:1409.6284v2](https://arxiv.org/pdf/1409.6284v2); the journal entry has
printed pages 323–355. Likewise, the mutual-position discussion cited at
[paper.tex:198](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L198) occurs on p. 3 of
[arXiv:1902.03550v2](https://arxiv.org/pdf/1902.03550v2). These are usable
locators, but the manuscript should identify which version supplies the page
numbers. Add the version to these citations or add a concise version note to
the corresponding bibliography entries. Do not change the journal publication
year to the arXiv year.

**Parini–Salort attribution.** I checked the actual headings and statements
of [Theorems 1.1 and 1.2](https://arxiv.org/pdf/1806.01165): they are the
Sobolev-sequence trichotomy and the quasi-open-set compactness/dichotomy result,
respectively. The introduction's current attribution fits those locators.

**Interval asymptotics.** At
[paper.tex:1030](https://github.com/skypher/laplace-tunneling/blob/paper-2026-09-04-r5/paper.tex#L1030), specify that the
Kwaśnicki and Zhang references concern **high-index eigenvalue asymptotics
on a single interval**. Their [arXiv abstracts](https://arxiv.org/abs/1012.1133)
[describe that regime](https://arxiv.org/abs/2608.23457), whereas the current
paper varies the separation of wells. “Sharper eigenvalue asymptotics” without
that qualifier momentarily blurs the distinction. This is a context edit, not
a request for another numerical comparison.

**Wu locator.** The existing “Introduction” locator is broad. A numbered
result would be more helpful if the author has the final article available,
but I have not assigned a replacement theorem number from inaccessible text.
The publication metadata check above is not an independent check of the
conjecture-resolution claim.

**Article numbers.** The entries ending in 231, 30, 98, 1950071, and 130195
use article numbers. The current volume:article format is common and not an
error. Writing “article 231,” etc., would improve clarity if the bibliography
format is being adjusted anyway.

## 7. Focused wording edits

These are local suggestions, not requests to alter any hypotheses or proofs.

| Location | Current wording | Suggested wording or reason |
| --- | --- | --- |
| p. 1, lines 170–171 | “one centrally symmetric component” | “a common reference well”; state the role of symmetry alongside the exact sector decomposition. Also avoid implying that every allowed reference set must be connected. |
| p. 2, lines 222–224 | “identifies the entire ground-state cluster … with the spectrum” | “approximates the first N eigenvalues … by the spectrum.” This describes the finite-L estimate directly. |
| p. 2, line 224 | “uniform cluster-error bounds” | “error bounds uniform over the N eigenvalues for each fixed configuration.” The intended variable of uniformity becomes explicit. |
| pp. 2 and 5, lines 229 and 391 | “scalar … branches” | “symmetric and antisymmetric sector operators,” or simply “the two branches.” The operators still act on L²(D). |
| p. 2, line 231 | “first-order kernel term” | “linear term in the kernel expansion.” This is easier to parse. |
| p. 3, lines 285–286 | “Write its eigenvalues with multiplicity and denote the first two distinct levels” | After stating simplicity, identify μ₁ and μ₂ directly as the first and second eigenvalues of Aᴅ. The existing wording asks the reader to reconcile two indexing conventions. |
| p. 4, lines 367–368 | “the square interaction with the location occupied by the other component” | “the terms involving the squared modulus of the function and integration over the other component.” This makes the cancellation described next easier to anticipate. |
| p. 7, line 558 | “The two branch ground-state energies” | An optional short clarification is “Let E₊ denote the symmetric-branch ground-state energy and E₋ the antisymmetric-branch ground-state energy.” |
| p. 12, line 1003 | “Suppose the centers satisfy” | “Suppose the sites satisfy.” The symbols aᵢ are the fixed sites used before multiplication by L. |
| p. 14, line 1148 | “The direct Galerkin eigenvalues” | “The scaled shifts computed from the Galerkin eigenvalues.” |
| p. 15, line 1218 | “reference output … was replayed with” | “reference output was reproduced using.” “Replayed” is repository terminology. |

Define the title's usage of *tunneling* in one sentence near the beginning if
desired: it is the splitting of the one-well level through the nonlocal
interaction between distant copies. The current comparison with the local
Dirichlet operator is useful; the paper does not need an unrelated discussion
of potential-barrier models to justify its terminology.

## 8. Page layout and back matter

The running heads, equation numbers, tables, mathematical accents, and
bibliography are legible. All listed PDF fonts are embedded Type 1 fonts.
I saw no clipped equation, table, or bibliography line. The form glyph in
item 1 is the substantive typography defect.

After textual revisions, attend to these smaller layout points:

- On pp. 5–6, Lemma 3.2 begins near the bottom of p. 5, but its assertions
  start on p. 6. Starting the lemma on p. 6 would improve reading continuity.
- The statement of Theorem 4.6 spans pp. 10–11. Keeping the full statement
  together would be useful if it fits naturally after editing.
- Corollary 5.2 is split across pp. 13–14, with the definition of θₖ,ₕ on
  the second page. The source's `\enlargethispage{3\baselineskip}` at line
  1077 also makes p. 13 extend below the usual text block. Reconsider that
  manual adjustment after the text is settled.
- The references start with one entry at the foot of p. 15 and continue on
  p. 16. This is acceptable. Reassess the balance after shortening the code
  availability paragraph rather than imposing a page break now.
- The two 36-point title-block skips and the 50-point skip before the
  introduction create a spacious first page and leave the first literature
  paragraph split across pp. 1–2. Slightly reducing this spacing would make
  the first page more efficient. It is a style preference, not an arXiv
  defect.

The code availability paragraph currently describes internal checks, progress
printing, three environment versions, the archived payload, a release tag,
and a long URL. Retain the reproducibility information but move the progress
printing and assembly-check description to the ancillary README. A compact
replacement could read:

> The ancillary files contain the script check_asymptotics.py, pinned
> dependencies, and reference output reproducing Tables 1 and 2. The output
> was reproduced using Python 3.12.3, NumPy 1.26.4, and SciPy 1.11.4. The
> corresponding source is available in the tagged repository release
> paper-2026-09-04-r5.

Keep the existing hyperlink on the release tag. The actual tagged manuscript
source was retrieved successfully and byte-matched the working `paper.tex`.
The AI-use disclosure specifies the uses and the author's responsibility;
its factual content should be retained. A separate conclusion section is
not necessary for this manuscript.

## 9. Submission-package findings

The following checks were performed in this review, independently of the
older release notes:

| Check | Outcome |
| --- | --- |
| Archive payload | All seven files byte-match their working-tree counterparts; the archive contains the three manuscript/bibliography files and the four ancillary files. |
| Clean source build | The extracted archive builds to 16 pages using the repository's existing PDF recipe, without relying on files outside the package other than the installed TeX distribution. |
| Final diagnostics | No final LaTeX warnings, unresolved references/citations, or overfull/underfull box diagnostics; no BibTeX warnings. |
| Reproduction of document | The rebuilt `.bbl` and layout-preserving PDF text match the supplied versions. |
| Existing release audit | Passed: 13 citations, 55 labels, 15 result/proof pairs, 11 numerical table rows, 1,537 abstract characters, 16 pages. The numerical-row check compares against saved output; no new numerical run was made. |
| Author/title metadata | The PDF title and author agree with the manuscript; the fixed date is consistent with the named release. |
| Public source | The tagged GitHub page returns HTTP 200; its raw manuscript file byte-matches the working source. |

The source/bibliography files at the archive root and the ancillary material
under `anc/` fit arXiv's documented
[TeX submission](https://info.arxiv.org/help/submit_tex.html) and
[ancillary-file](https://info.arxiv.org/help/ancillary_files.html) conventions.
The local build is not a run of arXiv's processing system; inspect the PDF
generated during the actual submission, particularly after any page-layout
changes.

For the submission form, copy only the abstract prose and formulas, omitting
the `abstract` environment, keywords, MSC block, and layout commands. arXiv's
[metadata instructions](https://info.arxiv.org/help/prep.html#abstract-required)
specify the 1,920-character limit and the supported text/TeX conventions.
The current source abstract contains no project-specific macros. A suitable
comments entry for the current layout is “16 pages, 2 tables; numerical code
and reference output included as ancillary files.” Update the page count if
the revised build changes it.

The reviewed submission archive is
`dist/laplace-tunneling-arxiv.tar.gz`. A second, older archive named
`dist/tunnel-arxiv.tar.gz` is also present locally; it was not the archive
reviewed here. After implementing edits, regenerate the named submission
archive so that the uploaded source corresponds to the revised PDF.

## 10. Suggested revision order

1. Replace the eight malformed form symbols and explicitly identify φ₁ in
   the abstract.
2. Clarify Table 2's scaled quantities and error column.
3. Bring the symmetry-free scope forward, consolidate the introduction's
   novelty comparisons, and include the distant-ball rate in the result
   overview.
4. Identify the arXiv versions used for page-specific citations and clarify
   the high-index regime of the interval references.
5. Shorten the code availability paragraph, settle the remaining copyedits,
   and adjust the resulting page breaks.
6. Rebuild, inspect the revised PDF, and regenerate the submission archive.

## Record of reviewed artifacts

SHA-256 digests:

```text
paper.tex
ffb8c867448f33f64e60139a33e08fe1ad20aac044730cc14bc4ae87592f5db8
paper.pdf
ef7e1090e0126e48ce6b223b7280c120b48ff4771b6d17345713ea0fcc84fb89
references.bib
2a8e60b3d31e1e7d044249357f3d5cab65c273bf0052d9c182a5d313886c7bca
dist/laplace-tunneling-arxiv.tar.gz
29de10e7a2e6a04907d6f0e64da27a1d27c694bebeada44b604b21020ea9af20
```

## Revision response — release `paper-2026-09-05`

| Review item | Revision |
| --- | --- |
| 1. Form symbol | Replaced all eight lowercase calligraphic occurrences by `\mathcal{Q}` and added a release check for this font-sensitive mistake. The rendered form is now Q. |
| 2. Abstract | Identified φ₁ as the ground-state eigenfunction, led with Corollary 4.7's general two-well scope, separated the symmetric-sector statement, identified the normalization, and described the Taylor remainder precisely. The revised abstract has 1,407 characters under the existing audit's counting convention. |
| 3. Introduction | Moved the result overview before the literature, added the distant-ball rate, explained the symmetry distinction early, and consolidated the novelty comparisons. |
| 4. Numerical presentation | Defined Eₕ(L) in equation (5.4), corrected the description of scaled shifts, labeled the effective spectra by fixed sites, expanded the caption, and rounded Table 1 to six decimal places. All displayed rows remain consistent with the saved output. |
| 5–6. Bibliography and context | Pinned the two page-specific citations and their bibliography links to arXiv v2, clarified the high-index interval regime, and corrected the Parini–Salort theorem numbering in the literature audit. Publication identities and the existing article-number style were retained. The existing Introduction locator for Wu was retained because the accessible material did not support a replacement theorem number. |
| 7. Wording | Applied the local edits concerning the one-well levels, sector operators, uniformity, linear kernel term, cross-energy description, branch labels, sites, and reproduction terminology. |
| 8. Layout and back matter | Reduced title-page spacing, kept the three flagged statements together, removed the page enlargement, and moved internal reproduction details to the ancillary README. All thirteen bibliography entries now fit on page 16. |
| 9–10. Release | Updated the manuscript date and release tag, regenerated the PDF and archive, inspected all pages, and built the extracted archive in a fresh directory. |

Checks performed before recording the revision result: the final LaTeX and
BibTeX logs are clean; the release audit passes with 13 citations, 56 labels,
15 result/proof pairs, 11 numerical rows, and 16 pages.  Every archived file
byte-matches its working source.  The fresh archive build reproduces the
generated bibliography and extracted PDF text, and repacking with the release
metadata reproduces the archive bytes.  The current artifact hashes are
recorded in `notes/final_audit.md`.
