#!/usr/bin/env python3
"""Mechanical release audit for the laplace-tunneling manuscript."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def read(relative: str) -> str:
    return (ROOT / relative).read_text(encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()

    paper = read("paper.tex")
    readme = read("README.md")
    bibliography = read("references.bib")
    built_bibliography = read("paper.bbl")
    build_log = read("paper.log")
    numerics = read("numerics/asymptotics_180.txt")
    failures: list[str] = []

    def require(condition: bool, message: str) -> None:
        if not condition:
            failures.append(message)

    required_files = [
        "paper.tex",
        "paper.pdf",
        "paper.bbl",
        "references.bib",
        "README.md",
        "tools/check_asymptotics.py",
        "tools/audit_release.py",
        "requirements-numerics.txt",
        "numerics/asymptotics_180.txt",
        "anc/README.txt",
    ]
    for relative in required_files:
        require((ROOT / relative).is_file(), f"missing release file: {relative}")

    cited: set[str] = set()
    for group in re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", paper):
        cited.update(key.strip() for key in group.split(","))
    bib_keys = set(re.findall(r"@\w+\{([^,]+),", bibliography))
    bbl_keys = set(re.findall(r"\\bibitem(?:\[[^]]*\])?\{([^}]+)\}", built_bibliography))
    require(cited == bib_keys, f"citation/BibTeX mismatch: cited={sorted(cited)}, bib={sorted(bib_keys)}")
    require(cited == bbl_keys, f"citation/bbl mismatch: cited={sorted(cited)}, bbl={sorted(bbl_keys)}")
    eprint_ids = set(re.findall(r"eprint\s*=\s*\{([^}]+)\}", bibliography))
    for identifier in eprint_ids:
        require(
            f"arXiv:{identifier}" in built_bibliography,
            f"arXiv identifier absent from generated bibliography: {identifier}",
        )

    labels = set(re.findall(r"\\label\{([^}]+)\}", paper))
    references = {
        label
        for label in re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", paper)
        if not label.startswith("#")
    }
    require(references <= labels, f"undefined source labels: {sorted(references - labels)}")

    environment_tokens = re.findall(r"\\(begin|end)\{([^}]+)\}", paper)
    stack: list[str] = []
    for action, environment in environment_tokens:
        if action == "begin":
            stack.append(environment)
        elif not stack or stack.pop() != environment:
            failures.append(f"unbalanced environment near \\end{{{environment}}}")
            break
    require(not stack, f"unclosed environments: {stack}")

    result_environments = ("theorem", "lemma", "proposition", "corollary")
    result_count = sum(paper.count(f"\\begin{{{name}}}") for name in result_environments)
    proof_count = paper.count("\\begin{proof}")
    require(result_count == proof_count, f"result/proof mismatch: {result_count}/{proof_count}")

    forbidden_markers = ("TODO", "FIXME", "TBD", "\\begin{assumption}", "\\begin{hypothesis}")
    for marker in forbidden_markers:
        require(marker not in paper, f"open marker in manuscript: {marker}")

    submission_metadata = (
        "pdfauthor={Leslie P. Polzer}",
        "\\author{Leslie P. Polzer}",
        "\\newcommand{\\authoraffiliation}{Independent Researcher}",
        "\\newcommand{\\authoremail}{polzer@fastmail.com}",
        "\\date{September 4, 2026}",
        "\\newcommand{\\shortauthors}{LESLIE P. POLZER}",
        "https://github.com/skypher/laplace-tunneling/tree/paper-2026-09-04-r5",
    )
    for fragment in submission_metadata:
        require(fragment in paper, f"missing submission metadata: {fragment}")
    require("mailto:" not in paper, "reference style requires an uncolored title-page email")
    require("\\usepackage{microtype}" not in paper, "reference style excludes microtype")

    reference_style = (
        "\\documentclass[twoside,10pt]{article}",
        "\\usepackage[T1]{fontenc}",
        "\\usepackage{lmodern}",
        "\\usepackage[small,labelfont=bf,labelsep=period]{caption}",
        "total={5.5in,8in}",
        "headsep=21pt",
        "\\newtheoremstyle{slbody}",
        "\\baselineskip=13.5pt",
    )
    for fragment in reference_style:
        require(fragment in paper, f"missing Virasoro-style primitive: {fragment}")

    ai_disclosure = (
        "\\section*{Use of artificial intelligence}",
        "OpenAI's GPT-5.6 Sol model",
        "\\texttt{gpt-5.6-sol}",
        "to explore and test arguments",
        "audit citations and calculations",
        "prepare reproducibility and release-checking code",
        "takes responsibility for all mathematical claims, citations, computations, and wording",
    )
    normalized_paper = re.sub(r"\s+", " ", paper)
    for fragment in ai_disclosure:
        require(fragment in normalized_paper, f"missing AI-disclosure text: {fragment}")
    forbidden_product_name = "co" + "dex"
    require(
        forbidden_product_name not in paper.lower(),
        "AI disclosure contains a prohibited product-name reference",
    )
    code_availability = (
        "assembled constant-function energy identity",
        "exact reuse of each translated one-well block",
        "Python~3.12.3, NumPy~1.26.4, and SciPy~1.11.4",
        "paper-2026-09-04-r5",
        "check_asymptotics.py",
        "requirements-numerics.txt",
        "asymptotics_180.txt",
        "these archived files correspond to the manuscript",
    )
    for fragment in code_availability:
        require(
            fragment in normalized_paper,
            f"missing code-availability text: {fragment}",
        )
    require(
        "identically oriented translates of a common well" in normalized_paper,
        "missing multi-well orientation scope",
    )
    require(
        "many congruent wells" not in normalized_paper,
        "multi-well claim overstates the proved translation geometry",
    )
    require(
        "compact-kernel nonlocal" not in normalized_paper,
        "ambiguous compact-kernel wording remains",
    )
    require(
        "identically oriented translates of a common well" in readme,
        "README overstates the multi-well geometry",
    )
    require(
        "paper-2026-09-04-r5" in readme,
        "README release tag is stale",
    )

    metadata_abstract_length = 0
    abstract_match = re.search(
        r"\\begin\{abstract\}(.*?)\\vskip5pt",
        paper,
        flags=re.DOTALL,
    )
    require(abstract_match is not None, "cannot extract metadata abstract")
    if abstract_match is not None:
        metadata_abstract = re.sub(r"\s+", " ", abstract_match.group(1)).strip()
        metadata_abstract_length = len(metadata_abstract)
        require(
            metadata_abstract_length <= 1920,
            f"metadata abstract exceeds 1920 characters: {metadata_abstract_length}",
        )
        for opaque_macro in (r"\R", r"\abs", r"\Hs", r"\ip", r"\norm", r"\!"):
            require(
                opaque_macro not in metadata_abstract,
                f"opaque macro in metadata abstract: {opaque_macro}",
            )

    critical_log_patterns = (
        "LaTeX Warning",
        "Package hyperref Warning",
        "Overfull \\hbox",
        "Overfull \\vbox",
        "Underfull \\hbox",
        "Underfull \\vbox",
        "undefined references",
        "undefined citations",
        "multiply defined",
    )
    for pattern in critical_log_patterns:
        require(pattern not in build_log, f"final build diagnostic: {pattern}")
    expected_pages = 16
    require(
        f"Output written on paper.pdf ({expected_pages} pages" in build_log,
        "unexpected final PDF page count",
    )

    expected_numerical_fragments = [
        "60 1.3794549573 0.9105539931 0.9628386433",
        "120 1.3753692130 0.8998883318 0.9633505837",
        "180 1.3741292905 0.8969647744 0.9636021778",
        "configuration=two_wells theta=[-0.18521477 +0.18521477]",
        "3.0 [-0.19073969 +0.18983213] 5.52492390e-03",
        "6.0 [-0.18654355 +0.18633540] 1.32877928e-03",
        "12.0 [-0.18555071 +0.18548609] 3.35940722e-04",
        "24.0 [-0.18530156 +0.18527949] 8.67909149e-05",
        "configuration=three_collinear_wells theta=[-0.29671332 +0.06548331 +0.23123001]",
        "3.0 [-0.30498358 +0.06556153 +0.23754436] 8.27026105e-03",
        "6.0 [-0.29873846 +0.06555350 +0.23274709] 2.02514771e-03",
        "12.0 [-0.29723551 +0.06550397 +0.23159465] 5.22191390e-04",
        "24.0 [-0.29685154 +0.06548844 +0.23131623] 1.38220035e-04",
        "completed elapsed_seconds=",
    ]
    for fragment in expected_numerical_fragments:
        require(fragment in numerics, f"missing reference-output fragment: {fragment}")

    manuscript_fragments = [
        "c_{d,s}=4^s s\\,\\Gamma(d/2+s)/(\\pi^{d/2}\\Gamma(1-s))",
        "C_{\\kappa,R}=2^{\\kappa+3}\\kappa(\\kappa+1)R^2",
        "\\label{eq:explicit-L0}",
        "\\label{eq:two-well-third-level}",
        "\\cite[Theorem~1.4]{GoelSreenadh2019}",
        "\\abs{u(x)-v(y)}^2-\\abs{u(x)}^2-\\abs{v(y)}^2",
        "\\ip{\\psi}{W\\psi}-w",
        "\\eta_N-\\frac{2b^2}{g}",
        "\\lambda_{N+1}(\\Omega_{\\mathbf a,L})-",
        "\\geq g-2\\gamma_L\\geq\\frac g2",
        "1.3794549573 & 0.9105539931 & 0.9628386433",
        "1.3753692130 & 0.8998883318 & 0.9633505837",
        "1.3741292905 & 0.8969647744 & 0.9636021778",
        "(-0.18521477,0.18521477)",
        "(-0.29671332,0.06548331,0.23123001)",
        "$-0.190740$ & $ 0.189832$ & $5.52\\times10^{-3}$",
        "$-0.186544$ & $ 0.186335$ & $1.33\\times10^{-3}$",
        "$-0.185551$ & $ 0.185486$ & $3.36\\times10^{-4}$",
        "$-0.185302$ & $ 0.185279$ & $8.68\\times10^{-5}$",
        "$-0.304984$ & $0.065562$ & $0.237544$ & $8.27\\times10^{-3}$",
        "$-0.298738$ & $0.065554$ & $0.232747$ & $2.03\\times10^{-3}$",
        "$-0.297236$ & $0.065504$ & $0.231595$ & $5.22\\times10^{-4}$",
        "$-0.296852$ & $0.065488$ & $0.231316$ & $1.38\\times10^{-4}$",
    ]
    for fragment in manuscript_fragments:
        require(fragment in paper, f"missing manuscript table fragment: {fragment}")

    if failures:
        for failure in failures:
            print(f"FAIL {failure}", flush=True)
        sys.exit(1)

    print(
        "release audit passed: "
        f"citations={len(cited)} labels={len(labels)} results={result_count} "
        f"numerical_rows=11 abstract_chars={metadata_abstract_length} "
        f"pages={expected_pages}",
        flush=True,
    )


if __name__ == "__main__":
    main()
