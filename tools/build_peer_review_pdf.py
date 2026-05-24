#!/usr/bin/env python3
from __future__ import annotations

import re
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from textwrap import wrap

from reportlab.lib import colors
from reportlab.lib.pagesizes import letter
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen import canvas


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "output" / "pdf" / "TINProofs_C1_C5_peer_review_packet.pdf"

BODY_FONT = "NotoSans"
BODY_BOLD = "NotoSans-Bold"
CODE_FONT = "FreeSerif"
CODE_BOLD = "NotoSans-Bold"

PAGE_W, PAGE_H = letter
MARGIN_X = 42
TOP_Y = PAGE_H - 44
BOTTOM_Y = 46
TEXT_W = PAGE_W - 2 * MARGIN_X

PROBLEMS = [
    (
        "C1",
        "Commodity Hull Theorem",
        [
            "TINProofs/C1/Defs.lean",
            "TINProofs/C1/ActionAffine.lean",
            "TINProofs/C1/SupportConcave.lean",
            "TINProofs/C1/Crossover.lean",
        ],
        [
            "Finite path data are represented by PathData with exposure T, survival Q, and positivity bounds.",
            "A_pi(lambda) = -log Q_pi + lambda*T_pi and V_pi(lambda) = log Q_pi - lambda*T_pi.",
            "The support F(lambda) is Finset.inf' of path actions; the value V(lambda) is Finset.sup' of path values.",
            "The formal crossover slope is the sign required by the action equality proof.",
        ],
        [
            "Check the sign convention against the manuscript prose. The Lean proof uses the slope that makes action_eq_at_crossover true for A = -log Q + lambda*T.",
        ],
    ),
    (
        "C2",
        "Stochastic Certification Asymmetry",
        [
            "TINProofs/C2/Defs.lean",
            "TINProofs/C2/GapTiers.lean",
            "TINProofs/C2/AsymmetryRatio.lean",
            "TINProofs/C2/Absorbing.lean",
            "TINProofs/C2/PoissonLimit.lean",
            "TINProofs/C2/Expansion.lean",
        ],
        [
            "Tier thresholds, delivery ratio, Binomial PMF/CDF/tails, asymmetry ratio, and achievable delivery ratios are formalized explicitly.",
            "The absorbing-tier and gap-tier claims are reduced to ceiling and finite-grid arithmetic.",
            "The Poisson-limit layer isolates distributional convergence and crossover existence conditions.",
            "The expansion layer records the external asymptotic input as a named hypothesis and proves the algebraic delivery-ratio consequence.",
        ],
        [
            "Median and mode facts remain explicit hypotheses rather than first-class Binomial median/mode definitions.",
            "The asymptotic theorem depends on the named Adell-Jodra-style input; review whether this is the intended trust boundary.",
        ],
    ),
    (
        "C3",
        "Lyapunov Radius of Validity",
        [
            "TINProofs/C3/Defs.lean",
            "TINProofs/C3/EigenSandwich.lean",
            "TINProofs/C3/VDotDecomp.lean",
            "TINProofs/C3/QuadBound.lean",
            "TINProofs/C3/RemainderBound.lean",
            "TINProofs/C3/BallBound.lean",
            "TINProofs/C3/RadiusOfValidity.lean",
        ],
        [
            "The setup stores eigenvalue, decay, coupling, and cubic-remainder constants as real inequalities.",
            "The proof stack separates eigenvalue sandwiching, Vdot decomposition, quadratic lower bounds, remainder bounds, and ball-local derivative control.",
            "The main radius theorem proves nonpositive Vdot inside the critical radius and then derives sublevel-set corollaries.",
        ],
        [
            "All analytic inputs are scalar inequalities in the setup; review whether the abstraction matches the paper's intended matrix and Taylor hypotheses.",
        ],
    ),
    (
        "C4",
        "Temporal Transport Factorization",
        [
            "TINProofs/C4/Defs.lean",
            "TINProofs/C4/Inclusion.lean",
            "TINProofs/C4/Factorization.lean",
            "TINProofs/C4/Monotonicity.lean",
            "TINProofs/C4/BraessLocalization.lean",
        ],
        [
            "Temporal transport is represented over abstract measurable events D, F, and E with delivery included in feasibility and efficiency.",
            "The factorization proves DR = ST * eta under nonzero feasibility mass, both in ENNReal and real-valued forms.",
            "Augmentation monotonicity is isolated to the feasible-reachability factor, and Braess-style decreases are localized in efficiency.",
        ],
        [
            "The model is event-level rather than graph-level. Peer review should check whether the event abstraction captures every manuscript dependency.",
        ],
    ),
    (
        "C5",
        "Three-Factor Sparse Law",
        [
            "TINProofs/C5/Defs.lean",
            "TINProofs/C5/ThreeFactor.lean",
            "TINProofs/C5/ChainProperties.lean",
            "TINProofs/C5/Classification.lean",
        ],
        [
            "The scalar sparse-law setup stores S_T, eta, E_H, Lyapunov exponent, DR, and their bounds.",
            "etaLyap = exp(E_H * lyap), Phi = eta / etaLyap, and the main theorem proves DR = S_T * etaLyap * Phi.",
            "Additional lemmas capture positivity, etaLyap < 1, and morphology vocabulary for trap/cluster classification.",
        ],
        [
            "The formal theorem is scalar and algebraic. Review whether any probabilistic interpretation should remain outside this theorem statement.",
        ],
    ),
]


DECL_RE = re.compile(r"^(structure|def|theorem|lemma|axiom|inductive)\s+")


@dataclass
class Declaration:
    kind: str
    name: str
    file: str
    line: int
    statement: str


def register_fonts() -> None:
    pdfmetrics.registerFont(TTFont(BODY_FONT, "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf"))
    pdfmetrics.registerFont(TTFont(BODY_BOLD, "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf"))
    pdfmetrics.registerFont(TTFont(CODE_FONT, "/usr/share/fonts/truetype/freefont/FreeSerif.ttf"))
    pdfmetrics.registerFont(TTFont(CODE_BOLD, "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf"))


def read_file(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def clean_text(text: str) -> str:
    return text.replace("\t", "  ")


def first_sentence_comment(text: str) -> str | None:
    m = re.search(r"/--\s*(.*?)\s*-/", text, flags=re.S)
    if not m:
        m = re.search(r"/-\s*(.*?)\s*-/", text, flags=re.S)
    if not m:
        return None
    s = " ".join(m.group(1).split())
    return s or None


def collect_declarations(rel: str) -> list[Declaration]:
    lines = read_file(rel).splitlines()
    decls: list[Declaration] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if DECL_RE.match(stripped):
            parts = stripped.split()
            kind = parts[0]
            name = parts[1] if len(parts) > 1 else "<anonymous>"
            collected = [stripped]
            j = i + 1
            if kind in {"theorem", "lemma"}:
                if ":= by" not in stripped:
                    while j < len(lines):
                        nxt = lines[j].strip()
                        if DECL_RE.match(nxt):
                            break
                        if ":= by" in nxt or nxt.endswith(":= by"):
                            before = nxt.split(":= by", 1)[0].rstrip()
                            if before:
                                collected.append(before)
                            break
                        collected.append(nxt)
                        j += 1
            elif kind in {"def", "inductive"}:
                seen_assign = ":=" in stripped
                seen_body = bool(stripped.split(":=", 1)[1].strip()) if seen_assign else False
                while j < len(lines):
                    nxt = lines[j].strip()
                    if DECL_RE.match(nxt) or nxt.startswith("/--") or nxt.startswith("/-"):
                        break
                    if nxt == "" and seen_assign and seen_body:
                        break
                    collected.append(nxt)
                    if ":=" in nxt:
                        seen_assign = True
                        seen_body = seen_body or bool(nxt.split(":=", 1)[1].strip())
                    elif seen_assign and nxt != "":
                        seen_body = True
                    j += 1
            else:
                while j < len(lines):
                    nxt = lines[j].strip()
                    if DECL_RE.match(nxt) or (nxt == "" and len(collected) > 1):
                        break
                    collected.append(nxt)
                    j += 1
            statement = "\n".join(collected)
            statement = statement.split(":= by", 1)[0].rstrip()
            decls.append(Declaration(kind, name, rel, i + 1, statement))
            i = max(j, i + 1)
        else:
            i += 1
    return decls


class PacketPDF:
    def __init__(self, path: Path):
        self.path = path
        self.c = canvas.Canvas(str(path), pagesize=letter)
        self.page_no = 0
        self.y = TOP_Y
        self.section = ""

    def new_page(self, section: str | None = None) -> None:
        if self.page_no:
            self.footer()
            self.c.showPage()
        self.page_no += 1
        if section is not None:
            self.section = section
        self.y = TOP_Y
        self.header()

    def header(self) -> None:
        self.c.setFillColor(colors.HexColor("#2F3A45"))
        self.c.setFont(BODY_BOLD, 8)
        self.c.drawString(MARGIN_X, PAGE_H - 28, "TINProofs C1-C5 formal verification packet")
        self.c.setFont(BODY_FONT, 8)
        self.c.drawRightString(PAGE_W - MARGIN_X, PAGE_H - 28, self.section)
        self.c.setStrokeColor(colors.HexColor("#C7CDD4"))
        self.c.line(MARGIN_X, PAGE_H - 34, PAGE_W - MARGIN_X, PAGE_H - 34)
        self.c.setFillColor(colors.black)

    def footer(self) -> None:
        self.c.setStrokeColor(colors.HexColor("#C7CDD4"))
        self.c.line(MARGIN_X, 34, PAGE_W - MARGIN_X, 34)
        self.c.setFont(BODY_FONT, 8)
        self.c.setFillColor(colors.HexColor("#5E6670"))
        self.c.drawString(MARGIN_X, 22, "Lean 4.29.1 / mathlib v4.29.1")
        self.c.drawRightString(PAGE_W - MARGIN_X, 22, f"page {self.page_no}")
        self.c.setFillColor(colors.black)

    def ensure(self, needed: float, section: str | None = None) -> None:
        if self.y - needed < BOTTOM_Y:
            self.new_page(section)

    def title(self, text: str) -> None:
        self.ensure(54)
        self.c.setFont(BODY_BOLD, 20)
        self.c.setFillColor(colors.HexColor("#18212B"))
        self.c.drawString(MARGIN_X, self.y, text)
        self.c.setFillColor(colors.black)
        self.y -= 32

    def h1(self, text: str) -> None:
        self.ensure(34)
        self.c.setFont(BODY_BOLD, 15)
        self.c.setFillColor(colors.HexColor("#18212B"))
        self.c.drawString(MARGIN_X, self.y, text)
        self.c.setFillColor(colors.black)
        self.y -= 22

    def h2(self, text: str) -> None:
        self.ensure(28)
        self.c.setFont(BODY_BOLD, 11)
        self.c.setFillColor(colors.HexColor("#28323D"))
        self.c.drawString(MARGIN_X, self.y, text)
        self.c.setFillColor(colors.black)
        self.y -= 17

    def paragraph(self, text: str, font: str = BODY_FONT, size: float = 9.4, leading: float = 12.4,
                  color=colors.black, indent: float = 0) -> None:
        text = clean_text(text)
        max_width = TEXT_W - indent
        approx = max(32, int(max_width / (size * 0.52)))
        chunks: list[str] = []
        for raw in text.splitlines() or [""]:
            if not raw:
                chunks.append("")
            else:
                chunks.extend(wrap(raw, width=approx, break_long_words=False, break_on_hyphens=False) or [""])
        for line in chunks:
            self.ensure(leading)
            self.c.setFont(font, size)
            self.c.setFillColor(color)
            self.c.drawString(MARGIN_X + indent, self.y, line)
            self.y -= leading
        self.c.setFillColor(colors.black)

    def bullet(self, text: str) -> None:
        self.ensure(14)
        self.c.setFont(BODY_FONT, 9.3)
        self.c.drawString(MARGIN_X + 8, self.y, "-")
        self.paragraph(text, size=9.3, leading=12.0, indent=22)

    def code(self, text: str, size: float = 7.0, leading: float = 8.6, line_numbers: bool = False,
             start_line: int = 1) -> None:
        text = clean_text(text)
        number_w = 34 if line_numbers else 0
        code_x = MARGIN_X + number_w
        max_width = TEXT_W - number_w
        space_w = pdfmetrics.stringWidth(" ", CODE_FONT, size)
        for n, raw in enumerate(text.splitlines() or [""], start_line):
            prefix = f"{n:4d}  " if line_numbers else ""
            pieces = self.wrap_code_line(raw, max_width, size)
            for k, piece in enumerate(pieces):
                self.ensure(leading)
                self.c.setFont(CODE_FONT, size)
                self.c.setFillColor(colors.HexColor("#1E252D"))
                if line_numbers and k == 0:
                    self.c.setFont(CODE_FONT, size)
                    self.c.setFillColor(colors.HexColor("#727B84"))
                    self.c.drawRightString(MARGIN_X + number_w - 7, self.y, f"{n}")
                    self.c.setFillColor(colors.HexColor("#1E252D"))
                elif line_numbers:
                    self.c.setFillColor(colors.HexColor("#A0A6AD"))
                    self.c.drawRightString(MARGIN_X + number_w - 7, self.y, "...")
                    self.c.setFillColor(colors.HexColor("#1E252D"))
                if k > 0:
                    piece = "  " + piece
                self.c.drawString(code_x, self.y, piece)
                self.y -= leading
        self.c.setFillColor(colors.black)

    def wrap_code_line(self, line: str, max_width: float, size: float) -> list[str]:
        if pdfmetrics.stringWidth(line, CODE_FONT, size) <= max_width:
            return [line]
        out: list[str] = []
        current = ""
        for ch in line:
            if pdfmetrics.stringWidth(current + ch, CODE_FONT, size) <= max_width:
                current += ch
            else:
                if current:
                    out.append(current)
                current = ch
        if current or not out:
            out.append(current)
        return out

    def rule(self) -> None:
        self.ensure(10)
        self.c.setStrokeColor(colors.HexColor("#C7CDD4"))
        self.c.line(MARGIN_X, self.y, PAGE_W - MARGIN_X, self.y)
        self.y -= 12

    def save(self) -> None:
        self.footer()
        self.c.save()


def source_header(rel: str) -> str:
    text = read_file(rel)
    comment = first_sentence_comment(text)
    return comment or rel


def build_pdf() -> Path:
    register_fonts()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    pdf = PacketPDF(OUT)

    all_files = [f for _, _, files, _, _ in PROBLEMS for f in files]
    declarations = {rel: collect_declarations(rel) for rel in all_files}
    theorem_count = sum(1 for ds in declarations.values() for d in ds if d.kind in {"theorem", "lemma"})
    decl_count = sum(len(ds) for ds in declarations.values())
    line_count = sum(len(read_file(rel).splitlines()) for rel in all_files)

    pdf.new_page("Overview")
    pdf.title("TINProofs C1-C5 Formal Verification Packet")
    pdf.paragraph("Peer-review draft for the Lean 4 formalization of the five TIN/SNTC proof blocks.")
    pdf.paragraph(f"Date: {date.today().isoformat()}")
    pdf.paragraph("Build target: source ~/.elan/env && cd ~/Desktop/lean-proofs && lake build")
    pdf.paragraph("Environment: Lean 4.29.1 with mathlib v4.29.1")
    pdf.paragraph(f"Scope: {len(all_files)} Lean modules, {line_count} source lines, {decl_count} top-level declarations, {theorem_count} theorem or lemma declarations.")
    pdf.rule()
    pdf.h1("Review Purpose")
    pdf.paragraph(
        "This packet is intended for a collaborator who needs to review the mathematical boundary of the formalization, "
        "not just see that the project compiles. Each problem section records the proof surface, the source modules, "
        "the main formal statements, and review notes. The appendix contains the complete Lean source for C1-C5."
    )
    pdf.h1("Problem Map")
    for code, title, files, _, _ in PROBLEMS:
        pdf.bullet(f"{code}: {title}; files: {', '.join(files)}")

    pdf.h1("Current Verification Status")
    pdf.bullet("The root import file TINProofs.lean imports C1 through C5.")
    pdf.bullet("The full Lake build completed successfully after adding C1.")
    pdf.bullet("The C1 source scan has no sorry, admit, or axiom declarations.")
    pdf.bullet("C2-C5 retain their existing formal boundaries, including explicit hypotheses where the paper depends on external analytic or probabilistic facts.")

    for code, title, files, summary, notes in PROBLEMS:
        section = f"{code} {title}"
        pdf.new_page(section)
        pdf.title(f"{code}. {title}")
        pdf.h1("Mathematical Surface")
        for item in summary:
            pdf.bullet(item)
        pdf.h1("Source Modules")
        for rel in files:
            pdf.bullet(f"{rel}: {source_header(rel)}")
        pdf.h1("Declarations for Review")
        for rel in files:
            pdf.h2(rel)
            for d in declarations[rel]:
                pdf.paragraph(f"{d.kind} {d.name} ({d.file}:{d.line})", font=BODY_BOLD, size=8.8, leading=11.2,
                              color=colors.HexColor("#26313C"))
                pdf.code(d.statement, size=7.0, leading=8.4)
                pdf.y -= 2
        pdf.h1("Review Notes")
        for note in notes:
            pdf.bullet(note)

    pdf.new_page("Source Appendix")
    pdf.title("Appendix: Complete Lean Source")
    pdf.paragraph(
        "The listings below are the full C1-C5 Lean modules included in the root TINProofs import surface. "
        "Line numbers are local to each file."
    )
    for code, title, files, _, _ in PROBLEMS:
        pdf.new_page(f"Appendix {code}")
        pdf.title(f"Appendix {code}: {title}")
        for rel in files:
            pdf.h1(rel)
            pdf.code(read_file(rel), size=6.5, leading=7.8, line_numbers=True)
            pdf.y -= 8

    pdf.save()
    return OUT


if __name__ == "__main__":
    path = build_pdf()
    print(path)
