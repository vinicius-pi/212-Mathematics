#!/usr/bin/env python3
"""Static and structural integrity checks against Lean/Rocq shortcuts and doc drift."""
from __future__ import annotations

import pathlib
import re
import shutil
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"
SRC_DIR = LEAN_DIR / "Mathematics212"
ROOT_LEAN = LEAN_DIR / "Mathematics212.lean"
BLUEPRINT_TEX = ROOT / "blueprint" / "src" / "content.tex"
BLUEPRINT_PDF = ROOT / "blueprint" / "src" / "print.pdf"
README_MD = ROOT / "README.md"
ARCH_MD = ROOT / "docs" / "ARCHITECTURE.md"

BANNED_LEAN_PATTERNS = [
    (r"\bsorry\b", "sorry placeholder"),
    (r"\badmit\b", "admit tactic"),
    (r"\bnative_decide\b", "native_decide (trusts native compiler)"),
    (r"\bLean\.ofReduceBool\b", "Lean.ofReduceBool"),
    (r"\bLean\.trustCompiler\b", "Lean.trustCompiler"),
    (r"(?m)^\s*axiom\s+", "custom axiom declaration"),
]

STYLE_BANNED_PHRASES = [
    r"\bserves as\b",
    r"\bnot only\b.*\bbut also\b",
    r"\bit is worth noting\b",
    r"\bdelve into\b",
    r"\btapestry\b",
    r"\bholistic\b",
    r"\bseamless(?:ly)?\b",
    r"\bleverag(?:e|ing)\b",
]


def strip_lean_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def collect_qualified_lean_declarations(lean_files: list[pathlib.Path]) -> set[str]:
    decls: set[str] = set()
    decl_re = re.compile(
        r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|protected\s+|scoped\s+)*"
        r"(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_.]+)"
    )
    for path in lean_files:
        stack: list[tuple[str, list[str]]] = []
        for raw_line in strip_lean_comments(path.read_text(encoding="utf-8")).splitlines():
            s = raw_line.strip()
            m_ns = re.match(r"^namespace\s+([A-Za-z0-9_.]+)$", s)
            if m_ns:
                stack.append(("ns", m_ns.group(1).split(".")))
                continue
            m_sec = re.match(r"^section(?:\s+([A-Za-z0-9_.]+))?$", s)
            if m_sec:
                sec_name = m_sec.group(1)
                stack.append(("sec", sec_name.split(".") if sec_name else []))
                continue
            if re.match(r"^end(?:\s+([A-Za-z0-9_.]+))?$", s):
                if stack:
                    stack.pop()
                continue
            if re.match(r"^(?:@\[[^\]]*\]\s*)*private\b", s):
                continue
            m_decl = decl_re.match(s)
            if m_decl:
                ns_parts = [part for kind, parts in stack if kind == "ns" for part in parts]
                name = m_decl.group(1)
                full = ".".join([*ns_parts, name]) if ns_parts else name
                decls.add(full)
    return decls


class LeanIntegrityTests(unittest.TestCase):
    def test_all_submodules_imported_in_root(self):
        root_imports = set(
            re.findall(r"(?m)^import\s+Mathematics212\.([A-Za-z0-9_]+)\s*$", ROOT_LEAN.read_text(encoding="utf-8"))
        )
        disk_modules = {p.stem for p in SRC_DIR.glob("*.lean")}
        self.assertEqual(
            disk_modules - root_imports,
            set(),
            f"Orphan Lean modules not imported by Mathematics212.lean: {sorted(disk_modules - root_imports)}",
        )
        self.assertEqual(
            root_imports - disk_modules,
            set(),
            f"Missing Lean module files referenced by Mathematics212.lean: {sorted(root_imports - disk_modules)}",
        )

    def test_no_banned_shortcuts_or_custom_axioms(self):
        lean_files = [ROOT_LEAN, *sorted(SRC_DIR.glob("*.lean"))]
        for path in lean_files:
            code = strip_lean_comments(path.read_text(encoding="utf-8"))
            for pattern, label in BANNED_LEAN_PATTERNS:
                self.assertIsNone(
                    re.search(pattern, code),
                    f"Banned construct ({label}) found in {path.relative_to(ROOT)}",
                )

    def test_blueprint_lean_tags_resolve_to_declarations(self):
        tex = BLUEPRINT_TEX.read_text(encoding="utf-8")
        tags = []
        for match in re.finditer(r"\\lean\{([^}]+)\}", tex):
            for entry in match.group(1).split(","):
                tags.append(entry.strip())
        self.assertTrue(tags, "Expected at least one \\lean{...} tag in blueprint/src/content.tex")

        qualified_decls = collect_qualified_lean_declarations([ROOT_LEAN, *sorted(SRC_DIR.glob("*.lean"))])
        missing = [tag for tag in tags if tag not in qualified_decls]
        self.assertEqual(missing, [], f"Blueprint \\lean tags missing from qualified Lean declarations: {missing}")

    def test_blueprint_pdf_synchronized(self):
        self.assertTrue(BLUEPRINT_PDF.exists(), "Missing blueprint/src/print.pdf")
        self.assertGreater(BLUEPRINT_PDF.stat().st_size, 0, "Empty blueprint/src/print.pdf")
        pdftotext = shutil.which("pdftotext")
        assert pdftotext is not None, "pdftotext is required to verify blueprint/src/print.pdf synchronization"
        proc = subprocess.run(
            [pdftotext, "-enc", "UTF-8", str(BLUEPRINT_PDF), "-"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=True,
        )
        pdf_text = proc.stdout
        self.assertIn("212-mathematics blueprint", pdf_text.lower())
        legacy_pkg = "RhAstra" + "Synthesis"
        self.assertNotIn(legacy_pkg, pdf_text, f"Legacy identifier {legacy_pkg} found in print.pdf")
        self.assertIsNone(
            re.search(r"rh-" + r"astra", pdf_text, flags=re.IGNORECASE),
            "Legacy repo name found in print.pdf",
        )
        self.assertNotIn("??", pdf_text, "Unresolved LaTeX reference or citation ('??') found in print.pdf")
        for author in ("Báez-Duarte", "Markov", "Titchmarsh", "van der Corput"):
            self.assertIn(author, pdf_text, f"Bibliography author {author!r} missing from print.pdf")

        norm_pdf = re.sub(r"\s+", "", pdf_text)
        tex = BLUEPRINT_TEX.read_text(encoding="utf-8")
        tags = [entry.strip() for m in re.finditer(r"\\lean\{([^}]+)\}", tex) for entry in m.group(1).split(",")]
        missing_in_pdf = [tag for tag in tags if tag not in norm_pdf]
        self.assertEqual(missing_in_pdf, [], f"Blueprint \\lean tags out of sync with print.pdf: {missing_in_pdf}")

    def test_public_docs_style(self):
        for doc in (README_MD, ARCH_MD):
            content = doc.read_text(encoding="utf-8")
            for pattern in STYLE_BANNED_PHRASES:
                self.assertIsNone(
                    re.search(pattern, content, flags=re.IGNORECASE),
                    f"Disallowed filler phrase matched {pattern!r} in {doc.relative_to(ROOT)}",
                )

    def test_no_legacy_naming_or_operatorname_in_docs(self):
        text_files = [
            ROOT_LEAN,
            *sorted(SRC_DIR.glob("*.lean")),
            LEAN_DIR / "lakefile.toml",
            LEAN_DIR / "lake-manifest.json",
            ROOT / ".github" / "workflows" / "verify.yml",
            BLUEPRINT_TEX,
            ROOT / "blueprint" / "src" / "print.tex",
            ROOT / "blueprint" / "src" / "web.tex",
            README_MD,
            ARCH_MD,
            ROOT / "docs" / "RECIPROCAL_GEVREY_PROOF.md",
            *sorted((ROOT / "tests").glob("test_*.py")),
        ]
        legacy_pkg = "RhAstra" + "Synthesis"
        legacy_repo_re = re.compile(r"rh-" + r"astra", flags=re.IGNORECASE)
        for path in text_files:
            content = path.read_text(encoding="utf-8")
            self.assertNotIn(
                legacy_pkg,
                content,
                f"Legacy identifier {legacy_pkg} found in {path.relative_to(ROOT)}",
            )
            self.assertIsNone(
                legacy_repo_re.search(content),
                f"Legacy repo name found in {path.relative_to(ROOT)}",
            )
        for md in (README_MD, ARCH_MD, ROOT / "docs" / "RECIPROCAL_GEVREY_PROOF.md"):
            self.assertNotIn(
                "\\operatorname",
                md.read_text(encoding="utf-8"),
                f"Unsupported GitHub MathJax macro \\operatorname found in {md.relative_to(ROOT)}",
            )

    def test_markdown_relative_links_resolve(self):
        for md in (README_MD, ARCH_MD, ROOT / "docs" / "RECIPROCAL_GEVREY_PROOF.md"):
            content = md.read_text(encoding="utf-8")
            for target in re.findall(r"\[[^\]]+\]\(([^)\s]+)\)", content):
                if target.startswith(("http://", "https://", "#")):
                    continue
                rel = target.split("#", 1)[0]
                resolved = (md.parent / rel).resolve()
                self.assertTrue(
                    resolved.exists(),
                    f"Broken relative link {target!r} in {md.relative_to(ROOT)}",
                )

    def test_pinned_toolchain_and_manifest(self):
        import json

        toolchain = (LEAN_DIR / "lean-toolchain").read_text(encoding="utf-8").strip()
        self.assertEqual(toolchain, "leanprover/lean4:v4.34.0")
        manifest = json.loads((LEAN_DIR / "lake-manifest.json").read_text(encoding="utf-8"))
        self.assertEqual(manifest.get("name"), "Mathematics212")
        mathlib = [p for p in manifest.get("packages", []) if p.get("name") == "mathlib"]
        self.assertEqual(len(mathlib), 1)
        self.assertEqual(mathlib[0].get("rev"), "5ed2965256430c3649e86755f9576b54eca72435")

    def test_readme_declarations_exist_in_main_theorems(self):
        main_src = strip_lean_comments((SRC_DIR / "MainTheorems.lean").read_text(encoding="utf-8"))
        readme = README_MD.read_text(encoding="utf-8")
        for line in readme.splitlines():
            if not line.startswith("|") or "MainTheorems" in line or ":---" in line:
                continue
            cells = [c.strip() for c in line.split("|")]
            if len(cells) >= 3:
                for decl in re.findall(r"`([A-Za-z0-9_]+)`", cells[2]):
                    self.assertIsNotNone(
                        re.search(rf"\b(?:abbrev|theorem|lemma|def)\s+{re.escape(decl)}\b", main_src),
                        f"README declaration `{decl}` missing from MainTheorems.lean",
                    )


if __name__ == "__main__":
    unittest.main()
