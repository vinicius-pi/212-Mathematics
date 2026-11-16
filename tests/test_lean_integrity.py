#!/usr/bin/env python3
"""Static and structural integrity checks against Lean/Rocq shortcuts and doc drift."""
from __future__ import annotations

import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"
SRC_DIR = LEAN_DIR / "RhAstraSynthesis"
ROOT_LEAN = LEAN_DIR / "RhAstraSynthesis.lean"
BLUEPRINT_TEX = ROOT / "blueprint" / "src" / "content.tex"
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

UNSLOP_BANNED_PHRASES = [
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


class LeanIntegrityTests(unittest.TestCase):
    def test_all_submodules_imported_in_root(self):
        root_imports = set(
            re.findall(r"(?m)^import\s+RhAstraSynthesis\.([A-Za-z0-9_]+)\s*$", ROOT_LEAN.read_text(encoding="utf-8"))
        )
        disk_modules = {p.stem for p in SRC_DIR.glob("*.lean")}
        self.assertEqual(
            disk_modules - root_imports,
            set(),
            f"Orphan Lean modules not imported by RhAstraSynthesis.lean: {sorted(disk_modules - root_imports)}",
        )
        self.assertEqual(
            root_imports - disk_modules,
            set(),
            f"Missing Lean module files referenced by RhAstraSynthesis.lean: {sorted(root_imports - disk_modules)}",
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

        lean_corpus = "\n".join(
            strip_lean_comments(p.read_text(encoding="utf-8"))
            for p in [ROOT_LEAN, *SRC_DIR.glob("*.lean")]
        )
        missing = []
        for tag in tags:
            leaf = tag.split(".")[-1]
            if not re.search(rf"\b(?:theorem|lemma|def|abbrev)\s+{re.escape(leaf)}\b", lean_corpus):
                missing.append(tag)
        self.assertEqual(missing, [], f"Blueprint \\lean tags missing from Lean sources: {missing}")

    def test_public_docs_pass_unslop_checks(self):
        for doc in (README_MD, ARCH_MD):
            content = doc.read_text(encoding="utf-8")
            for pattern in UNSLOP_BANNED_PHRASES:
                self.assertIsNone(
                    re.search(pattern, content, flags=re.IGNORECASE),
                    f"Unslop filler phrase matched {pattern!r} in {doc.relative_to(ROOT)}",
                )


if __name__ == "__main__":
    unittest.main()
