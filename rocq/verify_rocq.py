#!/usr/bin/env python3
"""Compile and kernel-check `rocq/*.v` using pinned `rocq/rocq-prover:9.0`."""
from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

IMAGE = "rocq/rocq-prover@sha256:3ed9c46fa02e9fd7748a959abebb11b36f8818d10738dcc93edc67354c313ce2"


def main() -> int:
    if not shutil.which("docker"):
        print("docker binary not found", file=sys.stderr)
        return 1
    rocq_dir = Path(__file__).resolve().parent
    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{rocq_dir}:/src:ro",
        IMAGE,
        "sh",
        "-lc",
        (
            "mkdir -p /tmp/rocq && cp /src/*.v /tmp/rocq/ && cd /tmp/rocq && "
            "rocq compile RationalEnvelope.v && rocq compile RationalContract.v && "
            "/home/rocq/.opam/4.14.2+flambda/bin/rocqchk RationalEnvelope RationalContract"
        ),
    ]
    proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
    print(proc.stdout)
    if proc.returncode != 0:
        return proc.returncode
    if re.search(r"(?mi)^\s*Axioms?\s*:", proc.stdout):
        print("Unexpected Rocq axiom dependency detected.", file=sys.stderr)
        return 1
    if proc.stdout.count("Closed under the global context") != 4:
        print("Missing expected 'Closed under the global context' confirmations.", file=sys.stderr)
        return 1
    if "Modules were successfully checked" not in proc.stdout:
        print("Missing 'Modules were successfully checked' rocqchk confirmation.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
