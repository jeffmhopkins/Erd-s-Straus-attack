#!/usr/bin/env python3
"""Verify the explicit solution certificates stored in ``data/``.

Each JSON file maps a prime ``n`` to a record ``{R, a, b, c}``. A record is a
valid certificate when

    4/n = 1/a + 1/b + 1/c    with a, b, c positive integers,

and, when ``R`` is present, when it is consistent with ``R = 4a - n``.

Verification uses exact integer arithmetic (no floating point):

    4 * a * b * c == n * (b*c + a*c + a*b).

Run as a script to check every bundled data file::

    python -m erdos_straus.verify
    python -m erdos_straus.verify data/hard_primes_1e6_solutions.json
"""

from __future__ import annotations

import gzip
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

from erdos_straus.solver import is_solution, hard_residue


# Repo-root/data, resolved relative to this file so it works from any CWD.
DATA_DIR = Path(__file__).resolve().parents[2] / "data"

DEFAULT_FILES = [
    "hard_primes_2e5_solutions.json",
    "hard_primes_1e6_solutions.json",
    "high_R_primes_5e6.json",
    "hard_primes_1.2e8_solutions.json.gz",
    # Minimal-R map: verification reconstructs each triple from (n, R) and
    # checks it exactly (slow but exhaustive: ~15 min single-threaded).
    "hard_primes_1e9_minimalR.json.gz",
]


def load_solutions(path: Path) -> Dict:
    """Load a solution file, transparently handling gzip (.gz) compression."""
    if path.suffix == ".gz":
        with gzip.open(path, "rt") as f:
            return json.load(f)
    return json.loads(path.read_text())


@dataclass
class FileReport:
    path: Path
    total: int
    valid: int
    failures: List[str]

    @property
    def ok(self) -> bool:
        return not self.failures


def verify_record(n: int, rec) -> List[str]:
    """Return a list of human-readable problems with a single certificate.

    ``rec`` is either a full record ``{R, a, b, c}`` or, for compact R-map
    files, an integer minimal ``R``. In the R-map case the explicit triple is
    reconstructed from (n, R) with the solver and then checked exactly, so the
    map is verified as a genuine certificate — not taken on faith.
    """
    problems: List[str] = []

    # Compact R-map entry: rec is the minimal residual R.
    if isinstance(rec, int):
        R = rec
        if R <= 0 or (n + R) % 4 != 0:
            return [f"n={n}: invalid R={R} (need R>0, n+R divisible by 4)"]
        from erdos_straus.bulk_generate import solve_residual, _init_small_primes
        _init_small_primes()
        sol = solve_residual(n, R)
        if sol is None:
            return [f"n={n}: R={R} does not yield a solution on reconstruction"]
        a, b, c = sol
        if not is_solution(n, a, b, c):
            problems.append(f"n={n}: reconstructed triple invalid")
        return problems

    try:
        a, b, c = int(rec["a"]), int(rec["b"]), int(rec["c"])
    except (KeyError, TypeError, ValueError) as exc:
        return [f"n={n}: malformed record ({exc})"]

    if not is_solution(n, a, b, c):
        problems.append(
            f"n={n}: 4/n != 1/a+1/b+1/c for (a,b,c)=({a},{b},{c})"
        )

    if "R" in rec and rec["R"] is not None:
        R = int(rec["R"])
        if 4 * a - n != R:
            problems.append(
                f"n={n}: stored R={R} but 4a-n={4 * a - n}"
            )
    return problems


def verify_file(path: Path, expect_hard: bool = True) -> FileReport:
    """Verify every certificate in one JSON file."""
    data = load_solutions(path)
    failures: List[str] = []
    valid = 0
    for key, rec in data.items():
        n = int(key)
        if expect_hard and not hard_residue(n):
            failures.append(f"n={n}: not in the hard residue set mod 840")
        problems = verify_record(n, rec)
        if problems:
            failures.extend(problems)
        else:
            valid += 1
    return FileReport(path=path, total=len(data), valid=valid, failures=failures)


def verify_all(files: List[Path] | None = None) -> List[FileReport]:
    if files is None:
        files = [DATA_DIR / name for name in DEFAULT_FILES]
    return [verify_file(p) for p in files]


def main(argv: List[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    paths = [Path(a) for a in argv] if argv else None
    reports = verify_all(paths)

    exit_code = 0
    for r in reports:
        status = "OK " if r.ok else "FAIL"
        print(f"[{status}] {r.path.name}: {r.valid}/{r.total} certificates valid")
        for msg in r.failures[:20]:
            print(f"    - {msg}")
        if len(r.failures) > 20:
            print(f"    ... and {len(r.failures) - 20} more")
        if not r.ok:
            exit_code = 1

    total = sum(r.total for r in reports)
    good = sum(r.valid for r in reports)
    print(f"\nTotal: {good}/{total} certificates verified across {len(reports)} file(s).")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
