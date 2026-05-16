#!/usr/bin/env python3
"""Differential SHA-256 / SHA-512 fuzzer.

Drives `Tests.DiffCli` against Python's stdlib `hashlib`. Both
implementations are bit-for-bit specified, so any divergence is a real
bug in our Lean side.

Usage:
  python3 tests/diff/diff_sha.py [N] [SEED]

  N    – number of random messages per length class (default 8)
  SEED – PRNG seed for reproducibility (default 0)

The Lean binary is invoked once and fed all commands on stdin; responses
come back on stdout in matching order.
"""

from __future__ import annotations

import hashlib
import os
import random
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

# Lengths spanning every block boundary that matters for both SHA-256
# (64-byte block, 8-byte length field, so padding inflection at 55/56)
# and SHA-512 (128-byte block, 16-byte length field, inflection at 111/112).
LENGTHS = [
    0, 1, 7, 8, 16, 31, 32, 33,
    54, 55, 56, 57, 63, 64, 65,
    110, 111, 112, 113, 127, 128, 129,
    200, 500, 1023, 1024, 1025,
    4096, 16384,
]


def lean_cli_path() -> Path:
    p = REPO_ROOT / ".lake" / "build" / "bin" / "Tests-DiffCli"
    if not p.exists():
        raise SystemExit(
            f"Tests.DiffCli not built. Run `lake build Tests.DiffCli` first. "
            f"(expected {p})"
        )
    return p


def main() -> int:
    n_per_length = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    rng = random.Random(seed)

    # Build the command/expected list.
    cases: list[tuple[str, bytes, str]] = []  # (algo, msg, expected_hex)
    # Fixed special cases first.
    for algo, fn in [("sha256", hashlib.sha256), ("sha512", hashlib.sha512)]:
        for length in LENGTHS:
            for _ in range(n_per_length):
                msg = rng.randbytes(length)
                cases.append((algo, msg, fn(msg).hexdigest()))
        # Edge patterns.
        for msg in [b"", b"\x00", b"\x00" * 64, b"\xff" * 64, b"a", b"abc",
                    b"a" * 1000000]:
            cases.append((algo, msg, fn(msg).hexdigest()))

    # Build the stdin script.
    cmds = "\n".join(f"{algo} {msg.hex()}" for algo, msg, _ in cases) + "\n"

    # Run Lean binary once, feed all commands.
    proc = subprocess.run(
        [str(lean_cli_path())],
        input=cmds,
        capture_output=True,
        text=True,
        timeout=300,
    )
    if proc.returncode != 0:
        print(f"Lean CLI exited {proc.returncode}: {proc.stderr}", file=sys.stderr)
        return 1

    responses = proc.stdout.splitlines()
    if len(responses) != len(cases):
        print(
            f"Response count mismatch: sent {len(cases)} cmds, got "
            f"{len(responses)} responses",
            file=sys.stderr,
        )
        return 1

    fails: list[str] = []
    for (algo, msg, expected), got in zip(cases, responses):
        if got != expected:
            # Truncate at 64 bytes (128 hex chars) for readability — the
            # previous form sliced msg.hex()[:64] which is only 32 bytes
            # and made the two branches identical at boundary lengths.
            mh = (
                msg.hex()
                if len(msg) <= 64
                else msg.hex()[:128] + f"… ({len(msg)}B)"
            )
            fails.append(
                f"  {algo} msg=({mh})\n    want {expected}\n    got  {got}"
            )

    if fails:
        print(f"FAIL {len(fails)} / {len(cases)} cases:", file=sys.stderr)
        for line in fails[:10]:
            print(line, file=sys.stderr)
        if len(fails) > 10:
            print(f"  … and {len(fails) - 10} more", file=sys.stderr)
        return 1

    print(f"OK {len(cases)} cases (sha256/sha512 vs Python hashlib)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
