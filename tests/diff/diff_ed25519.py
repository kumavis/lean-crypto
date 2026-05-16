#!/usr/bin/env python3
"""Differential Ed25519 fuzzer.

Cross-checks our Lean implementation against Node 22's built-in
`crypto.sign` / `crypto.verify` (RFC 8032 strict). The two
implementations are independent code paths from the same spec;
byte-equality on every case is the goal.

Run:
  python3 tests/diff/diff_ed25519.py [N] [SEED]
    N    – number of (sk, msg) pairs (default 30)
    SEED – PRNG seed (default 0)

We exercise five properties per (sk, msg) pair:
  1. Lean.derivePublicKey(sk) == Node.derivePubkey(sk)
  2. Lean.sign(sk, msg)        == Node.sign(sk, msg)   (Ed25519 is deterministic)
  3. Lean.verify(Lean.pk, Lean.sig, msg)               == true
  4. Node.verify(Lean.pk, Lean.sig, msg)               == true     (cross-verify)
  5. Lean.verify(Node.pk, Node.sig, msg)               == true     (cross-verify)
  6. Tamper one bit of sig → both Lean.verify and Node.verify reject
"""

from __future__ import annotations

import random
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
LEAN_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "Tests-DiffCli"
NODE_SCRIPT = REPO_ROOT / "tests" / "diff" / "ref_ed25519.js"

# Message lengths chosen to hit interesting block boundaries of SHA-512
# (Ed25519's internal hash uses 128-byte SHA-512 blocks).
LENGTHS = [0, 1, 7, 31, 32, 63, 64, 111, 112, 128, 129, 256, 1023]


def run_cli(cmd: list[str], stdin_text: str) -> list[str]:
    proc = subprocess.run(cmd, input=stdin_text, capture_output=True,
                          text=True, timeout=300)
    if proc.returncode != 0:
        raise RuntimeError(
            f"{cmd[0]} exited {proc.returncode}: {proc.stderr}"
        )
    return proc.stdout.splitlines()


def flip_bit0(hex_sig: str) -> str:
    sig = bytearray.fromhex(hex_sig)
    sig[0] ^= 0x01
    return sig.hex()


def main() -> int:
    if not LEAN_BIN.exists():
        raise SystemExit(f"missing {LEAN_BIN}; run `lake build Tests.DiffCli`")
    if not NODE_SCRIPT.exists():
        raise SystemExit(f"missing {NODE_SCRIPT}")

    n = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    rng = random.Random(seed)

    # Generate (sk, msg) pairs.
    pairs: list[tuple[bytes, bytes]] = []
    for _ in range(n):
        sk = rng.randbytes(32)
        msg = rng.randbytes(rng.choice(LENGTHS))
        pairs.append((sk, msg))

    # Phase 1: derive + sign on both sides.
    lean_cmds, node_cmds = [], []
    for sk, msg in pairs:
        lean_cmds.append(f"ed25519-pubkey {sk.hex()}")
        lean_cmds.append(f"ed25519-sign {sk.hex()} {msg.hex()}")
        node_cmds.append(f"ed25519-pubkey {sk.hex()}")
        node_cmds.append(f"ed25519-sign {sk.hex()} {msg.hex()}")

    lean1 = run_cli([str(LEAN_BIN)], "\n".join(lean_cmds) + "\n")
    node1 = run_cli(["node", str(NODE_SCRIPT)], "\n".join(node_cmds) + "\n")

    fails: list[str] = []

    derived: list[tuple[str, str, str, str]] = []  # (lean_pk, lean_sig, node_pk, node_sig)
    for i, (sk, msg) in enumerate(pairs):
        lpk, lsig = lean1[2 * i], lean1[2 * i + 1]
        npk, nsig = node1[2 * i], node1[2 * i + 1]
        if lpk != npk:
            fails.append(
                f"pubkey mismatch pair#{i} sk={sk.hex()[:16]}…\n"
                f"  lean: {lpk}\n  node: {npk}"
            )
        if lsig != nsig:
            fails.append(
                f"sign mismatch pair#{i} sk={sk.hex()[:16]}… msg={len(msg)}B\n"
                f"  lean: {lsig}\n  node: {nsig}"
            )
        derived.append((lpk, lsig, npk, nsig))

    # Phase 2: cross-verify under both verifiers.
    lean_verify_cmds, node_verify_cmds = [], []
    for (sk, msg), (lpk, lsig, npk, nsig) in zip(pairs, derived):
        # 3. Lean verifies its own
        lean_verify_cmds.append(f"ed25519-verify {lpk} {lsig} {msg.hex()}")
        # 4. Node verifies Lean's sig
        node_verify_cmds.append(f"ed25519-verify {lpk} {lsig} {msg.hex()}")
        # 5. Lean verifies Node's sig
        lean_verify_cmds.append(f"ed25519-verify {npk} {nsig} {msg.hex()}")
        # Tamper sig bit 0 — both verifiers should reject.
        tampered = flip_bit0(lsig)
        lean_verify_cmds.append(f"ed25519-verify {lpk} {tampered} {msg.hex()}")
        node_verify_cmds.append(f"ed25519-verify {lpk} {tampered} {msg.hex()}")

    lean2 = run_cli([str(LEAN_BIN)], "\n".join(lean_verify_cmds) + "\n")
    node2 = run_cli(["node", str(NODE_SCRIPT)], "\n".join(node_verify_cmds) + "\n")

    # Lean emits 3 verifies per pair; Node emits 2 verifies per pair.
    for i, ((sk, msg), _d) in enumerate(zip(pairs, derived)):
        lean_self_ok = lean2[3 * i]      # 3
        lean_cross_ok = lean2[3 * i + 1] # 5
        lean_tamper_ko = lean2[3 * i + 2] # tamper, expect "false"
        node_cross_ok = node2[2 * i]     # 4
        node_tamper_ko = node2[2 * i + 1] # tamper, expect "false"

        if lean_self_ok != "true":
            fails.append(f"pair#{i}: Lean rejected its own sig ({lean_self_ok})")
        if lean_cross_ok != "true":
            fails.append(f"pair#{i}: Lean rejected Node's sig ({lean_cross_ok})")
        if node_cross_ok != "true":
            fails.append(f"pair#{i}: Node rejected Lean's sig ({node_cross_ok})")
        if lean_tamper_ko != "false":
            fails.append(f"pair#{i}: Lean accepted tampered sig ({lean_tamper_ko})")
        if node_tamper_ko != "false":
            fails.append(f"pair#{i}: Node accepted tampered sig ({node_tamper_ko})")

    total = n * 7  # 2 sign+derive checks + 5 verify checks per pair
    if fails:
        print(f"FAIL {len(fails)} / {total} checks", file=sys.stderr)
        for line in fails[:10]:
            print(line, file=sys.stderr)
        if len(fails) > 10:
            print(f"… and {len(fails) - 10} more", file=sys.stderr)
        return 1

    print(f"OK {total} checks across {n} (sk, msg) pairs "
          "(Lean ↔ Node ed25519, derive + sign + cross-verify + tamper)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
