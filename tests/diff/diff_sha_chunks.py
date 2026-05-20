#!/usr/bin/env python3
"""Differential SHA streaming chunk-invariant fuzzer.

For each random message, picks several random chunkings and verifies that
*all four* of the following digests agree:

  1. Lean one-shot:     sha256(msg)
  2. Lean streaming:    init.update(c1)…update(cK).finalize  with chosen partition
  3. Python one-shot:   hashlib.sha256(msg).hexdigest()
  4. Python streaming:  hashlib.sha256(); h.update(c1)…h.update(cK); h.hexdigest()

This catches three classes of bug the existing one-shot fuzzer misses:

* Lean `Sha256Ctx` buffer state machine errors that depend on chunk
  boundaries straddling block boundaries
* Lean streaming-vs-one-shot inconsistency
* (Implicit) cross-impl agreement on streaming semantics

Usage:
  python3 tests/diff/diff_sha_chunks.py [N] [SEED]
    N    – number of messages per length class (default 4)
    SEED – PRNG seed (default 0)

Each message is exercised with 4 distinct random chunkings, so the
effective check count is `(2 algos) × (N per length) × (lengths) × 4`.
"""

from __future__ import annotations

import hashlib
import random
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
LEAN_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "Tests-DiffCli"

# Lengths spanning block boundaries for both SHA-256 (64-byte) and
# SHA-512 (128-byte). Random chunkings will cross these boundaries
# in non-trivial ways.
LENGTHS = [0, 1, 32, 55, 56, 63, 64, 65, 111, 112, 127, 128, 129,
           200, 500, 1000, 2049]


def run_cli(stdin_text: str) -> list[str]:
    proc = subprocess.run(
        [str(LEAN_BIN)], input=stdin_text, capture_output=True,
        text=True, timeout=300,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"DiffCli exited {proc.returncode}: {proc.stderr}"
        )
    return proc.stdout.splitlines()


def random_partition(rng: random.Random, msg: bytes) -> list[bytes]:
    """Randomly chop `msg` into 0..len(msg) chunks (sometimes empty chunks
    in the middle to exercise zero-length-update paths)."""
    if len(msg) == 0:
        # 50/50 either one empty chunk or no chunks at all
        return [b""] if rng.random() < 0.5 else []
    # Pick the number of chunks (at least 1, at most len(msg)+2 to allow
    # one or two zero-length filler chunks scattered in).
    n_chunks = rng.randint(1, min(len(msg) + 2, 8))
    # Distribute msg bytes across chunks, allowing zero-length chunks
    cut_points = sorted(rng.choices(range(len(msg) + 1), k=n_chunks - 1))
    chunks = []
    prev = 0
    for cp in cut_points:
        chunks.append(msg[prev:cp])
        prev = cp
    chunks.append(msg[prev:])
    return chunks


def byte_by_byte(msg: bytes) -> list[bytes]:
    """Chunk msg into individual bytes — pathological worst case for the
    buffer state machine."""
    return [bytes([b]) for b in msg]


def block_straddle(msg: bytes, block_size: int) -> list[bytes]:
    """Chunk msg so every chunk straddles the next block boundary by 1 byte.
    Forces the streaming buffer to alternate between partial-block hold
    and block-emit on every update."""
    if len(msg) == 0:
        return []
    chunks = []
    pos = 0
    # First chunk: block_size - 1 bytes
    first = min(block_size - 1, len(msg))
    chunks.append(msg[:first])
    pos = first
    while pos < len(msg):
        # Each subsequent chunk: block_size bytes (straddles the next boundary)
        remaining = len(msg) - pos
        take = min(block_size, remaining)
        chunks.append(msg[pos:pos + take])
        pos += take
    return chunks


def zero_padded(rng: random.Random, msg: bytes) -> list[bytes]:
    """Interleave the message bytes with explicit zero-length chunks.
    Tests that update(b"") is a no-op and doesn't corrupt buffer state."""
    if len(msg) == 0:
        return [b"", b"", b""]
    chunks = []
    pos = 0
    while pos < len(msg):
        chunks.append(b"")
        take = rng.randint(1, min(64, len(msg) - pos))
        chunks.append(msg[pos:pos + take])
        pos += take
    chunks.append(b"")
    return chunks


def python_streaming(algo: str, chunks: list[bytes]) -> str:
    h = hashlib.sha256() if algo == "sha256" else hashlib.sha512()
    for c in chunks:
        h.update(c)
    return h.hexdigest()


def python_oneshot(algo: str, msg: bytes) -> str:
    return (hashlib.sha256(msg) if algo == "sha256"
            else hashlib.sha512(msg)).hexdigest()


def main() -> int:
    if not LEAN_BIN.exists():
        raise SystemExit(f"missing {LEAN_BIN}; run `lake build Tests.DiffCli`")
    n_per_length = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    rng = random.Random(seed)

    # Build all (algo, msg, chunks) cases up front, so we can batch the
    # DiffCli commands. For each (algo, msg) we generate several chunking
    # patterns: random partitions plus three adversarial ones.
    cases: list[tuple[str, bytes, list[bytes], str]] = []
    # (algo, msg, chunks, expected_hex)
    PARTITIONS_PER_MSG = 4
    for algo in ("sha256", "sha512"):
        block_size = 64 if algo == "sha256" else 128
        for length in LENGTHS:
            for _ in range(n_per_length):
                msg = rng.randbytes(length)
                expected = python_oneshot(algo, msg)
                # 4 random partitions per msg
                strategies: list[list[bytes]] = [
                    random_partition(rng, msg) for _ in range(PARTITIONS_PER_MSG)
                ]
                # Adversarial chunkings (only for shorter messages — the
                # byte-by-byte one explodes the case count otherwise)
                if length <= 200:
                    strategies.append(byte_by_byte(msg))
                strategies.append(block_straddle(msg, block_size))
                strategies.append(zero_padded(rng, msg))
                for chunks in strategies:
                    py_streaming = python_streaming(algo, chunks)
                    if py_streaming != expected:
                        # Python streaming/one-shot disagree — should
                        # never happen, but if it does we report and
                        # bail rather than mask a Lean bug.
                        print(f"INTERNAL: Python streaming/oneshot disagree "
                              f"on {algo} len={length}", file=sys.stderr)
                        return 2
                    cases.append((algo, msg, chunks, expected))

    # Build the DiffCli command stream:
    # - For each case, emit:
    #     `<algo> <msg-hex>`           ← Lean one-shot
    #     `<algo>-chunks <c1> <c2> …`  ← Lean streaming with the chunks
    cmds_lines: list[str] = []
    for algo, msg, chunks, _ in cases:
        cmds_lines.append(f"{algo} {msg.hex()}")
        chunk_hexes = " ".join(c.hex() for c in chunks)
        # `<algo>-chunks` with zero hex args is a valid command: DiffCli's
        # `"sha256-chunks" :: hexes` pattern matches with `hexes = []`,
        # which decodes to the digest of the empty message. We emit the
        # bare form (no trailing space) so command boundaries stay clean.
        if chunks:
            cmds_lines.append(f"{algo}-chunks {chunk_hexes}")
        else:
            cmds_lines.append(f"{algo}-chunks")
    responses = run_cli("\n".join(cmds_lines) + "\n")

    expected_count = 2 * len(cases)
    if len(responses) != expected_count:
        print(f"Response count mismatch: sent {expected_count} cmds, "
              f"got {len(responses)}", file=sys.stderr)
        return 1

    fails: list[str] = []
    for i, (algo, msg, chunks, expected) in enumerate(cases):
        oneshot_got = responses[2 * i]
        streaming_got = responses[2 * i + 1]
        if oneshot_got != expected:
            fails.append(
                f"  {algo} oneshot len={len(msg)} chunks={len(chunks)}\n"
                f"    want {expected}\n    got  {oneshot_got}"
            )
        if streaming_got != expected:
            fails.append(
                f"  {algo} streaming len={len(msg)} chunks={len(chunks)} "
                f"sizes={[len(c) for c in chunks]}\n"
                f"    want {expected}\n    got  {streaming_got}"
            )

    if fails:
        print(f"FAIL {len(fails)} / {expected_count} cases:", file=sys.stderr)
        for line in fails[:10]:
            print(line, file=sys.stderr)
        if len(fails) > 10:
            print(f"  … and {len(fails) - 10} more", file=sys.stderr)
        return 1

    print(f"OK {expected_count} checks ({len(cases)} (msg, chunking) cases "
          f"× oneshot+streaming) vs Python hashlib (one-shot + streaming)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
