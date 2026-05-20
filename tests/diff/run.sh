#!/usr/bin/env bash
# Differential fuzz orchestrator.  Run from the repo root.
#
# Positional args (all optional; defaults shown):
#   $1 SHA_N         (16)   sha256/sha512 one-shot samples per length class
#   $2 ED_N          (50)   random Ed25519 (sk, msg) pairs
#                            (in addition to the 12 fixed boundary cases)
#   $3 SEED          (0)    PRNG seed for reproducibility
#   $4 SHA_CHUNKS_N  (4)    sha256/sha512 streaming chunk-invariant samples
#                            per length class (4 chunkings each)
#
# Examples:
#   tests/diff/run.sh                # default counts
#   tests/diff/run.sh 16 50          # bump SHA + Ed25519 counts
#   tests/diff/run.sh 64 200 1 16    # heavier sweep with seed=1
#
# Exit 0 only if every cross-check passes.  Requires python3 + node on PATH.

set -euo pipefail

cd "$(dirname "$0")/../.."

SHA_N="${1:-16}"
ED_N="${2:-50}"
SEED="${3:-0}"

echo ":: building DiffCli"
lake build Tests.DiffCli >/dev/null

echo ":: sha256/sha512 vs Python hashlib (n_per_length=$SHA_N, seed=$SEED)"
python3 tests/diff/diff_sha.py "$SHA_N" "$SEED"

SHA_CHUNKS_N="${4:-4}"
echo ":: sha256/sha512 streaming chunk-invariant vs Python hashlib (n_per_length=$SHA_CHUNKS_N, seed=$SEED)"
python3 tests/diff/diff_sha_chunks.py "$SHA_CHUNKS_N" "$SEED"

echo ":: ed25519 vs Node crypto (pairs=$ED_N, seed=$SEED)"
python3 tests/diff/diff_ed25519.py "$ED_N" "$SEED"
