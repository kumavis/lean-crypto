#!/usr/bin/env bash
# Differential fuzz orchestrator.  Run from the repo root.
#
#   tests/diff/run.sh             # default counts
#   tests/diff/run.sh 16 50       # 16 SHA samples per length, 50 Ed25519 pairs
#
# Exit 0 only if every cross-check passes.  Requires python3 + node on PATH.

set -euo pipefail

cd "$(dirname "$0")/../.."

SHA_N="${1:-8}"
ED_N="${2:-30}"
SEED="${3:-0}"

echo ":: building DiffCli"
lake build Tests.DiffCli >/dev/null

echo ":: sha256/sha512 vs Python hashlib (n_per_length=$SHA_N, seed=$SEED)"
python3 tests/diff/diff_sha.py "$SHA_N" "$SEED"

echo ":: ed25519 vs Node crypto (pairs=$ED_N, seed=$SEED)"
python3 tests/diff/diff_ed25519.py "$ED_N" "$SEED"
