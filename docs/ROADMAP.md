# `lean-crypto` — Roadmap

> **All v1 milestones (M1–M11) shipped.** Follow-on work lives in
> `docs/VCV_IO_ROADMAP.md` (M12–M18, VCV-io wrapper) and
> `docs/PROOFS_ROADMAP.md` (M19–M24, algebraic foundations).

Sequenced milestones from empty repo to SHA-256 + Ed25519 passing every
in-scope vector. Each milestone produces a runnable artifact with passing
tests before the next starts. Each milestone is a single PR.

Effort estimates are wall-clock for a focused agent session — small (< 1 day),
medium (1–2 days), large (2–4 days). They're rough guides for sequencing,
not commitments.

---

## M1 · Project skeleton — small

**Goal.** `lake build` succeeds on an empty library + one trivial test exe.
CI green.

**Deliverables.**
- `lean-toolchain` pinned to `leanprover/lean4:v4.27.0`.
- `lakefile.lean` declaring `lean_lib LeanCrypto` (release, `-O3`) and
  `lean_exe tests/HelloTest` printing `OK 0 vectors`.
- `LeanCrypto.lean` (root) and stub `LeanCrypto/Bytes.lean`.
- `.gitignore` (`.lake/`, `build/`, `*.olean`).
- `.github/workflows/ci.yml`: install elan, `lake build`, run every
  `tests/*.lean` exe, fail on any non-zero exit.
- `README.md` stub: one paragraph status, link to PLAN/ROADMAP.

**Acceptance.**
- `lake build` exits 0 on a clean checkout.
- `lake exe tests/HelloTest` prints `OK 0 vectors`.
- GitHub Actions run is green.

---

## M2 · `LeanCrypto.Bytes` — small

**Goal.** Big-endian and little-endian load/store for `UInt32` / `UInt64` /
256-bit values, plus hex parsing. Every later module uses these helpers; no
open-coded byte shuffling anywhere else.

**Deliverables.**
- `LeanCrypto/Bytes.lean`:
  - `loadU32BE`, `loadU64BE`, `loadU256LE`
  - `storeU32BE` (append), `storeU64BE` (append),
    `storeU256LE` (always 32 bytes)
  - `bytesToHex`, `hexToBytes` (mirrors noble's `utils.ts`)
- `LeanCrypto/Data/HexString.lean` (lifted in shape from gdncc/Cryptography).
- `tests/BytesTest.lean`:
  - `loadU32BE [0x12, 0x34, 0x56, 0x78] 0 = 0x12345678` and three more
    fixed cases.
  - Round-trip: `loadU32BE (storeU32BE x) = x` for a handful of `x`.
  - Same for `UInt64`.
  - `hexToBytes (bytesToHex b) = b` for several inputs including empty.

**Acceptance.**
- `lake exe tests/BytesTest` prints `OK <N> vectors`.
- CI green.

---

## M3 · SHA-256 one-shot — medium

**Goal.** `sha256 : ByteArray → ByteArray` passes every NIST CAVP
short-message vector.

**Deliverables.**
- `LeanCrypto/Hash/SHA256.lean`:
  - IV, K, Ch, Maj, Σ0, Σ1, σ0, σ1 (all `private`).
  - `rotr32` (`@[inline]`).
  - `compress : Sha256State → ByteArray → Nat → Sha256State` processing
    one 64-byte block from offset.
  - `padMessage : ByteArray → ByteArray` — full MD padding for one-shot.
  - `sha256 : ByteArray → ByteArray`.
- `LeanCrypto/Data/CAVS.lean` (parser; pattern from gdncc/Cryptography).
- `tests/vectors/sha256/SHA256ShortMsg.rsp` (committed).
- `tests/Sha256Test.lean`: reads `.rsp`, runs every record, exits 1 on first
  mismatch.

**Acceptance.**
- Empty-string vector: `sha256 ByteArray.empty` is
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (the
  vector with `Len = 0`).
- All NIST `SHA256ShortMsg.rsp` records pass.

**Concurrent check.** `rotr32` unit test from M2's pattern (`rotr32 0x12345678 8
= 0x78123456`) lives in `tests/Sha256Test.lean` and runs first — if SHA-256
breaks, we want to know which primitive is wrong.

---

## M4 · SHA-256 streaming — small

**Goal.** `Sha256Ctx.init`/`update`/`finalize` matches one-shot byte-for-byte;
passes NIST long-message and Monte Carlo vectors.

**Deliverables.**
- `Sha256Ctx` structure (state + buffer + bufLen + totalLen).
- `Sha256Ctx.init` / `update` / `finalize`.
- Refactor `sha256` one-shot to wrap streaming (one `update`, one `finalize`).
- `tests/vectors/sha256/SHA256LongMsg.rsp`,
  `tests/vectors/sha256/SHA256Monte.rsp` (committed).
- `tests/Sha256Test.lean` extended:
  - Long-message vectors run via streaming `update` chunked at 1 byte, 7
    bytes, 63 bytes, 64 bytes, 65 bytes, and 1024 bytes (differential
    test: chunk size must not affect output).
  - Monte Carlo vectors run end-to-end.

**Acceptance.**
- All NIST long and Monte Carlo vectors pass.
- Each long vector passes at every chunk granularity.

---

## M5 · SHA-512 — small

**Goal.** Same shape as SHA-256, native `UInt64`. Required by Ed25519.

**Deliverables.**
- `LeanCrypto/Hash/SHA512.lean`: structurally a copy of SHA-256 with
  - words → `UInt64`, block 128 bytes, 80 rounds.
  - SHA-512 IV and K constants.
  - SHA-512 Σ/σ rotation amounts (per PLAN §7.2).
  - 128-bit length field at end of final block (high 64 bits = 0).
- `tests/vectors/sha512/` (short, long, Monte vectors).
- `tests/Sha512Test.lean`.

**Acceptance.**
- All NIST SHA-512 short / long / Monte Carlo vectors pass.
- Same chunk-granularity differential test as SHA-256.

---

## M6 · `LeanCrypto.Field.Fp25519` — medium

**Goal.** Field arithmetic mod `p = 2²⁵⁵ − 19`. Correct, total, slow.

**Deliverables.**
- `LeanCrypto/Field/Fp25519.lean`:
  - `p`, `add`, `sub`, `mul`, `neg`, `square`, `pow`.
  - `inv` via Fermat (`pow a (p-2)`).
  - `sqrt` via the p ≡ 5 (mod 8) formula.
  - `sqrtM1` constant.
- `tests/Fp25519Test.lean`:
  - Unit tests against hand-computed values for `add`, `mul`, `inv`.
  - Round-trip: `mul a (inv a) = 1` for 10 random-looking nonzero `a`.
  - `sqrt`: `square (sqrt x).get! = x` for quadratic residues; `sqrt`
    returns `none` for non-residues (use Jacobi-symbol-style sampling, or
    hand-pick).
  - `pow a (p-1) = 1` for nonzero `a` (Fermat sanity).

**Acceptance.**
- All `tests/Fp25519Test.lean` cases pass.
- Wall-clock per test < 1 s (Fermat `pow` is the slow op; should still fit).

---

## M7 · `LeanCrypto.Field.ScalarL` — small

**Goal.** Arithmetic mod `ℓ`, plus the 64-byte-to-scalar reduction Ed25519
needs.

**Deliverables.**
- `LeanCrypto/Field/ScalarL.lean`:
  - `L`, `add`, `sub`, `mul`, `reduce` (Nat → ScalarL).
  - `reduce512Bit : ByteArray → ScalarL` reading 64 little-endian bytes.
- `tests/ScalarLTest.lean`:
  - Unit cases for `add`, `mul`.
  - `reduce512Bit` against a few RFC-8032 worked examples (the hash-of-prefix
    intermediates from §7.1 vector 1 — we hand-extract them once).

**Acceptance.**
- All `tests/ScalarLTest.lean` cases pass.

---

## M8 · `LeanCrypto.Curve.Edwards25519` — medium

**Goal.** Point addition, doubling, scalar multiplication, encode/decode in
extended Edwards coordinates.

**Deliverables.**
- `LeanCrypto/Curve/Edwards25519.lean`:
  - `EdPoint` (X, Y, Z, T), `EdAffine`.
  - `B` (base point), `identity`.
  - `add` (2008-hwcd-3 unified), `double` (2008-hwcd), `neg`.
  - `mul` (left-to-right double-and-add).
  - `encode` (32 bytes), `decode` (`Option EdPoint`).
- `tests/Edwards25519Test.lean`:
  - `B + B = 2·B` via `add` vs `double`.
  - First 8 multiples of `B` against hand-computed (or noble-derived) values
    — at minimum encoded forms of `2·B`, `4·B`, `8·B`.
  - Decode-encode round-trip for `B`, `2·B`, identity.
  - `decode` of a known invalid y (e.g. `p` itself, or all-`0xff` bytes
    representing y > p) returns `none`.
  - `ℓ · B = identity` (order check, expensive but worth running).

**Acceptance.**
- All `tests/Edwards25519Test.lean` cases pass.
- `ℓ · B = identity` takes < 30 s on a developer laptop. (If slower, revisit
  `Fp25519` representation; but flag and continue, don't optimise mid-stream.)

---

## M9 · `LeanCrypto.Signature.Ed25519` — medium

**Goal.** RFC 8032 sign and verify. Pass all 4 RFC §7.1 vectors end-to-end.

**Deliverables.**
- `LeanCrypto/Signature/Ed25519.lean`:
  - `clampScalar : ByteArray → ScalarL` (clear bits 0,1,2,255; set bit 254).
  - `derivePublicKey`, `sign`.
  - Internal `verifyWith (mode : VerifyMode)` plus two public wrappers:
    `verify` (strict RFC 8032) and `verifyZip215`. See PLAN §4.7 / §10.1.
- `tests/vectors/rfc8032/ed25519_rfc8032.json` (the 4 §7.1 vectors,
  hand-extracted into a tiny JSON file).
- `tests/Ed25519Test.lean`:
  - For each §7.1 vector: `derivePublicKey sk == pk`, `sign sk msg == sig`,
    `verify pk sig msg == true`, `verifyZip215 pk sig msg == true` (canonical
    inputs pass under both modes).
  - Tamper a single byte of sig and both verify variants reject.
  - Tamper a single byte of msg and both verify variants reject.

**Acceptance.**
- All 4 RFC 8032 vectors pass (derive, sign, both verify variants).
- All tamper tests reject under both variants.

---

## M10 · Wycheproof — small to medium

**Goal.** Pass Project Wycheproof's Ed25519 suite; document every divergence.

**Deliverables.**
- `tests/vectors/wycheproof/eddsa_test.json` (vendored snapshot, hash pinned
  in `tests/vectors/wycheproof/SOURCE.md`).
- Minimal JSON parser in `tests/Ed25519Test.lean` (using `Lean.Json`).
- `tests/wycheproof_decisions.md`: per-flag list mapping Wycheproof flags to
  expected outcomes under `verify` (strict) and `verifyZip215`, with
  one-line reasoning per row.
- `tests/Ed25519Test.lean` extended to iterate every Wycheproof case through
  **both** verify variants.

**Acceptance.**
- Under `verify` (strict): every `valid` case verifies `true`, every `invalid`
  case verifies `false`, every `acceptable` case matches the strict-column
  expectation in `wycheproof_decisions.md`.
- Under `verifyZip215`: every `valid` case verifies `true`, every `invalid`
  case verifies `false`, every `acceptable` case matches the ZIP-215-column
  expectation in `wycheproof_decisions.md`.
- Test runner prints `OK <N> vectors` (where `N` is total cases × 2 modes).

---

## M11 · Polish — small

**Goal.** Library is presentable and usable.

**Deliverables.**
- Docstrings on every public function in `LeanCrypto/`.
- `README.md`:
  - One-paragraph status (✓ SHA-256, ✓ SHA-512, ✓ Ed25519 strict).
  - Usage snippet for each public API.
  - Known leaks (per PLAN §8) called out.
  - Performance note: "v1 is correctness-first; sign/verify on the order of
    seconds, not microseconds. See `docs/PLAN.md` §9 for the optimisation
    roadmap."
- Optional: differential fuzz harness (`tests/fuzz.sh`, see PLAN §6.4).
  Not gated on CI.

**Acceptance.**
- `lake build && lake test` (or the equivalent CI command) runs every
  vector suite green from a clean checkout.
- `README` examples copy-paste-work into a fresh project that depends on
  this one.

---

## Cross-cutting acceptance: at every milestone

- No `sorry`, no `partial`, no `unsafe`, no `extern`. Grep for these in CI.
- No new external dependencies beyond what's in `lakefile.lean` at M1.
  Mathlib stays out.
- Test runner exit code is the source of truth. `lake build` succeeding
  with failing tests is not a pass.
- Each PR touches at most one milestone's worth of files plus the test
  runner for that milestone. PR descriptions reference the milestone ID
  (`M3`, `M6`, …) and cite the spec section the change implements.
- If a milestone's plan needs to change mid-stream (e.g. M6 discovers
  Fermat-`pow` is too slow for `ℓ · B = identity` in M8), the relevant
  `docs/PLAN.md` section is updated **in the same PR** and the PR
  description calls out the change.
