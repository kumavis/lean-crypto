# `lean-crypto` — Plan

> **Historical document.** Written before any code was; the v1 milestones
> M1–M11 followed this. The library has since been extended with a
> VCV-io wrapper (M12–M18, see `docs/VCV_IO_PLAN.md`) and an
> algebraic-foundations proof track (M19–M24, see
> `docs/PROOFS_ROADMAP.md`). Toolchain was bumped from the
> originally-planned `v4.27.0` to `v4.29.0` in M12 to match VCV-io's
> tagged release.

Pure Lean 4 implementation of SHA-256 and Ed25519, validated bit-for-bit against
[`noble-hashes`](https://github.com/paulmillr/noble-hashes) and
[`noble-ed25519`](https://github.com/paulmillr/noble-ed25519) and against
the standard test vectors from FIPS 180-4, RFC 8032, and Project Wycheproof.

Closest prior art in the Lean 4 ecosystem is
[gdncc/Cryptography](https://github.com/gdncc/Cryptography) (SHA-3, eprint
2024/1880); we adopt its idioms — fixed-size arrays as `{val : Array α // val.size = n}`
subtypes, `Fin n` for bounded indices, dependent state tags, `Id.run do`/`let mut`
loop bodies, pure-Lean with no external dependencies. This document spells out
the design choices in advance of any `.lean` code being written.

---

## 1. Scope

**In.**
- SHA-256 (FIPS 180-4 §6.2): one-shot `sha256 : ByteArray → ByteArray` and a
  streaming `Sha256Ctx` with `init` / `update` / `finalize`.
- SHA-512 (FIPS 180-4 §6.4): same shape, native `UInt64`. Required by Ed25519.
- Ed25519 (RFC 8032 §5.1, PureEdDSA over edwards25519 with SHA-512): public-key
  derivation, sign, verify. Operates over `ByteArray`.

**Out.**
- SHA-224, SHA-384, SHA-512/{224,256}, SHA-3, HMAC.
- X25519, Ed25519ph / Ed25519ctx, Ristretto255.
- Constant-time guarantees and side-channel hardening (documented but not fixed).
- Formal proofs of correctness or cryptographic security.
- Performance optimizations beyond using the right native word size.

**Out, but kept architecturally open for follow-on work.**
- Plugging into [VCV-io](https://github.com/Verified-zkEVM/VCV-io)'s `OracleComp`
  framework — VCV-io expects to wrap pure computations into its monad, so our
  ByteArray-in/ByteArray-out total functions are exactly the right shape; doing
  the wrap itself is a separate phase.
- Proofs of correctness (functions are written total, no `partial`, no `sorry`,
  no `unsafe`, with invariants stated as docstring comments rather than
  refinement types, so that proofs can be slotted in later).

---

## 2. Project layout

```
lean-crypto/
├── lean-toolchain                  # leanprover/lean4:v4.27.0 (matches gdncc/Cryptography)
├── lakefile.lean                   # release build, -O3, lean_lib + lean_exe per test runner
├── lake-manifest.json              # generated
├── README.md                       # usage and status (Phase 1 stub only)
├── docs/
│   ├── PLAN.md
│   └── ROADMAP.md
├── LeanCrypto.lean                 # root re-exports
├── LeanCrypto/
│   ├── Bytes.lean                  # ByteArray helpers, BE/LE load/store
│   ├── Hash/
│   │   ├── MerkleDamgard.lean      # padding + block-streaming scaffolding
│   │   ├── SHA256.lean             # IV, K, Ch, Maj, Σ, σ, compress, one-shot, streaming
│   │   └── SHA512.lean             # same shape, UInt64
│   ├── Field/
│   │   ├── Fp25519.lean            # arithmetic mod 2²⁵⁵−19
│   │   └── ScalarL.lean            # arithmetic mod ℓ
│   ├── Curve/
│   │   └── Edwards25519.lean       # extended-Edwards point ops, encode/decode
│   ├── Signature/
│   │   └── Ed25519.lean            # derivePublicKey, sign, verify
│   └── Data/
│       ├── HexString.lean          # hex ↔ ByteArray (test-vector helper)
│       └── CAVS.lean               # NIST .rsp parser (after gdncc/Cryptography)
└── tests/
    ├── Sha256Test.lean             # NIST CAVP runners
    ├── Sha512Test.lean
    ├── Fp25519Test.lean            # unit + round-trip tests
    ├── Edwards25519Test.lean       # RFC 8032 base-point multiples
    ├── Ed25519Test.lean            # RFC 8032 §7.1 + Wycheproof
    └── vectors/                    # committed, not fetched at build time
        ├── sha256/                 # SHA256ShortMsg.rsp, SHA256LongMsg.rsp, SHA256Monte.rsp
        ├── sha512/                 # SHA512ShortMsg.rsp, SHA512LongMsg.rsp, SHA512Monte.rsp
        ├── rfc8032/                # ed25519_rfc8032.json (hand-extracted, simple format)
        └── wycheproof/             # eddsa_test.json (vendored snapshot, pinned by hash)
```

Test runners are `lean_exe` targets that read vectors, run each case, exit nonzero
on first mismatch. CI runs each test executable.

---

## 3. Dependencies

**Lean toolchain.** Pinned to `leanprover/lean4:v4.27.0` (matches the
gdncc/Cryptography precedent; whatever ships with it gives us `ByteArray`,
`UInt32`/`UInt64` with full bit ops, `Fin n`, `Std.Internal.Parsec`, and
`omega` — all we need).

**std4 / batteries.** None. The standard library that ships with Lean 4.27.0
already provides `Std.Internal.Parsec`, `ByteArray`, `Array.modify`,
`omega`, and `decide`, which together cover every utility we need. We borrow
the `size_set` theorem snippet from batteries by inlining it (as gdncc/Cryptography does)
rather than taking on a dep.

**Mathlib.** No. Reasoning:
- Mathlib's build time is multi-minute; it dwarfs the implementation.
- `Fp25519` and `ScalarL` need only `Nat.gcd`, `Nat.modPow`, `%`, and shifts —
  all in core Lean.
- We deliberately do *not* want to depend on `ZMod p` or `EllipticCurve` for
  the implementation; those are abstractions for proofs, and proofs are a
  later phase.
- If later proof work needs Mathlib, the proof modules can take it as a
  dependency without forcing it on the implementation.

**Why this matters for the VCV-io follow-on.** VCV-io depends on Mathlib. Our
implementation does not, but our API surface is pure-functional `ByteArray → …`
so a thin wrapper module living in a future "proofs" lake target (which *would*
import Mathlib + VCV-io) can wrap our functions into `OracleComp` without
modifying anything in `LeanCrypto/`.

---

## 4. Type design

### 4.1 Bytes

`ByteArray` everywhere at the API boundary. Internally we may also use it
(Lean's `ByteArray.set` is in-place when uniquely referenced, so threaded
immutable updates compile to mutation). The other options:

- `Array UInt8`: slower for large inputs (no specialised buffer), no `set!`-equivalent
  with proof; ByteArray wins.
- `List UInt8`: bad for indexed access; only useful as a literal-list source. Rejected.

The `LeanCrypto.Bytes` module exposes:

```lean
def loadU32BE  (b : ByteArray) (off : Nat) (h : off + 4 ≤ b.size) : UInt32
def loadU64BE  (b : ByteArray) (off : Nat) (h : off + 8 ≤ b.size) : UInt64
def loadU256LE (b : ByteArray) (off : Nat) (h : off + 32 ≤ b.size) : Nat   -- for Ed25519 scalars / y-coords
def storeU32BE  : UInt32 → ByteArray → ByteArray  -- appends 4 bytes
def storeU64BE  : UInt64 → ByteArray → ByteArray  -- appends 8 bytes
def storeU256LE : Nat → ByteArray                 -- always 32 bytes, low-19 modular reduction is caller's job
```

Indexed-access variants accept either a proof or a `Fin b.size` index (depending
on what reads better; gdncc/Cryptography uses both styles). We define
`GetElem` instances for any fixed-size subtype we introduce.

**No open-coded byte shuffling outside this module.** Every load/store goes
through here; the SHA and Ed25519 modules use these helpers exclusively.

### 4.2 Hash word types

- SHA-256: `UInt32`. Lean's `UInt32` is mod 2³² natively; bit ops are constant-time
  primitives on the underlying machine word. No need for `| 0` JS coercions.
- SHA-512: `UInt64`. **Do not port** noble's `_u64.ts` high/low split — that exists
  only because JS bitops are 32-bit. SHA-512 in Lean is structurally identical
  to SHA-256 with `UInt64` substituted and the constants/rotations changed.
- Rotate-right is the one-liner gdncc/Cryptography uses:
  ```lean
  @[always_inline, inline] private def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
    (x >>> n) ||| (x <<< (32 - n))
  ```
  with a `UInt64` twin. A unit test on a known value (e.g. `rotr32 0x12345678 8 = 0x78123456`)
  pins this down before SHA is built on it.

### 4.3 Hash state

Follow the gdncc/Cryptography pattern: state is a sized subtype with a `GetElem`
instance, and a `subtypeModify` helper preserves the size invariant.

```lean
abbrev HashWords (w : Type) (n : Nat) := { val : Array w // val.size = n }
abbrev Sha256State := HashWords UInt32 8
abbrev Sha512State := HashWords UInt64 8
```

The streaming context bundles state + buffer + length counter:

```lean
structure Sha256Ctx where
  state    : Sha256State
  buffer   : ByteArray         -- ≤ 64 bytes, partial block
  bufLen   : Nat               -- < 64
  totalLen : Nat               -- total bytes consumed (length-in-bits = 8*totalLen)
```

We do *not* split absorbing vs squeezing into separate types as the SHA-3
implementation does — SHA-2 has no "squeeze" phase; `finalize` is a single
terminal call that returns a digest and consumes the context. A `Sha256Ctx`
value is single-use by convention; reusing one after `finalize` is a programmer
error but not a type error (we don't fence it with dependent types because the
ergonomic cost outweighs the protection for a non-XOF hash).

### 4.4 Field elements `Fp25519`

```lean
abbrev Fp25519 := Nat
```
with the invariant — documented at every public function — that values are
in `[0, p)`. Justification:
- `Nat`-backed is simplest and total; addition/multiplication/reduction are all in core.
- We don't write field-arithmetic proofs in this phase, so a structure wrapper
  buys us nothing yet.
- Future optimisation (limb representation) can replace the abbrev without
  changing any call-site if we expose all operations through a module-level API.

Operations:

```lean
namespace Fp25519
def p : Nat := 2^255 - 19
def add   : Fp25519 → Fp25519 → Fp25519     -- (a + b) % p
def sub   : Fp25519 → Fp25519 → Fp25519     -- (a + p - b) % p
def mul   : Fp25519 → Fp25519 → Fp25519     -- (a * b) % p
def neg   : Fp25519 → Fp25519               -- (p - a) % p
def square (a : Fp25519) : Fp25519 := mul a a
def pow   : Fp25519 → Nat → Fp25519         -- Nat.modPow-style; or hand-rolled
def inv   : Fp25519 → Fp25519               -- Fermat: pow a (p-2); see §7
def sqrt  : Fp25519 → Option Fp25519        -- p ≡ 5 mod 8 case
end Fp25519
```

`inv` chooses **Fermat (a^(p-2) mod p)** over extended-Euclidean for v1.
Tradeoff: Fermat is one-liner total and trivially correct; extended-Euclidean
is faster but requires a termination proof and more code. v1 priorities are
correctness and simplicity. Noted as a future optimisation target.

`sqrt` uses the p ≡ 5 (mod 8) formula: candidate `r = a^((p+3)/8) mod p`,
return `r` if `r² ≡ a`, else `r * 2^((p-1)/4) mod p` if that squares to `a`,
else `none`. The constant `2^((p-1)/4) mod p` is precomputed at the top of the
module.

### 4.5 Scalars mod ℓ

```lean
abbrev ScalarL := Nat
```
separate alias from `Fp25519` because they live in different rings; mixing them
would be a category error. Invariant: values in `[0, L)` where
`L = 2^252 + 27742317777372353535851937790883648493`.

```lean
namespace ScalarL
def L : Nat := 2^252 + 27742317777372353535851937790883648493
def reduce : Nat → ScalarL    -- general n mod L; used to reduce SHA-512 outputs
def reduce512Bit : ByteArray → ScalarL   -- 64-byte little-endian → mod L
def add : ScalarL → ScalarL → ScalarL
def mul : ScalarL → ScalarL → ScalarL
end ScalarL
```

We do **not** implement Barrett reduction or Montgomery multiplication for v1;
`Nat.mod` is the v1 path. Noted for follow-on.

### 4.6 Curve points

Extended Edwards (X, Y, Z, T) with the invariant `T·Z = X·Y` (equivalently
`T = X·Y / Z` in the affine projection).

```lean
structure EdPoint where
  X : Fp25519
  Y : Fp25519
  Z : Fp25519
  T : Fp25519
-- invariant: T * Z = X * Y (mod p)
```

Affine I/O lives in a separate type that's never used in the hot path:

```lean
structure EdAffine where x : Fp25519; y : Fp25519
def EdPoint.toAffine : EdPoint → EdAffine               -- requires Z ≠ 0; total via inv
def EdAffine.toExt   : EdAffine → EdPoint
def EdPoint.encode   : EdPoint → ByteArray              -- 32 bytes, LE y + x-sign bit
def EdPoint.decode   : ByteArray → Option EdPoint       -- rejects bad y, returns none for non-square x²
```

Group operations:

```lean
def EdPoint.identity   : EdPoint                   -- (0, 1, 1, 0)
def EdPoint.add        : EdPoint → EdPoint → EdPoint   -- unified add (2008-hwcd-3)
def EdPoint.double     : EdPoint → EdPoint         -- doubling (2008-hwcd)
def EdPoint.neg        : EdPoint → EdPoint
def EdPoint.mul        : Nat → EdPoint → EdPoint   -- scalar mult, left-to-right double-and-add
```

For v1 we use plain **left-to-right double-and-add** for `EdPoint.mul`. This is
the simplest correct implementation. It leaks timing via key-dependent
branches; this is documented at the top of the module as a known v1 leak.
Noble's wNAF + precomputed-base-point table is a follow-on optimisation
(see §8).

The 2008-hwcd-3 unified add formula (8M + 1k + 1A with `k = 2d`) and the
2008-hwcd doubling formula (4M + 4S + 1k) are reproduced inline from the
[Explicit-Formulas Database](https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended.html);
the noble-ed25519 source serves as a sanity check that we transcribed them
correctly. We do not invent our own formula.

### 4.7 Signature surface

```lean
namespace Ed25519
def derivePublicKey (sk : ByteArray) : ByteArray              -- 32 → 32
def sign            (sk msg : ByteArray) : ByteArray          -- (32, ·) → 64
def verify          (pk sig msg : ByteArray) : Bool           -- (32, 64, ·) → Bool
end Ed25519
```

- `derivePublicKey` expects exactly 32 input bytes; we leave validation as a
  precondition (callers passing the wrong size get an `unreachable!` — TBD;
  may instead clamp or pad in `Bytes`).
- `sign` returns exactly 64 bytes.
- `verify` returns `false` on any decoding/structural failure (length wrong,
  R-or-S decode fails, S ≥ ℓ, public-key decode fails, equation fails). It
  **does not throw**; this is the only Ed25519 entry point that can "fail",
  and we keep failure as a `Bool` return per the kickoff guardrail "Public APIs
  are total (no `Option`/`Except` for valid inputs; errors are explicit return
  types for things like signature verification, not exceptions)."

**Verify semantics.** We expose **two** verify entry points:

- `verify` (default): **strict RFC 8032**.
  - Reject if `S ≥ ℓ` (malleability resistance).
  - Reject if the public-key or R encoding is non-canonical (y ≥ p).
  - Reject small-order public keys.
  - Use the **cofactored** verification equation `[8](S·B) = [8]R + [8](k·A)`
    per RFC 8032 §5.1.7 step 4.
- `verifyZip215`: **ZIP-215** (matches noble-ed25519's default).
  - Still requires `S < ℓ`.
  - Accepts non-canonical y-coordinates on R and pk (y ≥ p reduced mod p).
  - Does not reject small-order public keys.
  - Same cofactored equation.

Both share the cofactored equation and `S < ℓ` check; they differ only in
canonicalisation strictness and small-order-pk rejection. They're factored
as a single internal `verifyWith (mode : VerifyMode)` with the two public
wrappers calling it with `.strict` / `.zip215`.

---

## 5. API surface (summary)

Public entry points, fully signed, no surprises:

```lean
-- Hashing
def sha256 (msg : ByteArray) : ByteArray
def sha512 (msg : ByteArray) : ByteArray

structure Sha256Ctx
def Sha256Ctx.init : Sha256Ctx
def Sha256Ctx.update : Sha256Ctx → ByteArray → Sha256Ctx
def Sha256Ctx.finalize : Sha256Ctx → ByteArray

structure Sha512Ctx
def Sha512Ctx.init : Sha512Ctx
def Sha512Ctx.update : Sha512Ctx → ByteArray → Sha512Ctx
def Sha512Ctx.finalize : Sha512Ctx → ByteArray

-- Ed25519
def Ed25519.derivePublicKey (sk : ByteArray) : ByteArray
def Ed25519.sign (sk msg : ByteArray) : ByteArray
def Ed25519.verify       (pk sig msg : ByteArray) : Bool  -- strict RFC 8032
def Ed25519.verifyZip215 (pk sig msg : ByteArray) : Bool  -- ZIP-215, noble-compatible
```

Everything else (field, scalar, curve, internal hashing helpers) lives behind
`private` or in its own namespace; not part of the supported surface for v1.

---

## 6. Test strategy

### 6.1 Where vectors live

In-repo at `tests/vectors/`. **Committed**, not fetched at build time. Two reasons:
- Reproducible builds.
- Offline CI.

Sizes are manageable: SHA-256 short-message vectors are ~30 KB, long-message ~1 MB,
Monte Carlo ~7 KB; SHA-512 similar magnitude. Wycheproof `eddsa_test.json`
is ~50 KB. Total committed test data: under 5 MB.

### 6.2 Parsers

`LeanCrypto.Data.CAVS` parses NIST `.rsp` files (`Len = …`, `Msg = …`,
`MD = …` records) using `Std.Internal.Parsec`. Pattern is taken directly
from gdncc/Cryptography's `Cryptography/Data/CAVS.lean` — we vendor the
idea, not the bytes.

`LeanCrypto.Data.HexString` provides hex ↔ `ByteArray`.

Wycheproof is JSON; we hand-roll a minimal parser since `Lean.Json` is in
core. (No external JSON dep.)

### 6.3 Passing run

Each test runner is a `lean_exe`:
1. Reads its vector file(s).
2. For each test: compute expected, compare bytewise.
3. On mismatch, prints `FAIL` with test index + expected + actual + first
   differing byte offset, exits 1.
4. On full pass, prints `OK <N> vectors`, exits 0.

CI invokes each test runner; any non-zero exit fails the build.

### 6.4 Differential fuzz harness (deferred to milestone 10/11)

A small harness that:
- Generates random `ByteArray`s of varied lengths (0, 1, 55, 56, 63, 64, 65,
  127, 128, 129, 1000, 1MB).
- Runs them through our `sha256` and a reference oracle.
- Reports first mismatch.

The reference oracle is **out-of-process**: invoke `openssl dgst -sha256` (or
`node -e "console.log(require('@noble/hashes/sha2').sha256(Buffer.from(process.argv[2],'hex')).toString('hex'))"`)
from the harness shell script. The harness is NOT a Lean test; it's a
`tests/fuzz.sh` that runs locally on demand. **It is not gated on CI on
day 1.** We add it after the deterministic vectors are passing; it's a
safety net, not a gate.

### 6.5 Known-answer breakdowns we will ship

- **SHA-256**: NIST CAVP short, long, Monte Carlo (~290 + 64 + 100 test cases).
- **SHA-512**: NIST CAVP short, long, Monte Carlo (~290 + 64 + 100 test cases).
- **Ed25519**: RFC 8032 §7.1 vectors (4 of them, edge-case minimal but
  load-bearing), then Wycheproof `eddsa_test.json` (≈110 cases, many of
  which are *negative* — signatures that must fail verify).

### 6.6 Wycheproof expected-failures policy

Some Wycheproof flags label cases that depend on choices RFC 8032 leaves
implementation-defined (e.g. `NonCanonicalPublicKey`, `Bleichenbacher`).
For each Wycheproof case we record:
- The flag set.
- Our expected `result` (valid / invalid).
- A one-line reason if our choice diverges from Wycheproof's expected outcome.

If our strict-mode verify rejects something Wycheproof labels `acceptable`,
we *pass* the case and document the choice (RFC strict > ZIP-215 leniency).
If we *fail* a case Wycheproof labels `valid`, that's a bug; the test runner
fails CI. Documented in `tests/wycheproof_decisions.md` to be written alongside
milestone 10.

---

## 7. Algorithmic & numeric reference (frozen here so it's not lost to context)

### 7.1 SHA-256 (FIPS 180-4 §6.2)

- Block size: 64 bytes.  Output: 32 bytes.  Word: `UInt32`.
- IV `H[0..7]`:
  `0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19`.
- `K[0..63]`: 64 constants (first 32 bits of cube roots of first 64 primes); copied verbatim from
  noble-hashes `sha2.ts` / FIPS 180-4 §4.2.2.
- Boolean functions:
  - `Ch(x,y,z)  = (x AND y) XOR ((NOT x) AND z)`
  - `Maj(x,y,z) = (x AND y) XOR (x AND z) XOR (y AND z)`
- Rotations / shifts:
  - `Σ0(x) = rotr(x,2) XOR rotr(x,13) XOR rotr(x,22)`
  - `Σ1(x) = rotr(x,6) XOR rotr(x,11) XOR rotr(x,25)`
  - `σ0(x) = rotr(x,7) XOR rotr(x,18) XOR (x SHR 3)`
  - `σ1(x) = rotr(x,17) XOR rotr(x,19) XOR (x SHR 10)`
- Schedule: `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]` for `t = 16..63`.
- Compression: 64 rounds; per round
  `T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t]`,
  `T2 = Σ0(a) + Maj(a,b,c)`,
  rotate variables `h←g←f←e←d+T1`, `d←c←b←a←T1+T2`.

### 7.2 SHA-512 (FIPS 180-4 §6.4)

- Block size: 128 bytes.  Output: 64 bytes.  Word: `UInt64`.
- IV `H[0..7]` (UInt64): `0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
  0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1,
  0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179`.
- `K[0..79]`: 80 constants (first 64 bits of cube roots of first 80 primes);
  copied verbatim from FIPS 180-4 §4.2.3.
- Same Ch, Maj as SHA-256 but on `UInt64`.
- Rotations:
  - `Σ0(x) = rotr(x,28) XOR rotr(x,34) XOR rotr(x,39)`
  - `Σ1(x) = rotr(x,14) XOR rotr(x,18) XOR rotr(x,41)`
  - `σ0(x) = rotr(x,1)  XOR rotr(x,8)  XOR (x SHR 7)`
  - `σ1(x) = rotr(x,19) XOR rotr(x,61) XOR (x SHR 6)`
- Length encoded as 128-bit BE in the final-block trailer. The high 64 bits
  are 0 for any feasible input (>2⁶¹ bytes would need many exabytes); we
  emit them as 0 unconditionally and document the assumption.

### 7.3 Merkle-Damgård padding (both)

Append `0x80`, then enough `0x00` bytes to make the final block end aligned
to `blockLen − lenFieldBytes`; then encode `8·totalLen` as a big-endian
unsigned integer of width `lenFieldBytes` (8 for SHA-256, 16 for SHA-512).
If `0x80 + zeros` would overflow the current block, emit a full padded
block first and start a fresh one.

### 7.4 Ed25519 numerics (RFC 8032 §5.1)

- `p = 2²⁵⁵ − 19`.
- `ℓ = 2²⁵² + 27742317777372353535851937790883648493`.
- Curve constant `d = −121665/121666 mod p =
  0x52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3`.
- Base point `B`:
  - `Bx = 0x216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a`
  - `By = 0x6666666666666666666666666666666666666666666666666666666666666658`
- Cofactor: 8.
- Square-root constant `sqrtM1 = 2^((p−1)/4) mod p =
  0x2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0` (sanity-checked
  against noble-ed25519's `RM1`).

### 7.5 RFC 8032 sign

```
h = SHA-512(sk)                       -- 64 bytes
s = clamp(h[0..32])                   -- scalar; clamp = clear bits 0,1,2 and 255; set bit 254
prefix = h[32..64]                    -- 32 bytes
A = s · B                             -- public-key point
encA = encode(A)                      -- 32 bytes
r = SHA-512(prefix || msg) mod ℓ      -- 64-byte hash reduced mod ℓ
R = r · B
encR = encode(R)
k = SHA-512(encR || encA || msg) mod ℓ
S = (r + k · s) mod ℓ
return encR || little-endian-32-bytes(S)   -- 64 bytes total
```

### 7.6 RFC 8032 verify (strict mode — our default)

```
require sig.size == 64
require pk.size == 32
encR := sig[0..32]
S    := little-endian-32-bytes-to-Nat(sig[32..64])
require S < ℓ
R := decode(encR)            -- fail-closed if non-canonical
A := decode(pk)              -- fail-closed if non-canonical
k := SHA-512(encR || pk || msg) mod ℓ
return  [8] · (S · B)  ==  [8] · R  +  [8] · (k · A)
```

### 7.7 Modular inverse and square root choices

- `inv`: Fermat (`pow a (p-2)`). v1 simplicity > speed.
- `sqrt`: the p ≡ 5 (mod 8) formula. Returns `none` for non-squares.
- `ScalarL.reduce512Bit`: build a `Nat` from 64 little-endian bytes, then
  `% ℓ`. Barrett reduction is post-v1.

---

## 8. Constant-time / side-channel posture (documented leaks)

Per the kickoff, fixing these is out of scope. We **document** them in v1
docstrings and call them out in `README.md`:

- `EdPoint.mul` (double-and-add) branches on each bit of the scalar. Leaks
  the secret scalar `s` and the per-message ephemeral `r` via timing.
- `Fp25519.inv` (Fermat) executes a fixed addition chain; **does not** leak
  the input. Safe.
- `Fp25519.sqrt` branches on which candidate squares to the input. Inputs
  here are public (the y-coordinate during decode), so this is not a secret-key
  leak.
- `ScalarL.reduce` via `Nat.mod` may not be constant-time in the runtime.
  Inputs are SHA-512 outputs, so the relevant secret is the per-message `r`.
- Wycheproof has small-order-point attacks; our strict decode rejects them, so
  this is a correctness defence, not a timing defence.

Future work would replace `EdPoint.mul` with a Montgomery-ladder or wNAF +
precomputed base-table, and replace `Fp25519` with a constant-time limb
representation.

---

## 9. Risks & known Lean limitations

- **Elaborator timeouts on long unrolled loops.** Per the gdncc/Cryptography
  source, loops "cannot be unrolled for now…because of an issue with Lean's
  elaborator." Mitigation: write the SHA-256 64-round and SHA-512 80-round
  compression as explicit `for` loops over `Fin 64` / `Fin 80`, *not* as
  manually unrolled blocks. If we hit the same elaborator wall, copy
  gdncc/Cryptography's `set_option maxRecDepth 1000` workaround at the
  call site (used in their `mkFixedBuffer`).
- **`Nat` arithmetic is slow.** v1 `Fp25519`/`ScalarL` are `Nat`-backed.
  Single Ed25519 sign/verify is on the order of seconds, not microseconds.
  Acceptable for the goal (correctness) and for test-vector validation.
  Wycheproof's ~110 cases should still complete in well under a minute.
  If they don't, we drop down to a limb-based representation as a follow-on,
  *not* in v1.
- **`ByteArray` indexed access requires proofs.** gdncc/Cryptography handles
  this by carrying `omega`-provable size invariants on subtypes; we adopt
  the same pattern in `LeanCrypto.Bytes`. Risk: proof obligations blow up
  for some non-obvious case. Mitigation: use unsized `ByteArray.get!` *only*
  in non-hot paths (e.g. parsing test vectors), never in the compression loop.
- **No mutable global state.** All "tables" are `Array α` literals at the
  top of their module, evaluated once at load. Confirmed compatible with
  Lean's evaluation model.
- **JSON parsing of Wycheproof at compile time vs runtime.** We parse at
  **runtime** in the test runner (`Lean.Json.parse`); compile-time parsing
  via `#eval` is a non-goal and unnecessary.

---

## 10. Spec vs noble divergences (flagged for review)

These are differences between **RFC 8032** / **FIPS 180-4** and noble-ed25519's
behavior that the test vectors don't unambiguously resolve. We declare a
default choice; flag if you want it different.

1. **Verify modes — we ship both.**
   - `verify` (default): strict RFC 8032 §5.1.7. Rejects non-canonical
     encodings, S ≥ ℓ, small-order pk; uses cofactored equation
     `[8]·(S·B) = [8]·R + [8]·(k·A)`.
   - `verifyZip215`: matches noble-ed25519's default. Accepts non-canonical
     y-coordinates; still rejects S ≥ ℓ; same cofactored equation.
   - Wycheproof has both "strict" and "acceptable" cases. Our M10 runner
     iterates each case once per variant: cases that are *valid under both*
     must verify under both; cases labelled `invalid` must fail under both;
     cases labelled `acceptable` are expected to fail strict and pass ZIP-215
     (verified per case).

2. **Small-order public-key rejection.**
   - RFC 8032 doesn't explicitly mandate it; noble strict does.
   - **Our v1 default: reject small-order public keys.** Matches noble-strict;
     defends against known attacks. Cheap to implement (multiply by `ℓ`,
     check identity).

3. **SHA-512 length encoding for inputs > 2⁶¹ bytes.**
   - SHA-512 spec uses a 128-bit length field. No realistic input reaches
     2⁶¹ bytes, but the encoding is defined.
   - **Our v1 behavior: emit `(0 : UInt64) :: 8·totalLen.toUInt64BE`.** I.e.
     high 64 bits are 0. Same as every real-world implementation. No test
     vector exercises this anyway.

4. **`sign` with non-32-byte `sk`.**
   - RFC 8032 defines `sk` as exactly 32 bytes.
   - **Our v1 behavior: defined only on 32-byte `sk`.** Callers passing wrong
     sizes get an `unreachable!` or an explicit precondition (TBD; finalised
     in milestone 9). We **don't** truncate or zero-pad.

---

## 11. Resolved decisions (post-review)

1. **Verify modes:** ship **both** strict RFC 8032 (default `verify`) and
   `verifyZip215`. See §4.7 and §10.1 for details.
2. **Lean toolchain pin:** `leanprover/lean4:v4.27.0`, matching gdncc/Cryptography.
3. **Lake layout:** single `lean_lib LeanCrypto` plus one `lean_exe` per test
   runner. Splitting into multiple libraries is not worth the ceremony for a
   single-repo project; gdncc/Cryptography uses the same shape.
4. **CI:** GitHub Actions wired up from M1 (build + run every test exe on
   push/PR). Local `lake test` (or equivalent) also expected to work from
   a clean checkout — CI is not a replacement for the local loop.
