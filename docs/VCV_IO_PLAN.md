# `lean-crypto` — VCV-io wrapper plan

Wrapping our pure-functional Lean implementation of SHA-256 / SHA-512 / Ed25519
into [VCV-io](https://github.com/dtumad/VCV-io)'s `OracleComp` framework so the
primitives are usable from VCV-io games and proof-targets.

This plan covers two phases shipping together (separate PRs):

- **Phase A — Deterministic adapters.** Trivial lifts `f → pure ∘ f`. Lets a
  VCV-io program call our primitives without import wrangling.
- **Phase B — Oracle interfaces.** A `SignatureAlg` instance for Ed25519, a
  RandomOracle-modeled SHA-512 variant, and one smoke-test UF-CMA experiment.
  Modeling only — no security proofs.

Phase C (actual UF-CMA reductions) is **out of scope**. The surface we ship
must not preclude it.

---

## 1. Why this is feasible without touching core

The core `LeanCrypto` library is pure-functional, Mathlib-free, and operates
on `ByteArray`. VCV-io expects monadic computations in `OracleComp spec α` for
some `spec : OracleSpec ι`. Pure functions lift to `OracleComp` as
`pure ∘ f`; deterministic state-passing lifts to `do let r ← pure …`.

The wrapper lives in a **separate `lean_lib`** in the same lakefile. The
wrapper imports `LeanCrypto` (no Mathlib) **and** Mathlib + VCV-io. The core
library keeps its zero-dependency posture.

---

## 2. Module layout

```
LeanCryptoVCVio.lean                  -- root re-exports
LeanCryptoVCVio/
  Prelude.lean                        -- VCV-io / Mathlib opens, drawBytes helper
  Hash/
    SHA256.lean                       -- sha256OC : ByteArray → OracleComp []ₒ ByteArray
    SHA512.lean                       -- sha512OC + ROM-shape signature alias
  Signature/
    Ed25519.lean                      -- SignatureAlg, deterministic SHA-512
    Ed25519ROM.lean                   -- SignatureAlg, SHA-512 modeled as RandomOracle
  Games/
    Smoke.lean                        -- UFCMA exp with trivial adv; sanity-only
Tests/VCVio/
  Hash.lean                           -- simulateQ ∘ sha256OC = LeanCrypto.sha256
  Ed25519Det.lean                     -- RFC 8032 §7.1 vector through SignatureAlg
  Ed25519ROM.lean                     -- PerfectlyComplete + smoke
  GameSmoke.lean                      -- trivial-adv UFCMA exp evaluates to false
```

---

## 3. Lakefile / dependencies

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

require VCVio from git
  "https://github.com/dtumad/VCV-io" @ "<commit sha pinned at M13>"

lean_lib LeanCryptoVCVio where
  buildType := BuildType.release
```

VCV-io is unreleased (no semver). We pin a specific commit SHA via
`lake-manifest.json` and bump it explicitly when we want a new version.

---

## 4. Toolchain bump (M12 precursor)

VCV-io is on Lean 4.28.0 + Mathlib 4.28.0; we're on 4.27.0. The bump is a
**standalone PR** before the wrapper work starts.

- Update `lean-toolchain` to `leanprover/lean4:v4.28.0`.
- Run `lake build` on everything we have today; fix any breaks (likely
  small — `Array.modify` or `String.trim`-style API tweaks).
- Re-run NIST CAVP, RFC 8032, Wycheproof, and the differential fuzz harness.

Keeping it standalone means the existing test surface stays green on 4.28
before we add a Mathlib dep on top.

---

## 5. The Ed25519 `SignatureAlg` instance

VCV-io defines (in `VCVio/CryptoFoundations/SignatureAlg.lean`):

```
structure SignatureAlg (m : Type → Type v) (M PK SK S : Type) extends ExecutionMethod m where
  keygen : m (PK × SK)
  sign   : PK → SK → M → m S
  verify : PK → M → S → m Bool
```

Mapping for Ed25519:

| Field | Type for Ed25519                         |
|-------|------------------------------------------|
| `M`   | `ByteArray` (the message)                |
| `PK`  | `ByteArray` (32 bytes)                   |
| `SK`  | `ByteArray` (32 bytes, the seed)         |
| `S`   | `ByteArray` (64 bytes)                   |
| `m`   | `OracleComp unifSpec` for `ed25519` (deterministic except for keygen randomness); `OracleComp (ByteArray →ₒ ByteArray)` for `ed25519ROM` |

```lean
namespace LeanCryptoVCVio

def ed25519 : SignatureAlg (OracleComp unifSpec) ByteArray ByteArray ByteArray ByteArray where
  keygen := do
    let sk ← drawBytes 32                          -- 256 coin flips, packed
    return (LeanCrypto.derivePublicKey sk, sk)
  sign  _pk sk msg := pure (LeanCrypto.sign sk msg)
  verify pk msg sig := pure (LeanCrypto.verify pk sig msg)

end LeanCryptoVCVio
```

`drawBytes : (n : Nat) → OracleComp unifSpec ByteArray` lives in
`LeanCryptoVCVio.Prelude`. It's the wrapper's only piece of real monadic
plumbing.

### 5.1 `PerfectlyComplete` and the core lemma we need

VCV-io's `PerfectlyComplete sigAlg` asserts:

```
∀ msg, (do let (pk, sk) ← keygen; verify pk msg (← sign pk sk msg)) ↝ pure true
```

For our `ed25519` this reduces (by `pure_bind` / `simulateQ`-irrelevance) to:

```
∀ sk msg, LeanCrypto.verify (derivePublicKey sk) (LeanCrypto.sign sk msg) msg = true
```

We have this **as a test** (every RFC + Wycheproof vector exercises it), but
not as a `theorem` in core. Phase B asks core to grow exactly one lemma:

```lean
theorem Ed25519.verify_sign_self (sk msg : ByteArray) (hsk : sk.size = 32) :
    verify (derivePublicKey sk) (sign sk msg) msg = true
```

This is the **single load-bearing ask** of the wrapper on core. If the proof
turns out hard, Phase B falls back to per-vector `Decidable.decide` blocks
rather than universal completeness — flagged in M15 below.

---

## 6. SHA-512 as a RandomOracle

VCV-io's `VCVio/OracleComp/QueryTracking/RandomOracle.lean` defines a
caching/lazy random oracle. For Ed25519ROM we replace every internal
`sha512 x` call with `query () x` against an oracle of spec
`ByteArray →ₒ ByteArray`.

```lean
def sha512ROSpec : OracleSpec Unit := fun _ => ByteArray  -- (ByteArray →ₒ ByteArray)

def ed25519ROM :
    SignatureAlg (OracleComp sha512ROSpec) ByteArray ByteArray ByteArray ByteArray where
  keygen := do
    let sk ← drawBytes 32
    let h ← query (spec := sha512ROSpec) () sk
    -- … same RFC 8032 shape, but each sha512 call → query
```

The ROM variant is the **shape** that UF-CMA proofs would target. Phase B
ships the modeling, not the proof.

---

## 7. Tests / acceptance

### Phase A (M14)
- `Tests/VCVio/Hash`: For 20 random messages, `simulateQ idQueryImpl (sha256OC msg)`
  byte-equals `LeanCrypto.sha256 msg`. Same for SHA-512.

### Phase B (M15–M17)
- `Tests/VCVio/Ed25519Det`: RFC 8032 §7.1 vector 1 round-trips through the
  `SignatureAlg` instance: seed `keygen`'s `unifSpec` via a fixed-bit
  `QueryImpl`, then `sign` and `verify` match RFC bytes.
- `Tests/VCVio/Ed25519ROM`: `PerfectlyComplete ed25519ROM` typechecks; one
  keygen→sign→verify smoke trip through `simulateQ`.
- `Tests/VCVio/GameSmoke`: `unforgeableExp ed25519 trivialAdv` evaluates to
  `false` (trivial adversary returns `(msg, garbage_sig)`).

Same guardrail as core: no `sorry`, `partial`, `unsafe`, or `extern`. CI
forbidden-tokens grep applies to `LeanCryptoVCVio/` and `Tests/VCVio/`.

---

## 8. CI

New job in `.github/workflows/ci.yml`, runs in parallel with existing `build`:

```yaml
vcvio-build:
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v4
    - name: Install elan
      run: …
    - uses: actions/cache@v4
      with:
        path: .lake
        key: lake-vcvio-${{ runner.os }}-${{ hashFiles('lean-toolchain', 'lakefile.lean', 'lake-manifest.json') }}
    - name: Mathlib cache
      run: lake exe cache get
    - name: Build wrapper
      run: lake build LeanCryptoVCVio
    - name: Run wrapper tests
      run: for exe in .lake/build/bin/Tests-VCVio-*; do "$exe"; done
```

Cold first run ~5 min (Mathlib download); warm runs ~1–2 min. If `lake exe
cache get` ever breaks, we gate this job behind a nightly schedule instead
of every push.

---

## 9. Risks

- **VCV-io API churn.** No stable release. Pin a SHA in `lake-manifest.json`;
  budget time per bump. If breaking changes are frequent, vendor a snapshot.
- **`PerfectlyComplete` proof of `verify_sign_self`.** Proving universal
  completeness of our own Ed25519 implementation may be harder than expected.
  Fallback: per-vector `Decidable.decide` blocks. Flagged in M15.
- **Mathlib in CI.** Slow even with cache. `lake exe cache get` is the
  primary mitigation. Fallback: nightly-only.
- **4.27 → 4.28 toolchain bump.** Low probability of large breakage in our
  small surface, but treat M12 as standalone so it doesn't ambush wrapper work.

---

## 10. Out of scope (v1 + B)

- Actual UF-CMA reductions or any security proof.
- Performance of `simulateQ`'d primitives.
- ML-KEM / ML-DSA interop with VCV-io's `LatticeCrypto/`.
- Re-proving SHA-256 collision-resistance or anything in ROM.

---

## 11. Resolved decisions

1. **Scope:** Phase A + B together, Phase C deferred.
2. **Layout:** Same repo, new `lean_lib LeanCryptoVCVio`. Core stays
   Mathlib-free.
3. **CI:** Gated job with `lake exe cache get`. Falls back to nightly if
   `cache get` becomes unreliable.
4. **Toolchain bump:** Standalone precursor PR (M12) before wrapper work.
5. **VCV-io pin:** Specific commit SHA in `lake-manifest.json`. Manual bumps.
