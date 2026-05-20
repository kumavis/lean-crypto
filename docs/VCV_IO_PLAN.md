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

> **Status (post-M18):** Phase A + B's modeling layer are shipped. Both
> `PerfectlyComplete` promises (§5.1, §6) were deferred — they required a
> `verify_sign_self` theorem that turned out to be person-months of
> algebraic-correctness proof. See `docs/PROOFS_ROADMAP.md` for what was
> shipped instead (per-vector `native_decide` theorems + the
> `ed25519_completes_on_rfc_vectors` wrapper lemma) and where that path
> bottoms out (M24: `add_assoc_crossEq` exceeds `grobner`'s current
> heuristic budget). The wrapper-level VCV-io types and tests are all
> green on CI.

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

After the package split (post-M18), all wrapper modules live in the
nested Lake package at `packages/lean-crypto-vcvio/`:

```
packages/lean-crypto-vcvio/
├── lakefile.lean                       -- requires lean-crypto (../..) + Mathlib + VCV-io
├── LeanCryptoVCVio.lean                -- root re-exports
├── LeanCryptoVCVio/
│   ├── Prelude.lean                    -- VCV-io / Mathlib opens, drawBytes helper
│   ├── Hash/
│   │   ├── SHA256.lean                 -- sha256OC : ByteArray → OracleComp spec ByteArray
│   │   └── SHA512.lean                 -- sha512OC
│   ├── Signature/
│   │   ├── Ed25519.lean                -- SignatureAlg, deterministic SHA-512
│   │   └── Ed25519ROM.lean             -- ROM building blocks (signROM, etc.)
│   └── Games/
│       └── Smoke.lean                  -- UFCMA exp with trivial adv; sanity-only
├── LeanCryptoProofs.lean               -- root re-exports for proofs
├── LeanCryptoProofs/                   -- M19-M24 algebraic foundations
└── Tests/VCVio/
    ├── Hash.lean                       -- simulateQ ∘ sha256OC = LeanCrypto.sha256
    ├── Ed25519Det.lean                 -- RFC 8032 §7.1 vector through SignatureAlg
    ├── Ed25519ROM.lean                 -- ROM Ed25519 with honest sha512 oracle
    ├── GameSmoke.lean                  -- trivial-adv UFCMA exp evaluates to false
    └── Smoke.lean                      -- M13 dep-wiring smoke
```

The outer `lean-crypto` package keeps zero deps; consumers of the
wrapper require this inner package via Lake's git `subDir` syntax.

---

## 3. Lakefile / dependencies

The wrapper lives in its own Lake package. Its `lakefile.lean`:

```lean
require «lean-crypto» from ".." / ".."   -- relative to repo root in monorepo
require "leanprover-community" / "mathlib" @ git "v4.29.0"
require VCVio from git "https://github.com/dtumad/VCV-io" @ "v4.29.0"

package «lean-crypto-vcvio» where
lean_lib LeanCryptoVCVio where ...
```

The outer `lean-crypto` lakefile has **no Mathlib or VCV-io requires** —
consumers depending only on the core get a clean dep tree.

VCV-io tags a release matching each Mathlib bump (we use `v4.29.0`). Bumps
land via lakefile edits + `lake update` in the inner package.

---

## 4. Toolchain bump (M12 precursor) — *shipped*

VCV-io's `v4.29.0` tag pins Lean 4.29.0 + Mathlib 4.29.0; v1 of the
library was on Lean 4.27.0. M12 bumped `lean-toolchain` to
`leanprover/lean4:v4.29.0` (originally planned at 4.28.0; revised mid-
flight to match VCV-io's tag).

The bump landed as a **standalone PR** before the wrapper work — zero
code changes were needed beyond the toolchain pin. Every existing test
exe and the differential fuzz harness stayed green on 4.29.0.

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

### 5.1 `PerfectlyComplete` — what we shipped vs. what we planned

VCV-io's `PerfectlyComplete sigAlg` asserts:

```
∀ msg, (do let (pk, sk) ← keygen; verify pk msg (← sign pk sk msg)) ↝ pure true
```

For our `ed25519` this reduces (by `pure_bind` / `simulateQ`-irrelevance) to:

```
∀ sk msg, LeanCrypto.verify (derivePublicKey sk) (LeanCrypto.sign sk msg) msg = true
```

Phase B asked core to grow exactly one lemma:

```lean
theorem Ed25519.verify_sign_self (sk msg : ByteArray) (hsk : sk.size = 32) :
    verify (derivePublicKey sk) (sign sk msg) msg = true
```

**That lemma was *not* shipped** — the fallback flagged in this section
(per-vector decide) is what landed. The post-mortem in
`docs/PROOFS_ROADMAP.md` documents the M20–M24 sequence that:

1. Proved `verify_sign_self_rfc_{1,2,3}` for the RFC 8032 §7.1 vectors
   via `native_decide` (with the documented `ofReduceBool` axiom cost).
2. Wrapped them into `ed25519_completes_on_rfc_vectors` at the
   `SignatureAlg`-pipeline level (`docs/PROOFS_ROADMAP.md` M20).
3. Laid in algebraic foundations on `EdPoint` (`ProjEq` Setoid, cast
   lemmas, group laws on `add` except associativity).
4. Probed associativity (M24 spike); it exceeds Lean's current
   `grobner` heuristic budget. Deferred indefinitely.

Net for the wrapper: the universal `PerfectlyComplete ed25519` is
*not* an instance in `LeanCryptoVCVio/`. The genuine completeness
statement available to downstream proofs is
`LeanCryptoVCVio.Ed25519Proofs.ed25519_completes_on_rfc_vectors`,
quantified over the RFC test corpus.

---

## 6. SHA-512 as a RandomOracle — *partially shipped*

VCV-io's `VCVio/OracleComp/QueryTracking/RandomOracle.lean` defines a
caching/lazy random oracle. For Ed25519ROM we replace every internal
`sha512 x` call with `query bs` against an oracle of spec
`ByteArray →ₒ ByteArray`.

```lean
-- Final shape (note the spec is indexed by ByteArray, not Unit):
def sha512ROSpec : OracleSpec ByteArray := fun _ => ByteArray

def signROM (sk msg : ByteArray) : OracleComp sha512ROSpec ByteArray := do
  let h ← query (spec := sha512ROSpec) sk
  let s := clampScalar (h.extract 0 32)
  -- … same RFC 8032 shape, but each sha512 call → query bs
```

**Scope deviation in M16:** the originally-planned `ed25519ROM :
SignatureAlg (OracleComp sha512ROSpec) …` instance was *not* shipped.
A SignatureAlg that includes keygen randomness needs a combined
`unifSpec + sha512ROSpec` spec, which is more plumbing than M16's
scope. What landed instead are the building blocks
(`derivePublicKeyROM`, `signROM`, `verifyROM`) typed in
`OracleComp sha512ROSpec`, plus a test that runs them under
`sha512Impl : QueryImpl sha512ROSpec Id` (instantiating the oracle
with the real SHA-512) and confirms byte-equality with the RFC vectors.

The ROM variant remains the **shape** that UF-CMA proofs would target.
Phase B shipped the modeling, not the proof — same fate as Phase A's
PerfectlyComplete.

---

## 7. Tests / acceptance — *what shipped*

### Phase A (M14)
- `Tests/VCVio/Hash`: 17 message lengths × 2 algos = 34 cases asserting
  `simulateQ emptyImpl (shaXOC m) |>.run = shaX m`. ✓

### Phase B (M15–M17)
- `Tests/VCVio/Ed25519Det`: 3 RFC 8032 §7.1 vectors × 3 ops
  (`ed25519.sign` + strict / ZIP-215 verify) = 9 byte-exact checks via
  `simulateQ` with `constUnifImpl`. ✓
- `Tests/VCVio/Ed25519ROM`: 3 RFC vectors × 3 ops (`derivePublicKeyROM`,
  `signROM`, `verifyROM`) = 9 checks via `simulateQ` with `sha512Impl`
  wired to the real SHA-512. The `PerfectlyComplete ed25519ROM`
  typecheck **was not shipped** — same deferral as Phase A. ✓ (runtime
  checks only)
- `Tests/VCVio/GameSmoke`: `smokeGame` (the inner experiment body of
  `unforgeableExp ed25519 trivialAdv`, lifted to `ProbComp Bool` since
  `unforgeableExp` returns `noncomputable SPMF Bool`) evaluates to
  `false` under `simulateQ` with `constUnifImpl`. ✓

Same guardrail as core: no `sorry`, `partial`, `unsafe`, or `extern`. CI
forbidden-tokens grep applies to `LeanCryptoVCVio/`,
`LeanCryptoProofs/`, and `Tests/VCVio/`.

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

## 9. Risks — post-mortem

- **VCV-io API churn.** Mitigated: `v4.29.0` tag pin held throughout
  M13–M18. No bumps were needed.
- **`PerfectlyComplete` proof of `verify_sign_self`.** Materialised
  exactly as flagged. The "may be harder than expected" was right; the
  external survey (`docs/PROOFS_ROADMAP.md` M21) estimated 4–8
  person-months. We took the documented fallback: per-RFC-vector
  `native_decide` theorems land an honest weakened completeness
  statement; universal proof deferred indefinitely.
- **Mathlib in CI.** `lake exe cache get` worked fine. The `build` job
  initially failed for a *different* reason — missing explicit
  `lake update` after M13 added the Mathlib + VCV-io `require`s —
  fixed in a follow-up commit. Cold CI time: ~12 min for `vcvio-build`.
- **4.27 → 4.29 toolchain bump.** No code changes needed.

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
5. **VCV-io pin:** Tag-per-toolchain (e.g. `v4.29.0`); bump together with
   our Lean / Mathlib bumps.
