# `lean-crypto` — VCV-io wrapper roadmap

Seven milestones from "4.27 with no Mathlib" to "Ed25519 plugged into VCV-io's
`SignatureAlg` and UF-CMA scaffolding, CI-green." Each milestone is one PR.

See `docs/VCV_IO_PLAN.md` for the design, and `docs/PROOFS_ROADMAP.md` for
the M19–M24 follow-on proof work.

## Status snapshot

| Milestone | Status | Notes |
|-----------|--------|-------|
| M12 | ✅ | Toolchain bumped 4.27 → 4.29.0 (one minor past originally-planned 4.28 to match VCV-io's tag) |
| M13 | ✅ | Mathlib + VCV-io v4.29.0 wired; `lean_lib LeanCryptoVCVio` builds |
| M14 | ✅ | Deterministic adapters for SHA-256/512 + Ed25519; 34-case test |
| M15 | ⚠ | `SignatureAlg` instance landed; `PerfectlyComplete` deferred (see M20 in `docs/PROOFS_ROADMAP.md`) |
| M16 | ⚠ | `signROM`/`verifyROM`/`derivePublicKeyROM` landed; `PerfectlyComplete` deferred; no `SignatureAlg` instance for ROM yet (out-of-scope deviation) |
| M17 | ✅ | UF-CMA smoke wiring (`trivialAdv` + smokeGame) |
| M18 | ✅ | CI `vcvio-build` job + README integration section |

The ⚠ rows ship working code matching the runtime expectations but
explicitly defer the `PerfectlyComplete` proof. The completeness story
moves to `docs/PROOFS_ROADMAP.md` (M19–M24), which delivers
machine-checked completeness on the RFC 8032 vectors via `native_decide`
plus an algebraic-foundations layer.

---

## M12 · Toolchain bump to Lean 4.29.0 — small

**Goal.** Existing code compiles and every test passes on Lean 4.29.0. No
new features, no new deps. (Originally planned at 4.28.0; bumped one minor
during M13 wiring to match VCV-io's latest tag.)

**Deliverables.**
- `lean-toolchain` → `leanprover/lean4:v4.29.0`.
- Fix any compile errors surfaced by the bump.
- All M1–M11 deliverables continue to pass.

**Acceptance.**
- `lake build` succeeds on a clean checkout against 4.29.0.
- Every existing test exe exits 0.
- Differential fuzz (`tests/diff/run.sh`) still passes.
- CI green.

---

## M13 · Lakefile + dependencies — small

**Goal.** Mathlib and VCV-io are wired into the lakefile. Empty
`LeanCryptoVCVio` library builds. No symbols added yet beyond a stub.

**Deliverables.**
- `lakefile.lean`:
  - `require "leanprover-community" / "mathlib" @ git "v4.29.0"`.
  - `require VCVio from git "https://github.com/dtumad/VCV-io" @ "v4.29.0"`.
  - `lean_lib LeanCryptoVCVio` with `buildType := .release`.
- `LeanCryptoVCVio.lean` (root, empty re-exports).
- `LeanCryptoVCVio/Prelude.lean` — imports VCV-io / Mathlib, defines `drawBytes`.
- `lake-manifest.json` regenerated.
- Test exe `Tests.VCVio.Smoke` that prints `OK 0 vectors`.

**Acceptance.**
- `lake exe cache get && lake build LeanCryptoVCVio` succeeds.
- `Tests.VCVio.Smoke` exits 0.
- Core `LeanCrypto` library still builds with **no Mathlib imports** (verified
  by grep on `LeanCrypto/**.lean`).

---

## M14 · Phase A — deterministic adapters — small

**Goal.** SHA and Ed25519 primitives are accessible from `OracleComp` as
trivial pure-computation lifts. `simulateQ` of each adapter byte-equals the
corresponding pure function.

**Shipped:**
- `LeanCryptoVCVio/Hash/SHA256.lean` — `sha256OC : ByteArray → OracleComp spec ByteArray` (polymorphic in `spec`).
- `LeanCryptoVCVio/Hash/SHA512.lean` — `sha512OC`.
- Adapter-style lifts of `derivePublicKey`, `sign`, `verify`, `verifyZip215`
  in `LeanCryptoVCVio/Signature/Ed25519.lean` (`SignatureAlg` instance landed
  in M15).
- `LeanCryptoVCVio/Prelude.lean` — added `emptyImpl : QueryImpl []ₒ Id`.
- `Tests/VCVio/Hash.lean` — 17 message lengths × 2 algos = 34 cases asserting
  `simulateQ emptyImpl (shaXOC m) |>.run = shaX m` byte-exactly.

**Acceptance:** all 34 cases green. (Original plan said 40 × 2 = 80 cases at
20 random msgs per length; we shipped a 17-length sweep at 1 msg each instead
since the algorithm has no per-message variability beyond length boundaries.)

---

## M15 · Phase B.1 — `SignatureAlg` instance + `PerfectlyComplete` — medium

**Goal.** Ed25519 is a `SignatureAlg ProbComp …`. RFC 8032 vector 1
round-trips through it.

**Shipped:**
- `LeanCryptoVCVio/Signature/Ed25519.lean`:
  - `ed25519 : SignatureAlg ProbComp ByteArray ByteArray ByteArray ByteArray`
    via a shared `mkEd25519` builder (also yields `ed25519Zip215`).
  - `@[simp]` lemmas `ed25519_sign`, `ed25519_verify`, etc.
- `LeanCryptoVCVio/Prelude.lean` additions:
  - `drawBytes (n : Nat) : ProbComp ByteArray` via `mapM` over `List.range n`
    sampling `UInt8` per `$ᵗ`.
  - `constUnifImpl : QueryImpl unifSpec Id` (returns 0 to every query;
    fine for deterministic sign/verify under `simulateQ`).
- `Tests/VCVio/Ed25519Det.lean` — 3 RFC 8032 §7.1 short vectors × 3 ops
  (sign + strict verify + ZIP-215 verify) = 9 checks, all byte-equal to
  the RFC.

**Deferred:** `instance : PerfectlyComplete ed25519` is *not* shipped.
The universal `verify_sign_self` theorem it depends on requires the
algebraic-correctness proof of the 2008-HWCD addition formula (the
M21 external research estimated 4–8 person-months); we follow every
other Ed25519 formalisation at scale (HACL\*, s2n-bignum, EasyCrypt)
and axiomatise / defer the group law.

**The fallback path** (per-vector `Decidable.decide`) flagged in the
original plan was the right call. It evolved into the M20 work in
`docs/PROOFS_ROADMAP.md`, which proves `verify_sign_self_rfc_{1,2,3}`
via `native_decide` and bundles them into a wrapper-level
`ed25519_completes_on_rfc_vectors` lemma — the weakened-but-genuine
completeness statement downstream VCV-io game proofs can use.

**Acceptance:** all 9 RFC checks green; wrapper builds with no
forbidden tokens; deferral documented in source.

---

## M16 · Phase B.2 — SHA-512 as RandomOracle — medium

**Goal.** SHA-512 modeled as an abstract random oracle for Ed25519's
internal hashing.

**Shipped:**
- `LeanCryptoVCVio/Signature/Ed25519ROM.lean`:
  - `sha512ROSpec : OracleSpec ByteArray := fun _ => ByteArray` (note:
    the spec is indexed by `ByteArray`, not `Unit` as originally
    sketched — the input *is* the bytes to hash, the range is the
    digest).
  - `derivePublicKeyROM`, `signROM`, `verifyROM` over
    `OracleComp sha512ROSpec`. `verifyROM` is strict-only
    (`verifyZip215ROM` is straightforward to add if needed).
  - `sha512Impl : QueryImpl sha512ROSpec Id` instantiates the oracle
    with the real `LeanCrypto.Hash.SHA512.sha512`.
- `Tests/VCVio/Ed25519ROM.lean`: 3 RFC vectors × 3 ops (derive + sign +
  verify) = 9 checks; all byte-equal to RFC when the oracle is wired
  to honest SHA-512.

**Scope deviation:** the original plan called for a *new* `SignatureAlg
ed25519ROM` instance over `OracleComp sha512ROSpec`. Building that
requires combining `unifSpec` (for keygen randomness) with the hash
oracle (for sign/verify), which is more plumbing than M16's scope. We
shipped the OracleComp-typed building blocks (`derivePublicKeyROM`,
`signROM`, `verifyROM`) directly; the SignatureAlg-over-combined-spec
version would live in a follow-up.

**Deferred:** `PerfectlyComplete ed25519ROM` — same algebraic-correctness
dependency as M15's PerfectlyComplete.

**Two private helpers** (`clampScalar`, `projEq`) are re-stated verbatim
in this module because the core ones are `private`. Documented in the
source as fragile against drift; promoting them to a shared
`LeanCrypto.Signature.Ed25519.Internals` module is a follow-up.

**Acceptance:** all 9 ROM-vs-real-SHA checks green.

---

## M17 · Phase B.3 — UF-CMA smoke game — small

**Goal.** Validate that the `SignatureAlg` instance plugs into VCV-io's
`unforgeableExp` / `unforgeableAdv` infrastructure.

**Shipped:**
- `LeanCryptoVCVio/Games/Smoke.lean`:
  - `trivialAdv : SignatureAlg.unforgeableAdv ed25519` returning `(ε, ε)`
    ignoring the public key.
  - `smokeGame : ProbComp Bool` — a concrete `OracleComp`-level mirror
    of the experiment body (`unforgeableExp` itself returns `SPMF Bool`
    via the noncomputable `ProbCompRuntime.probComp`, so we drop one
    level to run it).
- `Tests/VCVio/GameSmoke.lean` — runs `smokeGame` through `simulateQ`
  with `constUnifImpl` (fixed-seed keygen), asserts result is `false`.

**Acceptance:** smoke test green. No security claims — shape validation
only.

---

## M18 · CI job + README — small

**Goal.** Wrapper builds and tests run on every push. README documents what
the wrapper is for.

**Shipped:**
- `.github/workflows/ci.yml` with a parallel `vcvio-build` job:
  - `lake update` then `lake exe cache get` for Mathlib oleans.
  - `git submodule update --init --depth 1` for VCV-io's
    mlkem-native / mldsa-native / c-fn-dsa submodules.
  - `lake build LeanCryptoVCVio` + each `Tests.VCVio.*` exe.
  - Each `Tests-VCVio-*` runs.
- Existing `build` job also picked up an explicit `lake update` step
  (needed once the lakefile started requiring Mathlib + VCV-io) and
  per-step failure-tail capture to `$GITHUB_STEP_SUMMARY` so future
  regressions surface in the API without admin log access.
- Forbidden-tokens grep extended to `LeanCryptoVCVio/`,
  `LeanCryptoProofs/`, and `Tests/VCVio/`.
- New CI guard: core `LeanCrypto/**.lean` must not import Mathlib or
  VCVio (grep-enforced).
- `README.md` gained a `VCV-io integration` section with the
  `SignatureAlg` snippet and links to the plan + roadmap docs.

**Acceptance:** both `build` (~2.5 min) and `vcvio-build` (~12 min cold,
Mathlib cache-hit warm) jobs green on every push.

---

## Cross-cutting acceptance: at every milestone

- No `sorry`/`partial`/`unsafe`/`extern` (CI grep).
- Core `LeanCrypto/**.lean` does not import Mathlib or VCV-io (CI grep).
- VCV-io pin is a specific commit SHA in `lake-manifest.json`, never `master`.
- Each PR references its milestone ID (`M12`, …) and cites the PLAN section
  it implements.
- If a milestone's plan needs to change mid-stream, update
  `docs/VCV_IO_PLAN.md` in the **same PR** and call out the change.
