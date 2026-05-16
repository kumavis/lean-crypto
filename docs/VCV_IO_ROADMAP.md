# `lean-crypto` — VCV-io wrapper roadmap

Seven milestones from "4.27 with no Mathlib" to "Ed25519 plugged into VCV-io's
`SignatureAlg` and UF-CMA scaffolding, CI-green." Each milestone is one PR.

See `docs/VCV_IO_PLAN.md` for the design.

---

## M12 · Toolchain bump to Lean 4.28.0 — small

**Goal.** Existing code compiles and every test passes on Lean 4.28.0. No
new features, no new deps.

**Deliverables.**
- `lean-toolchain` → `leanprover/lean4:v4.28.0`.
- Fix any compile errors surfaced by the bump.
- All M1–M11 deliverables continue to pass.

**Acceptance.**
- `lake build` succeeds on a clean checkout against 4.28.0.
- Every existing test exe exits 0.
- Differential fuzz (`tests/diff/run.sh`) still passes.
- CI green.

---

## M13 · Lakefile + dependencies — small

**Goal.** Mathlib and VCV-io are wired into the lakefile. Empty
`LeanCryptoVCVio` library builds. No symbols added yet beyond a stub.

**Deliverables.**
- `lakefile.lean`:
  - `require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"`.
  - `require VCVio from git "https://github.com/dtumad/VCV-io" @ "<pin>"`.
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

**Deliverables.**
- `LeanCryptoVCVio/Hash/SHA256.lean` — `sha256OC : ByteArray → OracleComp []ₒ ByteArray`.
- `LeanCryptoVCVio/Hash/SHA512.lean` — `sha512OC`.
- Adapter-style lifts of `derivePublicKey`, `sign`, `verify`, `verifyZip215`
  in `LeanCryptoVCVio/Signature/Ed25519.lean` (just the lifts; `SignatureAlg`
  instance lands in M15).
- `Tests/VCVio/Hash.lean` — 20 random messages each for SHA-256 and SHA-512;
  assert `simulateQ idImpl (sha256OC m) = sha256 m`.

**Acceptance.**
- `Tests/VCVio/Hash` exits 0.
- All 40 cases (20 × 2 algos) match byte-exactly.

---

## M15 · Phase B.1 — `SignatureAlg` instance + `PerfectlyComplete` — medium

**Goal.** Ed25519 is a `SignatureAlg (OracleComp unifSpec) …`. RFC 8032
vector 1 round-trips through it. `PerfectlyComplete` proof goes through (or
falls back to per-vector `decide`).

**Deliverables.**
- `LeanCryptoVCVio/Signature/Ed25519.lean`:
  - `def ed25519 : SignatureAlg (OracleComp unifSpec) …` as in PLAN §5.
  - `instance : PerfectlyComplete ed25519` — proved via
    `Ed25519.verify_sign_self` lemma (see below).
- **Core addition:** `LeanCrypto/Signature/Ed25519.lean` grows
  `theorem verify_sign_self (sk msg : ByteArray) (hsk : sk.size = 32) :
    verify (derivePublicKey sk) (sign sk msg) msg = true`.
  - If the universal proof is harder than budgeted (>1 day), fall back to
    `decide`-able instances for the 4 RFC 8032 vectors and document the
    weaker completeness statement in the wrapper.
- `Tests/VCVio/Ed25519Det.lean`:
  - Fixed-seed `QueryImpl` that yields RFC 8032 §7.1 vector 1's `sk`.
  - Run `keygen`/`sign`/`verify` through `simulateQ` with that impl.
  - Assert byte-equality with the published `pk` and `sig`.

**Acceptance.**
- `Tests/VCVio/Ed25519Det` exits 0.
- `PerfectlyComplete ed25519` typechecks (or, if fallback engaged, the
  decidable variant typechecks and the docstring calls out the weakening).
- Wrapper builds with no `sorry`/`partial`/`unsafe`/`extern`.

**Concurrent check.** `verify_sign_self`'s proof difficulty becomes the
schedule risk for the whole roadmap. If by mid-M15 the universal proof is
clearly multi-day, take the fallback in the same PR rather than spilling.

---

## M16 · Phase B.2 — SHA-512 as RandomOracle — medium

**Goal.** A second `SignatureAlg` instance where SHA-512 is queried as an
abstract random oracle instead of computed via `LeanCrypto.sha512`.

**Deliverables.**
- `LeanCryptoVCVio/Signature/Ed25519ROM.lean`:
  - `def sha512ROSpec : OracleSpec Unit := fun _ => ByteArray`.
  - `def ed25519ROM : SignatureAlg (OracleComp sha512ROSpec) …` mirroring
    `ed25519` but routing every internal hash call through `query () _`.
- `instance : PerfectlyComplete ed25519ROM` — proved by reduction to
  `ed25519` under the "instantiate the oracle with `sha512`" `QueryImpl`.

**Acceptance.**
- `Tests/VCVio/Ed25519ROM`: instantiate the random oracle with the real
  `sha512` via `QueryImpl`; assert `simulateQ` of `keygen → sign → verify`
  yields `true` for RFC vector 1.
- `PerfectlyComplete ed25519ROM` typechecks.

---

## M17 · Phase B.3 — UF-CMA smoke game — small

**Goal.** VCV-io's `unforgeableExp` runs end-to-end against `ed25519` with a
trivial adversary. Sanity-check that the wrapper plugs into VCV-io's game
infrastructure.

**Deliverables.**
- `LeanCryptoVCVio/Games/Smoke.lean` — `trivialAdv : unforgeableAdv ed25519`
  that returns `(msg, garbage_sig)` without ever querying the signing oracle.
- `Tests/VCVio/GameSmoke.lean` — runs `unforgeableExp ed25519 trivialAdv`
  via `simulateQ` and asserts the result is `false` (trivial adv never wins).

**Acceptance.**
- `Tests/VCVio/GameSmoke` exits 0.
- No security claims made; this is shape-validation only.

---

## M18 · CI job + README — small

**Goal.** Wrapper builds and tests run on every push. README documents what
the wrapper is for.

**Deliverables.**
- `.github/workflows/ci.yml` extended with a `vcvio-build` job:
  - `lake exe cache get` for Mathlib oleans.
  - `lake build LeanCryptoVCVio`.
  - Run every `Tests-VCVio-*` exe.
  - Forbidden-tokens grep extended to `LeanCryptoVCVio/` and `Tests/VCVio/`.
- `README.md` gains a `VCV-io integration` section linking to
  `docs/VCV_IO_PLAN.md` and showing the `SignatureAlg` snippet from §5.

**Acceptance.**
- GitHub Actions `vcvio-build` job is green.
- Existing `build` job is unchanged and still green.

---

## Cross-cutting acceptance: at every milestone

- No `sorry`/`partial`/`unsafe`/`extern` (CI grep).
- Core `LeanCrypto/**.lean` does not import Mathlib or VCV-io (CI grep).
- VCV-io pin is a specific commit SHA in `lake-manifest.json`, never `master`.
- Each PR references its milestone ID (`M12`, …) and cites the PLAN section
  it implements.
- If a milestone's plan needs to change mid-stream, update
  `docs/VCV_IO_PLAN.md` in the **same PR** and call out the change.
