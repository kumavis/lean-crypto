# lean-crypto

Pure Lean 4 implementation of **SHA-256**, **SHA-512**, and **Ed25519**,
validated bit-for-bit against the [`noble-hashes`](https://github.com/paulmillr/noble-hashes)
and [`noble-ed25519`](https://github.com/paulmillr/noble-ed25519) references
and the standard test suites — FIPS 180-4 / NIST CAVP, RFC 8032 §7.1,
and Project Wycheproof (`testvectors_v1/ed25519_test.json`).

* **Status:** v1 complete (M1–M11). Optional VCV-io wrapper layered on top (M12–M18).
* **Toolchain:** pinned to `leanprover/lean4:v4.29.0`.
* **Core dependencies:** none — no Mathlib, no std4/batteries, no FFI.
* **Wrapper dependencies (opt-in):** Mathlib 4.29.0 + VCV-io 4.29.0, used only
  by the separate `LeanCryptoVCVio` library.

See [`docs/PLAN.md`](docs/PLAN.md) and [`docs/ROADMAP.md`](docs/ROADMAP.md)
for the core design, and
[`docs/VCV_IO_PLAN.md`](docs/VCV_IO_PLAN.md) /
[`docs/VCV_IO_ROADMAP.md`](docs/VCV_IO_ROADMAP.md) for the VCV-io wrapper.

## What's in the box

| Primitive  | Public API                                                        | Validation                                          |
|------------|-------------------------------------------------------------------|-----------------------------------------------------|
| SHA-256    | `sha256`, `Sha256Ctx.init/update/finalize`                        | NIST CAVP: short, long, Monte (615 cases)           |
| SHA-512    | `sha512`, `Sha512Ctx.init/update/finalize`                        | NIST CAVP: short, long, Monte (1127 cases)          |
| Ed25519    | `Ed25519.derivePublicKey`, `sign`, `verify`, `verifyZip215`       | RFC 8032 §7.1 (4 vectors), Wycheproof (150 cases × 2 modes) |

Every entry point is total — `ByteArray → ByteArray` (and `Bool` for
verify) — with no `IO`, no `partial`, no `sorry`, no `unsafe`, no `extern`,
no FFI. CI enforces those bans at build time.

`verify` is **strict RFC 8032 §5.1.7**: rejects `S ≥ ℓ`, non-canonical
`R` or `pk` encodings (`y ≥ p`), and small-order public keys. Uses the
cofactored equation `[8](S·B) = [8](R + k·A)`.

`verifyZip215` is the [ZIP-215](https://zips.z.cash/zip-0215) variant,
matching `noble-ed25519`'s default: still requires `S < ℓ` and uses the
same cofactored equation, but reduces `y` mod `p` (accepting non-canonical
encodings) and does not reject small-order public keys.

## Usage

```lean
import LeanCrypto

open LeanCrypto.Bytes
open LeanCrypto.Hash.SHA256
open LeanCrypto.Signature.Ed25519

-- Hashing (one-shot)
#eval bytesToHex (sha256 "abc".toUTF8)
-- ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad

-- Hashing (streaming)
let ctx := (Sha256Ctx.init.update "ab".toUTF8).update "c".toUTF8
#eval bytesToHex ctx.finalize
-- ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad

-- Ed25519 sign / verify
let sk := -- 32-byte ByteArray
let msg := "hello".toUTF8
let pk := Ed25519.derivePublicKey sk
let sig := Ed25519.sign sk msg
#eval Ed25519.verify pk sig msg     -- true
```

## Building

```sh
# One-time: install elan (Lean toolchain manager)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Build (downloads the pinned toolchain on first run)
lake build

# Run every test executable
for exe in .lake/build/bin/*; do
  [ -x "$exe" ] && [ -f "$exe" ] && "$exe" || true
done
```

The CI workflow in `.github/workflows/ci.yml` does the same.

## Performance and limitations

v1 is **correctness-first**. All field arithmetic is `Nat`-backed; modular
inverse is Fermat (`a^(p-2) mod p`); scalar multiplication is left-to-right
double-and-add. On a modern laptop the full test suite (over 2,000 vectors
including 100,000 Monte Carlo SHA hashes and `ℓ·B = identity`) completes
in **under five seconds**. A single Ed25519 sign + verify is on the order
of tens of milliseconds. SHA-256/-512 on small inputs is microseconds.

Future optimisation passes (limb-representation field arithmetic,
wNAF scalar mult, precomputed base-point tables) would move Ed25519
sub-millisecond, but they are deliberately deferred until correctness
is proven.

## Known timing leaks (out of scope for v1)

* `EdPoint.smul` (double-and-add) branches on each bit of the scalar.
  This **leaks the secret scalar** via timing on the sign path and the
  per-message ephemeral `r`.
* `ScalarL.reduce` calls `Nat.mod`, which is not constant-time. Inputs
  are SHA-512 outputs so the relevant secret is the per-message `r`.
* `Fp25519.sqrt` branches on which candidate root is valid. Inputs are
  public (decode-time `y`), so this is not a secret-key leak.
* `Fp25519.inv` is Fermat (a fixed addition chain) — safe.

Fixing these requires constant-time field-arithmetic primitives Lean 4
does not currently expose; see `docs/PLAN.md` §8 for the follow-on plan.

## Reproducible test vectors

| Source     | Path                                                |
|------------|-----------------------------------------------------|
| NIST CAVP  | `tests/vectors/sha256/` and `tests/vectors/sha512/` |
| RFC 8032   | `tests/vectors/rfc8032/test1024.msg.hex` + embedded short vectors |
| Wycheproof | `tests/vectors/wycheproof/ed25519_test.json` (see `SOURCE.md`) |

All vectors are committed in-repo. Refresh procedure for the Wycheproof
snapshot is documented in `tests/vectors/wycheproof/SOURCE.md`.

## VCV-io integration (optional)

A separate `LeanCryptoVCVio` library lifts the SHA-256/SHA-512/Ed25519
primitives into [VCV-io](https://github.com/dtumad/VCV-io)'s `OracleComp`
framework so they plug into game-based crypto proofs. The core
`LeanCrypto` library stays Mathlib-free; the wrapper takes Mathlib +
VCV-io as dependencies only inside its own `lean_lib` target.

```lean
import LeanCryptoVCVio

open LeanCryptoVCVio

-- Deterministic adapter (M14): pure SHA-512 lifted into OracleComp.
example (msg : ByteArray) :
    OracleComp ([]ₒ) ByteArray :=
  sha512OC msg

-- SignatureAlg instance for Ed25519 (M15): keygen samples 32 random
-- bytes via unifSpec; sign/verify route through LeanCrypto's pure ops.
#check (ed25519 : SignatureAlg ProbComp ByteArray ByteArray ByteArray ByteArray)

-- SHA-512 modeled as a random oracle (M16): every internal sha512 call
-- becomes a `query (spec := sha512ROSpec) bs`.
#check (signROM : ByteArray → ByteArray → OracleComp sha512ROSpec ByteArray)

-- UF-CMA shape wiring (M17): trivialAdv plugs into VCV-io's
-- unforgeableAdv / unforgeableExp without any proof work.
#check (trivialAdv : SignatureAlg.unforgeableAdv ed25519)
```

What the wrapper does *not* ship:

* No `UF-CMA` reduction. `unforgeableExp` is wired (M17) but no
  security theorem is stated against it.
* No `PerfectlyComplete` instance on `ed25519` or `ed25519ROM`. The
  proof depended on a universal
  `verify (derivePublicKey sk) (sign sk msg) msg = true` theorem — the
  algebraic-correctness theorem of the scheme itself, multi-month
  Mathlib-level work per the external survey, deferred indefinitely.
  See `docs/PROOFS_ROADMAP.md` for what *was* proven (per-RFC-vector
  `native_decide` theorems + foundations on the Edwards group law).
* No `lean_exe` driven game evaluation. `unforgeableExp` lives at the
  `SPMF Bool` level via the noncomputable `ProbCompRuntime.probComp`;
  the runtime smoke test (`Tests/VCVio/GameSmoke.lean`) drives a
  hand-built parallel game body through `simulateQ` instead.

## Proof track (`LeanCryptoProofs/`)

A third `lean_lib LeanCryptoProofs` carries the algebraic foundations
work (also depends on Mathlib; also opt-in). Highlights from M19–M24:

```lean
import LeanCryptoProofs

open LeanCrypto.Signature.Ed25519.Proofs

-- Genuine compile-time theorem (not a runtime check): RFC 8032 §7.1
-- vector 1's freshly-signed signature verifies under the strict
-- RFC 8032 verifier.
#check (verify_sign_self_rfc_1 :
    verify (derivePublicKey sk_1) (sign sk_1 msg_1) msg_1 = true)

-- Wrapper-level bundle: the SignatureAlg sign-then-verify pipeline
-- reduces to `pure true` on each (sk, msg) in `rfcVectors`.
open LeanCryptoVCVio.Ed25519Proofs in
#check ed25519_completes_on_rfc_vectors
```

Each `verify_sign_self_rfc_*` theorem is closed by `native_decide`,
which compiles the decidability check to native code and asserts the
result as a fresh per-theorem axiom (`_native_decide.ax_N`). The
trust base is `propext + Classical.choice + Quot.sound` plus three
`ofReduceBool`-derived axioms, audited in source via `#print axioms`.
Mathlib forbids `native_decide` via its style linter; we're outside
Mathlib so this is a documented trade-off, isolated to one module.

Also landed: `ProjEq` Setoid on `EdPoint`, `Fp25519 ↔ ZMod p` cast
lemmas, `add_comm` / `add_zero_*` / `add_negate_cancel` via `ring` /
`linear_combination`. `add_assoc` was probed and exceeds Lean's
current `grobner` heuristic budget — see `docs/PROOFS_ROADMAP.md` M24
for the post-mortem and the three possible paths if anyone ever
comes back to it.

CI runs the wrapper build + tests in a separate `vcvio-build` job that
restores Mathlib's precompiled olean cache via `lake exe cache get`.

```sh
# Build the wrapper and its tests locally (downloads Mathlib + VCV-io
# on first run; subsequent builds use cached oleans):
lake update
git -C .lake/packages/VCVio submodule update --init --depth 1
lake exe cache get
lake build LeanCryptoVCVio
for exe in .lake/build/bin/Tests-VCVio-*; do "$exe"; done
```
