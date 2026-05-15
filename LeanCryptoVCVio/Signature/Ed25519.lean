import LeanCryptoVCVio.Prelude

/-!
# Ed25519 deterministic adapters

Lifts `LeanCrypto.Signature.Ed25519`'s pure operations into `OracleComp` as
deterministic computations. The `SignatureAlg` instance with a real
randomness source for keygen lands in M15; these adapters are
spec-polymorphic so they can sit inside any larger oracle program.
-/

namespace LeanCryptoVCVio

open LeanCrypto.Signature.Ed25519 (derivePublicKey sign verify verifyZip215)

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type _} [Monad m]

/-- `derivePublicKey` lifted to `OracleComp`. -/
@[reducible] def derivePublicKeyOC (sk : ByteArray) : OracleComp spec ByteArray :=
  pure (derivePublicKey sk)

@[simp] lemma simulateQ_derivePublicKeyOC (impl : QueryImpl spec m) (sk : ByteArray) :
    simulateQ impl (derivePublicKeyOC (spec := spec) sk) = pure (derivePublicKey sk) := rfl

/-- `sign` lifted to `OracleComp`. -/
@[reducible] def signOC (sk msg : ByteArray) : OracleComp spec ByteArray :=
  pure (sign sk msg)

@[simp] lemma simulateQ_signOC (impl : QueryImpl spec m) (sk msg : ByteArray) :
    simulateQ impl (signOC (spec := spec) sk msg) = pure (sign sk msg) := rfl

/-- `verify` lifted to `OracleComp`. -/
@[reducible] def verifyOC (pk sig msg : ByteArray) : OracleComp spec Bool :=
  pure (verify pk sig msg)

@[simp] lemma simulateQ_verifyOC (impl : QueryImpl spec m) (pk sig msg : ByteArray) :
    simulateQ impl (verifyOC (spec := spec) pk sig msg) = pure (verify pk sig msg) := rfl

/-- `verifyZip215` lifted to `OracleComp`. -/
@[reducible] def verifyZip215OC (pk sig msg : ByteArray) : OracleComp spec Bool :=
  pure (verifyZip215 pk sig msg)

@[simp] lemma simulateQ_verifyZip215OC (impl : QueryImpl spec m)
    (pk sig msg : ByteArray) :
    simulateQ impl (verifyZip215OC (spec := spec) pk sig msg)
      = pure (verifyZip215 pk sig msg) := rfl

/-! ### Ed25519 as a `SignatureAlg` over `ProbComp`

`keygen` draws 32 uniformly random bytes for the seed via `drawBytes` and
returns `(derivePublicKey sk, sk)`. `sign` and `verify` are deterministic
lifts. The full PRF-style construction lives in the underlying `LeanCrypto`
implementation; here we expose it through VCV-io's signature-scheme
abstraction so that the result type plugs into `unforgeableExp` and friends.

`PerfectlyComplete ed25519` is **not** asserted yet: discharging it would
require a `verify_sign_self` theorem about our Ed25519 implementation
(`verify (derivePublicKey sk) (sign sk msg) msg = true` for every 32-byte
seed and arbitrary message), which is the algebraic-correctness proof
of the scheme itself — multi-day Mathlib-level work, beyond M15's scope.
The runtime tests under `Tests/VCVio/Ed25519Det.lean` verify completeness
on the RFC 8032 §7.1 vectors instead. -/

/-- Ed25519 packaged as a `SignatureAlg` in the `ProbComp` monad. Strict
RFC 8032 verification (no ZIP-215 lenience). -/
def ed25519 : SignatureAlg ProbComp ByteArray ByteArray ByteArray ByteArray where
  keygen := do
    let sk ← drawBytes 32
    return (derivePublicKey sk, sk)
  sign _pk sk msg := pure (sign sk msg)
  verify pk msg σ := pure (verify pk σ msg)

@[simp] lemma ed25519_sign (pk sk msg : ByteArray) :
    ed25519.sign pk sk msg = pure (sign sk msg) := rfl

@[simp] lemma ed25519_verify (pk msg σ : ByteArray) :
    ed25519.verify pk msg σ = pure (verify pk σ msg) := rfl

/-- ZIP-215-lenient variant of `ed25519`. Same `keygen`/`sign`; `verify`
routes through `verifyZip215`. -/
def ed25519Zip215 :
    SignatureAlg ProbComp ByteArray ByteArray ByteArray ByteArray where
  keygen := do
    let sk ← drawBytes 32
    return (derivePublicKey sk, sk)
  sign _pk sk msg := pure (sign sk msg)
  verify pk msg σ := pure (verifyZip215 pk σ msg)

@[simp] lemma ed25519Zip215_sign (pk sk msg : ByteArray) :
    ed25519Zip215.sign pk sk msg = pure (sign sk msg) := rfl

@[simp] lemma ed25519Zip215_verify (pk msg σ : ByteArray) :
    ed25519Zip215.verify pk msg σ = pure (verifyZip215 pk σ msg) := rfl

end LeanCryptoVCVio
