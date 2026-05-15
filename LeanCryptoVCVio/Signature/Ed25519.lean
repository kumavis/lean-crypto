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

end LeanCryptoVCVio
