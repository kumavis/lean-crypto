import LeanCryptoVCVio.Prelude

/-!
# SHA-512 deterministic adapter

Lifts `LeanCrypto.sha512 : ByteArray → ByteArray` into `OracleComp` as a
deterministic computation. Polymorphic in the oracle spec.
-/

namespace LeanCryptoVCVio

open LeanCrypto.Hash.SHA512 (sha512)

/-- Lift `LeanCrypto.Hash.SHA512.sha512` into `OracleComp` as a deterministic
computation. -/
@[reducible] def sha512OC {ι : Type} {spec : OracleSpec ι} (msg : ByteArray) :
    OracleComp spec ByteArray :=
  pure (sha512 msg)

@[simp] lemma simulateQ_sha512OC {ι : Type} {spec : OracleSpec ι}
    {m : Type → Type _} [Monad m] (impl : QueryImpl spec m) (msg : ByteArray) :
    simulateQ impl (sha512OC (spec := spec) msg) = pure (sha512 msg) := rfl

end LeanCryptoVCVio
