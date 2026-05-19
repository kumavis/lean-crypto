import LeanCryptoVCVio.Prelude

/-!
# SHA-256 deterministic adapter

Lifts `LeanCrypto.sha256 : ByteArray → ByteArray` into `OracleComp` as a
deterministic computation. Polymorphic in the oracle spec so callers can
drop the adapter into any game program without having to combine specs.
-/

namespace LeanCryptoVCVio

open LeanCrypto.Hash.SHA256 (sha256)

/-- Lift `LeanCrypto.Hash.SHA256.sha256` into `OracleComp` as a deterministic
computation. -/
@[reducible] def sha256OC {ι : Type} {spec : OracleSpec ι} (msg : ByteArray) :
    OracleComp spec ByteArray :=
  pure (sha256 msg)

@[simp] lemma simulateQ_sha256OC {ι : Type} {spec : OracleSpec ι}
    {m : Type → Type _} [Monad m] (impl : QueryImpl spec m) (msg : ByteArray) :
    simulateQ impl (sha256OC (spec := spec) msg) = pure (sha256 msg) := rfl

end LeanCryptoVCVio
