import VCVio.OracleComp.SimSemantics.SimulateQ
import LeanCrypto

/-!
# VCV-io wrapper — prelude

Shared imports and namespace setup for the `LeanCryptoVCVio` library.
Brings `LeanCrypto` (our pure-functional implementation) into scope alongside
the slice of VCV-io that the wrapper currently uses:

* `OracleSpec`, `OracleComp` — the free-monad framework.
* `QueryImpl`, `simulateQ` — needed to interpret the deterministic
  adapters back to their pure values for testing.

The import surface widens further in later milestones:

* M15: adds `VCVio.CryptoFoundations.SignatureAlg` for the
  `SignatureAlg` instance.
* M16: adds `VCVio.OracleComp.QueryTracking.RandomOracle` for the
  SHA-512-as-RandomOracle variant.
-/

namespace LeanCryptoVCVio

/-- Vacuous `QueryImpl` for the empty oracle spec: there is no query to
implement because the spec's domain is `PEmpty`. Used as the trivial
interpreter when running the deterministic adapters under `simulateQ`. -/
@[reducible] def emptyImpl : QueryImpl []ₒ Id := fun x => x.elim

end LeanCryptoVCVio
