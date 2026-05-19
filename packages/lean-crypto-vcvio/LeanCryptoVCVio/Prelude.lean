import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.SignatureAlg
import LeanCrypto

/-!
# VCV-io wrapper — prelude

Shared imports and namespace setup for the `LeanCryptoVCVio` library.
Brings `LeanCrypto` (our pure-functional implementation) into scope alongside
the slice of VCV-io that the wrapper currently uses:

* `OracleSpec`, `OracleComp` — the free-monad framework.
* `QueryImpl`, `simulateQ` — needed to interpret the deterministic
  adapters back to their pure values for testing.
* `SampleableType`, `$ᵗ` — uniform sampling for `keygen` randomness.
* `SignatureAlg` — VCV-io's signature-scheme abstraction.

The import surface widens further in later milestones:

* M16: adds `VCVio.OracleComp.QueryTracking.RandomOracle` for the
  SHA-512-as-RandomOracle variant.
-/

namespace LeanCryptoVCVio

/-- Vacuous `QueryImpl` for the empty oracle spec: there is no query to
implement because the spec's domain is `PEmpty`. Used as the trivial
interpreter when running the deterministic adapters under `simulateQ`. -/
@[reducible] def emptyImpl : QueryImpl []ₒ Id := fun x => x.elim

/-- `QueryImpl unifSpec Id` that returns 0 for every uniform query. Lets us
evaluate deterministic `ProbComp` computations whose downstream value does
not depend on the sampled randomness — e.g. running `sign` / `verify`
through `simulateQ` when the result is already pinned. -/
@[reducible] def constUnifImpl : QueryImpl unifSpec Id := fun _ => pure 0

/-- Sample `n` uniformly random bytes as a `ByteArray` under `ProbComp`. -/
def drawBytes (n : Nat) : ProbComp ByteArray := do
  let bs ← (List.range n).mapM (fun _ : Nat => $ᵗ UInt8)
  return ⟨bs.toArray⟩

end LeanCryptoVCVio
