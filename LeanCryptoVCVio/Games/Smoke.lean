import LeanCryptoVCVio.Prelude
import LeanCryptoVCVio.Signature.Ed25519

/-!
# UF-CMA smoke wiring for `ed25519`

Validates that the `SignatureAlg` instance built in M15 plugs into VCV-io's
`unforgeableAdv` / `unforgeableExp` infrastructure. No security claim is
made — this is shape verification only.

We also expose a concrete `smokeGame : ProbComp Bool` that mirrors the
inner experiment body but stays at the `OracleComp` level (the
`unforgeableExp` wrapper jumps to `SPMF Bool` via `evalDist`, which is
noncomputable). The runtime test under `Tests/VCVio/GameSmoke.lean`
drives `smokeGame` through `simulateQ` and asserts the trivial adversary
never wins.
-/

namespace LeanCryptoVCVio

/-- A trivial UF-CMA adversary against `ed25519`: ignores the public key,
makes no signing-oracle queries, and returns an empty `(msg, sig)` pair.
Used to wire `unforgeableExp` for shape verification only. -/
def trivialAdv : SignatureAlg.unforgeableAdv ed25519 where
  main := fun _pk => pure (ByteArray.empty, ByteArray.empty)

/-- Concrete runtime smoke: the inner body of `unforgeableExp ed25519 trivialAdv`
expressed as a `ProbComp Bool`. Always returns `false` for the trivial
adversary (verify rejects an empty 0-byte signature). -/
def smokeGame : ProbComp Bool := do
  let (pk, _sk) ← ed25519.keygen
  -- Trivial adversary returns (ε, ε); no signing queries means the log is empty.
  let msg : ByteArray := ByteArray.empty
  let σ   : ByteArray := ByteArray.empty
  let verified ← ed25519.verify pk msg σ
  -- `!log.wasQueried msg && verified`, with `log` empty → `!false && verified = verified`.
  return verified

end LeanCryptoVCVio
