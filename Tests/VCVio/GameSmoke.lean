import LeanCryptoVCVio

open LeanCryptoVCVio

/-! M17 acceptance: the trivial UF-CMA adversary against `ed25519`
never wins.

`trivialAdv` returns `(ε, ε)` (empty message, empty signature) ignoring
the public key. `ed25519.verify pk ε ε` rejects (length != 64), so the
experiment body evaluates to `false` for every keygen-sampled (pk, sk).

We run the smokeGame's inner `ProbComp Bool` body through `simulateQ`
with `constUnifImpl` (returns 0 to every uniform query) — a fixed
seed for keygen — and confirm the result is `false`.

No security claim is made by this test; it's a shape check that the
SignatureAlg instance plugs into VCV-io's UF-CMA scaffolding. -/

def main : IO UInt32 := do
  let result : Bool := simulateQ constUnifImpl smokeGame |>.run
  if result = false then
    IO.println "OK 1 vector (trivial UF-CMA adversary loses against ed25519)"
    return 0
  else
    IO.eprintln "FAIL trivial adversary accidentally won (verify returned true on empty sig)"
    return 1
