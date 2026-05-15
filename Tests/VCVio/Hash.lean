import LeanCryptoVCVio

open LeanCrypto.Hash.SHA256 (sha256)
open LeanCrypto.Hash.SHA512 (sha512)
open LeanCryptoVCVio

/-! M14 acceptance: deterministic adapters round-trip through `simulateQ`.

Builds a handful of `ByteArray` inputs at lengths that span every SHA-256 /
SHA-512 block-boundary case, runs each through the OracleComp lift composed
with `simulateQ` over the empty spec, and asserts the result byte-equals the
pure implementation. Any discrepancy aborts with a non-zero exit code. -/

/-- Lengths covering both SHA-256 (64-byte block, length field at 56) and
SHA-512 (128-byte block, length field at 112). -/
def lengths : List Nat :=
  [0, 1, 7, 31, 32, 55, 56, 63, 64, 65, 111, 112, 127, 128, 129, 200, 1023]

/-- Deterministic pattern fill, so the test is reproducible across runs. -/
def patternBytes (n : Nat) : ByteArray :=
  let arr := Array.range n |>.map (fun i => UInt8.ofNat ((i * 17 + 13) % 256))
  ⟨arr⟩

structure CaseResult where
  algo : String
  len  : Nat
  ok   : Bool
  deriving Repr

def runCase (algo : String) (msg : ByteArray)
    (oc : ByteArray → OracleComp ([]ₒ) ByteArray) (pure_ : ByteArray → ByteArray) :
    CaseResult :=
  let got := simulateQ emptyImpl (oc msg) |>.run
  let want := pure_ msg
  { algo, len := msg.size, ok := got = want }

def main : IO UInt32 := do
  let mut results : Array CaseResult := #[]
  for n in lengths do
    let msg := patternBytes n
    results := results.push (runCase "sha256" msg sha256OC sha256)
    results := results.push (runCase "sha512" msg sha512OC sha512)
  let failures : Array CaseResult := results.filter (fun r => !r.ok)
  if failures.isEmpty then
    let n := results.size
    IO.println ("OK " ++ toString n ++
      " vectors (simulateQ ∘ shaXOC matches LeanCrypto.shaX)")
    return 0
  else
    for r in failures do
      IO.eprintln ("FAIL " ++ r.algo ++ " len=" ++ toString r.len)
    return 1
