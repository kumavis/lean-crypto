import LeanCrypto.Bytes
import LeanCrypto.Field.ScalarL

open LeanCrypto.Bytes
open LeanCrypto.Field.ScalarL

/-! M7 test runner for `LeanCrypto.Field.ScalarL`. -/

abbrev TestM := StateM (Nat × Option String)

def ok : TestM Unit := modify fun (n, e) => (n + 1, e)

def fail (msg : String) : TestM Unit :=
  modify fun (n, e) => (n, e.orElse (fun () => some msg))

def checkEq [BEq α] [ToString α] (name : String) (expected actual : α) : TestM Unit :=
  if expected == actual then ok
  else fail s!"{name}: expected {expected}, got {actual}"

def tests : TestM Unit := do
  -- Reference value for ℓ (RFC 8032 / Ed25519 spec).
  checkEq "L"
    (2^252 + 27742317777372353535851937790883648493) L

  -- Boundary arithmetic
  checkEq "(L-1) + 1 = 0" 0 (add (L - 1) 1)
  checkEq "0 - 1 = L-1" (L - 1) (sub 0 1)
  checkEq "mul 0 _" 0 (mul 0 12345)
  checkEq "mul 1 a" 12345 (mul 1 12345)
  checkEq "L mod L = 0" 0 (reduce L)
  checkEq "(L-1) mod L" (L - 1) (reduce (L - 1))

  -- reduce512Bit: 0 → 0
  let zeros := ByteArray.mk (Array.replicate 64 (0 : UInt8))
  checkEq "reduce512Bit zero" 0 (reduce512Bit zeros)

  -- reduce512Bit: 1 → 1 (low byte = 1, rest zero, LE)
  let one := zeros.set! 0 1
  checkEq "reduce512Bit one" 1 (reduce512Bit one)

  -- reduce512Bit: all-0xff (64 bytes) = 2^512 - 1; reduce to (2^512 - 1) mod L.
  -- Sanity: the result must be < L.
  let allff := ByteArray.mk (Array.replicate 64 (0xff : UInt8))
  let r := reduce512Bit allff
  if r >= L then fail s!"reduce512Bit allff: result {r} ≥ L"
  else ok
  -- And it must agree with the direct Nat computation.
  checkEq "reduce512Bit allff value" ((2^512 - 1) % L) (reduce512Bit allff)

def main : IO UInt32 := do
  let ((), (n, err)) := tests.run (0, none)
  match err with
  | some msg => IO.eprintln s!"FAIL {msg} (after {n} passing)"; return 1
  | none => IO.println s!"OK {n} vectors"; return 0
