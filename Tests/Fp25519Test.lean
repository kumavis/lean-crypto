import LeanCrypto.Field.Fp25519

open LeanCrypto.Field.Fp25519

/-! M6 test runner for `LeanCrypto.Field.Fp25519`. -/

abbrev TestM := StateM (Nat × Option String)

def ok : TestM Unit := modify fun (n, e) => (n + 1, e)

def fail (msg : String) : TestM Unit :=
  modify fun (n, e) => (n, e.orElse (fun () => some msg))

def checkEq [BEq α] [ToString α] (name : String) (expected actual : α) : TestM Unit :=
  if expected == actual then ok
  else fail s!"{name}: expected {expected}, got {actual}"

def tests : TestM Unit := do
  -- p = 2^255 - 19
  checkEq "p" (2^255 - 19) p

  -- Boundary arithmetic
  checkEq "(p-1) + 1 = 0" 0 (add (p - 1) 1)
  checkEq "0 - 1 = p-1" (p - 1) (sub 0 1)
  checkEq "neg 0 = 0" 0 (neg 0)
  checkEq "neg 1 = p-1" (p - 1) (neg 1)
  checkEq "mul 0 _" 0 (mul 0 12345)
  checkEq "mul 1 a" 12345 (mul 1 12345)
  checkEq "mul (p-1) (p-1) = 1" 1 (mul (p - 1) (p - 1))

  -- pow: small cases
  checkEq "pow 2 0 = 1"   1 (pow 2 0)
  checkEq "pow 2 1 = 2"   2 (pow 2 1)
  checkEq "pow 2 10"    1024 (pow 2 10)
  checkEq "pow a 1 = a" 42 (pow 42 1)

  -- Fermat: pow a (p-1) = 1 for nonzero a
  for a in [1, 2, 3, 7, 0xdeadbeef, p - 1] do
    checkEq s!"Fermat pow {a} (p-1)" 1 (pow a (p - 1))

  -- inv: round-trip a * inv a = 1
  for a in [1, 2, 3, 7, 0xdeadbeef, 0x1234567890abcdef, p - 1] do
    let inv_a := inv a
    checkEq s!"a * inv a = 1, a={a}" 1 (mul a inv_a)

  -- sqrt: for QRs, (sqrt a)^2 = a; sqrtM1^2 = p - 1
  checkEq "sqrtM1^2 = p-1" (p - 1) (square sqrtM1)

  -- (a^2) is a QR with sqrt either a or -a
  for a in [2, 3, 7, 0xdeadbeef] do
    let asq := square a
    match sqrt asq with
    | none => fail s!"sqrt of square {a} returned none"
    | some r =>
        if square r != asq then
          fail s!"sqrt({a}^2)^2 != {a}^2"
        else
          ok

  -- Non-residue: sqrt should return none
  -- 2 is a non-residue mod p (well-known for Curve25519). Verify.
  match sqrt 2 with
  | none => ok
  | some _ => fail "sqrt 2 should return none"

  -- (p-1) is a QR with sqrt = sqrtM1
  match sqrt (p - 1) with
  | none => fail "sqrt (p-1) returned none"
  | some r => checkEq "sqrt(p-1)^2 = p-1" (p - 1) (square r)

def main : IO UInt32 := do
  let ((), (n, err)) := tests.run (0, none)
  match err with
  | some msg => IO.eprintln s!"FAIL {msg} (after {n} passing)"; return 1
  | none => IO.println s!"OK {n} vectors"; return 0
