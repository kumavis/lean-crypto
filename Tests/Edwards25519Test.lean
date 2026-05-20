import LeanCrypto.Bytes
import LeanCrypto.Field.Fp25519
import LeanCrypto.Field.ScalarL
import LeanCrypto.Curve.Edwards25519

open LeanCrypto.Bytes
open LeanCrypto.Field.Fp25519
open LeanCrypto.Field.ScalarL (L)
open LeanCrypto.Curve.Edwards25519
open LeanCrypto.Curve.Edwards25519.EdPoint

/-! M8 test runner: edwards25519 point operations. -/

abbrev TestM := StateM (Nat × Option String)

def ok : TestM Unit := modify fun (n, e) => (n + 1, e)

def fail (msg : String) : TestM Unit :=
  modify fun (n, e) => (n, e.orElse (fun () => some msg))

def checkEq [BEq α] [ToString α] (name : String) (expected actual : α) : TestM Unit :=
  if expected == actual then ok
  else fail s!"{name}: expected {expected}, got {actual}"

/-- Two extended-coordinate points are equal as group elements iff their
toAffine projections agree. -/
def affineEq (p q : EdPoint) : Bool :=
  let pa := toAffine p
  let qa := toAffine q
  pa.x == qa.x && pa.y == qa.y

/-- Canonical encoding of the base point — `y = 0x666…58` little-endian
with sign-of-x = 0 in the high bit of byte 31. Well-known constant from
RFC 8032. -/
def baseEncoded : String :=
  "5866666666666666666666666666666666666666666666666666666666666666"

def tests : TestM Unit := do
  -- B + B = 2·B via add vs double
  let twoB_add := add basePoint basePoint
  let twoB_dbl := double basePoint
  if !affineEq twoB_add twoB_dbl then
    fail "B+B (via add) disagrees with 2·B (via double)"
  else ok

  -- Identity behaves as identity
  let bPlusZero := add basePoint identity
  if !affineEq bPlusZero basePoint then
    fail "B + identity != B"
  else ok
  let zeroDouble := double identity
  if !affineEq zeroDouble identity then
    fail "2 · identity != identity"
  else ok

  -- B + (-B) = identity
  let negB := negate basePoint
  let bMinusB := add basePoint negB
  if !affineEq bMinusB identity then
    fail "B + (-B) != identity"
  else ok

  -- smul small-scalar cases vs. iterated add
  let oneB := smul 1 basePoint
  if !affineEq oneB basePoint then fail "smul 1 basePoint != basePoint" else ok
  let zeroB := smul 0 basePoint
  if !affineEq zeroB identity then fail "smul 0 basePoint != identity" else ok
  let threeB_smul := smul 3 basePoint
  let threeB_iter := add (double basePoint) basePoint
  if !affineEq threeB_smul threeB_iter then
    fail "smul 3 basePoint disagrees with 2B + B"
  else ok

  -- Canonical base-point encoding
  checkEq "encode(B)" baseEncoded (bytesToHex (encode basePoint))

  -- decode∘encode = identity (group-element-equality) for a handful of
  -- points spanning small, medium, and large scalars
  for n in [1, 2, 3, 7, 8, 100, 12345, 0xdeadbeef] do
    let pt := smul n basePoint
    let enc := encode pt
    match decode enc with
    | none => fail s!"decode failed for {n}·B"
    | some pt' =>
        if !affineEq pt pt' then
          fail s!"decode∘encode mismatch for {n}·B"
        else
          ok

  -- Distributivity-style sanity: smul (a+b) B = (smul a B) + (smul b B)
  for (a, b) in ([(3, 5), (100, 7), (12345, 67890)] : List (Nat × Nat)) do
    let lhs := smul (a + b) basePoint
    let rhs := add (smul a basePoint) (smul b basePoint)
    if !affineEq lhs rhs then
      fail s!"smul ({a}+{b}) != smul {a} + smul {b}"
    else ok

  -- Doubling consistency: smul 2 B = double B
  let twoB_smul := smul 2 basePoint
  let twoB_dbl  := double basePoint
  if !affineEq twoB_smul twoB_dbl then
    fail "smul 2 B != double B"
  else ok

  -- ℓ · B = identity (large; ~256 doubles + many adds)
  let ellB := smul L basePoint
  if !affineEq ellB identity then
    fail "ℓ · B != identity"
  else ok

def main : IO UInt32 := do
  let ((), (n, err)) := tests.run (0, none)
  match err with
  | some msg => IO.eprintln s!"FAIL {msg} (after {n} passing)"; return 1
  | none => IO.println s!"OK {n} vectors"; return 0
