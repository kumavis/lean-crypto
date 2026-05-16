import LeanCrypto.Bytes

open LeanCrypto.Bytes

/-! M2 test runner for `LeanCrypto.Bytes`.

Prints `OK <N> vectors` on success; on first failure prints
`FAIL <msg>` and exits 1. Uses the panicky `!` load variants throughout
so we don't fight proof obligations on freshly-built buffers. -/

abbrev TestM := StateM (Nat × Option String)

def ok : TestM Unit := modify fun (n, e) => (n + 1, e)

def fail (msg : String) : TestM Unit :=
  modify fun (n, e) => (n, e.orElse (fun () => some msg))

def checkEq [BEq α] [ToString α] (name : String) (expected actual : α) : TestM Unit :=
  if expected == actual then ok
  else fail s!"{name}: expected {expected}, got {actual}"

def mkBA (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

def tests : TestM Unit := do
  -- loadU32BE literal cases
  checkEq "loadU32BE 0x12345678"
    (0x12345678 : UInt32) (loadU32BE! (mkBA [0x12, 0x34, 0x56, 0x78]) 0)
  checkEq "loadU32BE all-ones"
    (0xffffffff : UInt32) (loadU32BE! (mkBA [0xff, 0xff, 0xff, 0xff]) 0)
  checkEq "loadU32BE one"
    (1 : UInt32) (loadU32BE! (mkBA [0x00, 0x00, 0x00, 0x01]) 0)
  checkEq "loadU32BE high-bit"
    (0x80000000 : UInt32) (loadU32BE! (mkBA [0x80, 0x00, 0x00, 0x00]) 0)
  checkEq "loadU32BE off=2"
    (0xdeadbeef : UInt32)
    (loadU32BE! (mkBA [0x00, 0x00, 0xde, 0xad, 0xbe, 0xef]) 2)

  -- storeU32BE size + round-trip
  for x in ([0, 1, 0xff, 0x12345678, 0xdeadbeef, 0xffffffff] : List UInt32) do
    let b := storeU32BE ByteArray.empty x
    checkEq s!"storeU32BE size {x}" 4 b.size
    checkEq s!"storeU32BE round-trip {x}" x (loadU32BE! b 0)

  -- loadU64BE literal
  checkEq "loadU64BE 0x0123456789abcdef"
    (0x0123456789abcdef : UInt64)
    (loadU64BE! (mkBA [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]) 0)

  -- storeU64BE size + round-trip
  for x in ([0, 1, 0xff, 0x0123456789abcdef, 0xffffffffffffffff] : List UInt64) do
    let b := storeU64BE ByteArray.empty x
    checkEq s!"storeU64BE size {x}" 8 b.size
    checkEq s!"storeU64BE round-trip {x}" x (loadU64BE! b 0)

  -- 256-bit LE round-trip
  for n in ([0, 1, 0xff, 2^128, 2^200, 2^256 - 1,
             0x1234567890abcdef1234567890abcdef] : List Nat) do
    let b := storeU256LE n
    checkEq s!"storeU256LE size {n}" 32 b.size
    checkEq s!"storeU256LE round-trip {n}" n (loadU256LE! b 0)

  -- bytesToHex / hexToBytes
  checkEq "bytesToHex empty" "" (bytesToHex ByteArray.empty)
  checkEq "bytesToHex deadbeef" "deadbeef" (bytesToHex (mkBA [0xde, 0xad, 0xbe, 0xef]))
  checkEq "bytesToHex 00ff" "00ff" (bytesToHex (mkBA [0x00, 0xff]))

  -- Hex round-trip
  for s in ["", "00", "ff", "deadbeef", "0123456789abcdef", "ABCDEF"] do
    match hexToBytes s with
    | none => fail s!"hexToBytes {s} returned none"
    | some b => checkEq s!"hex round-trip {s}" s.toLower (bytesToHex b)

  -- hexToBytes rejects odd-length and bad chars
  match hexToBytes "abc" with
  | none => ok
  | some _ => fail "hexToBytes odd-length should be none"
  match hexToBytes "zz" with
  | none => ok
  | some _ => fail "hexToBytes bad-char should be none"

def main : IO UInt32 := do
  let ((), (n, err)) := tests.run (0, none)
  match err with
  | some msg =>
      IO.eprintln s!"FAIL {msg} (after {n} passing)"
      return 1
  | none =>
      IO.println s!"OK {n} vectors"
      return 0
