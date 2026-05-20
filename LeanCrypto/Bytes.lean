/-!
# `LeanCrypto.Bytes`

Byte-array helpers used by every primitive in this library.

* Big-endian `UInt32`/`UInt64` loads — used by SHA-2.
* Little-endian 256-bit loads/stores — used by Ed25519 (scalar and
  y-coordinate encoding).
* Append-style `UInt32`/`UInt64` stores — used to emit hash digests and
  Merkle–Damgård length fields.
* `bytesToHex` / `hexToBytes` for test-vector parsing.

All load functions are total and take a proof that the requested slice fits
in the source `ByteArray`. The proof obligation is usually discharged by
`by decide` (literal inputs) or `by omega` (loop-bound contexts), matching
the pattern in gdncc/Cryptography.
-/

set_option autoImplicit false

namespace LeanCrypto.Bytes

/-! ## Big-endian word loads -/

/-- Load 4 bytes at offset `off` from `b` as a big-endian `UInt32`. -/
@[inline] def loadU32BE (b : ByteArray) (off : Nat) (h : off + 4 ≤ b.size) : UInt32 :=
  let b0 : UInt32 := (b[off]'(by omega)).toUInt32
  let b1 : UInt32 := (b[off + 1]'(by omega)).toUInt32
  let b2 : UInt32 := (b[off + 2]'(by omega)).toUInt32
  let b3 : UInt32 := (b[off + 3]'(by omega)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Load 8 bytes at offset `off` from `b` as a big-endian `UInt64`. -/
@[inline] def loadU64BE (b : ByteArray) (off : Nat) (h : off + 8 ≤ b.size) : UInt64 :=
  let b0 : UInt64 := (b[off]'(by omega)).toUInt64
  let b1 : UInt64 := (b[off + 1]'(by omega)).toUInt64
  let b2 : UInt64 := (b[off + 2]'(by omega)).toUInt64
  let b3 : UInt64 := (b[off + 3]'(by omega)).toUInt64
  let b4 : UInt64 := (b[off + 4]'(by omega)).toUInt64
  let b5 : UInt64 := (b[off + 5]'(by omega)).toUInt64
  let b6 : UInt64 := (b[off + 6]'(by omega)).toUInt64
  let b7 : UInt64 := (b[off + 7]'(by omega)).toUInt64
  (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32)
    ||| (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7

/-! ### Panicky variants for tests / parsers

These call `ByteArray.get!`, which returns `0` and emits a runtime panic
message on out-of-bounds. Use them in test runners and `.rsp`/JSON parsers
where input validation has already happened (or where a runtime panic is
exactly the right failure mode); hot-path crypto code must use the
proof-carrying versions above. -/

@[inline] def loadU32BE! (b : ByteArray) (off : Nat) : UInt32 :=
  let b0 : UInt32 := (b.get! off).toUInt32
  let b1 : UInt32 := (b.get! (off + 1)).toUInt32
  let b2 : UInt32 := (b.get! (off + 2)).toUInt32
  let b3 : UInt32 := (b.get! (off + 3)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

@[inline] def loadU64BE! (b : ByteArray) (off : Nat) : UInt64 :=
  let b0 : UInt64 := (b.get! off).toUInt64
  let b1 : UInt64 := (b.get! (off + 1)).toUInt64
  let b2 : UInt64 := (b.get! (off + 2)).toUInt64
  let b3 : UInt64 := (b.get! (off + 3)).toUInt64
  let b4 : UInt64 := (b.get! (off + 4)).toUInt64
  let b5 : UInt64 := (b.get! (off + 5)).toUInt64
  let b6 : UInt64 := (b.get! (off + 6)).toUInt64
  let b7 : UInt64 := (b.get! (off + 7)).toUInt64
  (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32)
    ||| (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7

def loadU256LE! (b : ByteArray) (off : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:32] do
    acc := acc ||| ((b.get! (off + i)).toNat <<< (i * 8))
  acc

/-! ## Big-endian word stores (append) -/

/-- Append the big-endian bytes of `x` to `b`. -/
@[inline] def storeU32BE (b : ByteArray) (x : UInt32) : ByteArray :=
  (((b.push (x >>> 24).toUInt8).push (x >>> 16).toUInt8).push (x >>> 8).toUInt8).push x.toUInt8

/-- Append the big-endian bytes of `x` to `b`. -/
@[inline] def storeU64BE (b : ByteArray) (x : UInt64) : ByteArray :=
  (((((((b.push (x >>> 56).toUInt8).push (x >>> 48).toUInt8).push (x >>> 40).toUInt8).push (x >>> 32).toUInt8).push (x >>> 24).toUInt8).push (x >>> 16).toUInt8).push (x >>> 8).toUInt8).push x.toUInt8

/-! ## Little-endian 256-bit (32-byte) load/store

These build/consume a `Nat`. The store always produces 32 bytes (truncating
high bits silently if `n ≥ 2^256` — callers in Ed25519 reduce mod p first).
-/

/-- Read 32 little-endian bytes at offset `off` from `b` as a `Nat`. -/
def loadU256LE (b : ByteArray) (off : Nat) (h : off + 32 ≤ b.size) : Nat := Id.run do
  let mut acc : Nat := 0
  for hi : i in [:32] do
    have : i < 32 := hi.upper
    acc := acc ||| ((b[off + i]'(by omega)).toNat <<< (i * 8))
  acc

/-- Encode the low 256 bits of `n` as 32 little-endian bytes. -/
def storeU256LE (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut x := n
  for _ in [:32] do
    out := out.push (UInt8.ofNat (x % 256))
    x := x >>> 8
  out

/-! ## Hex ↔ bytes -/

private def nibbleToChar (n : UInt8) : Char :=
  let n := n.toNat
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Lowercase hex encoding of a `ByteArray`. -/
def bytesToHex (b : ByteArray) : String := Id.run do
  let mut s : String := ""
  for i in [:b.size] do
    let byte := b.get! i
    s := s.push (nibbleToChar (byte >>> 4))
    s := s.push (nibbleToChar (byte &&& 0x0f))
  s

private def hexCharToNibble? (c : Char) : Option UInt8 :=
  let n := c.toNat
  if '0'.toNat ≤ n ∧ n ≤ '9'.toNat then some (UInt8.ofNat (n - '0'.toNat))
  else if 'a'.toNat ≤ n ∧ n ≤ 'f'.toNat then some (UInt8.ofNat (n - 'a'.toNat + 10))
  else if 'A'.toNat ≤ n ∧ n ≤ 'F'.toNat then some (UInt8.ofNat (n - 'A'.toNat + 10))
  else none

/-- Decode a hex string into a `ByteArray`. Returns `none` on bad chars or odd
length. Accepts upper or lower case. -/
def hexToBytes (s : String) : Option ByteArray := Id.run do
  let cs := s.toList
  if cs.length % 2 != 0 then return none
  let mut out := ByteArray.empty
  let mut pair : List Char := cs
  while !pair.isEmpty do
    match pair with
    | hi :: lo :: rest =>
        match hexCharToNibble? hi, hexCharToNibble? lo with
        | some h, some l => out := out.push ((h <<< 4) ||| l); pair := rest
        | _, _ => return none
    | _ => return none  -- unreachable given length-mod-2 check
  return some out

end LeanCrypto.Bytes
