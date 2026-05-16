import LeanCrypto.Bytes

/-!
# `LeanCrypto.Hash.SHA256`

SHA-256 per FIPS 180-4 §6.2.

This file ships the one-shot `sha256 : ByteArray → ByteArray` (M3). The
streaming `Sha256Ctx`/`init`/`update`/`finalize` API lands in M4 and
re-uses the per-block compression here.

The hash context state lives as a sized subtype with a `GetElem` instance,
matching the gdncc/Cryptography idiom — every indexed access carries an
inline-discharged proof and the array size is preserved across updates.
No `partial`, no `sorry`, no `unsafe`.
-/

set_option autoImplicit false

namespace LeanCrypto.Hash.SHA256

open LeanCrypto.Bytes

/-! ## Sized vectors -/

private abbrev Vec (n : Nat) := { arr : Array UInt32 // arr.size = n }

instance (n : Nat) : GetElem (Vec n) Nat UInt32 (fun _ i => i < n) where
  getElem v i h := v.val[i]'(v.property.symm ▸ h)

@[always_inline, inline]
private def Vec.set {n : Nat} (v : Vec n) (i : Nat) (x : UInt32) : Vec n :=
  ⟨v.val.modify i (fun _ => x), by simp [Array.size_modify, v.property]⟩

private abbrev State    := Vec 8
private abbrev Schedule := Vec 64
private abbrev Consts64 := Vec 64

/-! ## Constants (FIPS 180-4 §5.3.3, §4.2.2) -/

private def IV : State := ⟨
  #[ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
     0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ], by decide⟩

private def K : Consts64 := ⟨
  #[ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
     0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
     0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
     0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
     0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
     0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
     0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
     0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ],
  by decide⟩

/-! ## Bit-twiddling primitives (FIPS 180-4 §4.1.2) -/

@[always_inline, inline]
def rotr32 (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

@[always_inline, inline] private def Ch  (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)
@[always_inline, inline] private def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
@[always_inline, inline] private def bigSigma0 (x : UInt32) : UInt32 := rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22
@[always_inline, inline] private def bigSigma1 (x : UInt32) : UInt32 := rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25
@[always_inline, inline] private def smallSigma0 (x : UInt32) : UInt32 := rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> 3)
@[always_inline, inline] private def smallSigma1 (x : UInt32) : UInt32 := rotr32 x 17 ^^^ rotr32 x 19 ^^^ (x >>> 10)

/-! ## Per-block compression (FIPS 180-4 §6.2.2) -/

/-- Process one 64-byte block at offset `off` of `b` and return the updated
state.  Caller must ensure `off + 64 ≤ b.size`. -/
def compressBlock (s : State) (b : ByteArray) (off : Nat) (h : off + 64 ≤ b.size) : State := Id.run do
  -- Build the message schedule W[0..63].
  let mut W : Schedule := ⟨Array.replicate 64 0, by decide⟩
  -- W[0..15] = 16 big-endian UInt32 from the block bytes.
  for hi : i in [:16] do
    have hi' : i < 16 := hi.upper
    have hb : off + 4*i + 4 ≤ b.size := by omega
    W := W.set i (loadU32BE b (off + 4*i) hb)
  -- W[16..63] via the message schedule recurrence.
  for hj : j in [:48] do
    have _hj' : j + 1 ≤ 48 := hj.upper
    let t := j + 16
    let w15 := W[t - 15]'(by omega)
    let w2  := W[t -  2]'(by omega)
    let w7  := W[t -  7]'(by omega)
    let w16 := W[t - 16]'(by omega)
    let s0 := smallSigma0 w15
    let s1 := smallSigma1 w2
    W := W.set t (s1 + w7 + s0 + w16)
  -- Working variables.
  let mut a := s[0]
  let mut b' := s[1]
  let mut c := s[2]
  let mut d := s[3]
  let mut e := s[4]
  let mut f := s[5]
  let mut g := s[6]
  let mut h' := s[7]
  -- 64 rounds.
  for ht : t in [:64] do
    have ht' : t < 64 := ht.upper
    let T1 := h' + bigSigma1 e + Ch e f g + K[t] + W[t]
    let T2 := bigSigma0 a + Maj a b' c
    h' := g; g := f; f := e; e := d + T1
    d  := c; c := b'; b' := a; a := T1 + T2
  -- Add the working variables back into the state.
  let s := s.set 0 (s[0] + a)
  let s := s.set 1 (s[1] + b')
  let s := s.set 2 (s[2] + c)
  let s := s.set 3 (s[3] + d)
  let s := s.set 4 (s[4] + e)
  let s := s.set 5 (s[5] + f)
  let s := s.set 6 (s[6] + g)
  let s := s.set 7 (s[7] + h')
  s

/-! ## Streaming API

Padding (FIPS 180-4 §5.1.1) is applied inline by `Sha256Ctx.finalize`: append
`0x80`, zero-fill until the size is congruent to 56 (mod 64), then append the
64-bit big-endian total bit-length of the original message. The streaming
form is the canonical implementation; the one-shot `sha256` below is a thin
wrapper. -/

/-- SHA-256 streaming context. `buffer` holds the current partial block
(`< 64` bytes); `totalLen` counts every byte ever passed to `update`. -/
structure Sha256Ctx where
  state    : State
  buffer   : ByteArray
  totalLen : Nat

/-- Fresh, empty context. -/
def Sha256Ctx.init : Sha256Ctx :=
  { state := IV, buffer := ByteArray.empty, totalLen := 0 }

/-- Helper: process every full 64-byte block of `b` against state `s` and
return the new state along with the trailing partial-block bytes. -/
private def absorb (s : State) (b : ByteArray) : State × ByteArray := Id.run do
  let nBlocks := b.size / 64
  let mut s := s
  for hi : i in [:nBlocks] do
    have hi' : i + 1 ≤ nBlocks := hi.upper
    let off := i * 64
    have hb : off + 64 ≤ b.size := by
      have h := Nat.div_mul_le_self b.size 64
      omega
    s := compressBlock s b off hb
  let consumed := nBlocks * 64
  return (s, b.extract consumed b.size)

/-- Absorb `input`. Internally accumulates partial blocks until they can be
processed; safe to call with any size. -/
def Sha256Ctx.update (ctx : Sha256Ctx) (input : ByteArray) : Sha256Ctx :=
  let combined := ctx.buffer ++ input
  let (state, buffer) := absorb ctx.state combined
  { state := state
    buffer := buffer
    totalLen := ctx.totalLen + input.size }

/-- Apply padding to the trailing partial block and emit the final 32-byte digest. -/
def Sha256Ctx.finalize (ctx : Sha256Ctx) : ByteArray := Id.run do
  let lenBits : UInt64 := UInt64.ofNat (ctx.totalLen * 8)
  let mut tail := ctx.buffer
  tail := tail.push 0x80
  while tail.size % 64 != 56 do
    tail := tail.push 0
  tail := storeU64BE tail lenBits
  -- Now tail.size is a multiple of 64 (either 64 or 128).
  let (state, _) := absorb ctx.state tail
  let mut out := ByteArray.empty
  for hi : i in [:8] do
    have _hi' : i + 1 ≤ 8 := hi.upper
    out := storeU32BE out state[i]
  out

/-! ## One-shot SHA-256 -/

/-- Compute the SHA-256 digest of `msg`. Always returns 32 bytes. Implemented
as a single `update` + `finalize` over the streaming API for byte-for-byte
parity with chunked input. -/
def sha256 (msg : ByteArray) : ByteArray :=
  (Sha256Ctx.init.update msg).finalize

end LeanCrypto.Hash.SHA256
