import LeanCrypto.Bytes

/-!
# `LeanCrypto.Hash.SHA512`

SHA-512 per FIPS 180-4 §6.4.

Structurally identical to `LeanCrypto.Hash.SHA256`, but on native `UInt64`
words with 128-byte blocks, 80 rounds, and a 128-bit length field. We
deliberately use native `UInt64` — noble-hashes' `_u64.ts` split-into-two-
`UInt32`s representation exists only because JavaScript bitwise ops are
32-bit, and is unnecessary in Lean.

The 128-bit length field is encoded as 8 zero bytes followed by the
big-endian low-64 bits of `8 * totalLen`. This is correct for any input
shorter than 2⁶¹ bytes (≈ 2 EB); no real-world input ever reaches that.
-/

set_option autoImplicit false

namespace LeanCrypto.Hash.SHA512

open LeanCrypto.Bytes

/-! ## Sized vectors -/

private abbrev Vec (n : Nat) := { arr : Array UInt64 // arr.size = n }

instance (n : Nat) : GetElem (Vec n) Nat UInt64 (fun _ i => i < n) where
  getElem v i h := v.val[i]'(v.property.symm ▸ h)

@[always_inline, inline]
private def Vec.set {n : Nat} (v : Vec n) (i : Nat) (x : UInt64) : Vec n :=
  ⟨v.val.modify i (fun _ => x), by simp [Array.size_modify, v.property]⟩

private abbrev State    := Vec 8
private abbrev Schedule := Vec 80
private abbrev Consts80 := Vec 80

/-! ## Constants (FIPS 180-4 §5.3.5, §4.2.3) -/

private def IV : State := ⟨
  #[ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
     0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179 ],
  by decide⟩

private def K : Consts80 := ⟨
  #[ 0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
     0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
     0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
     0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
     0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
     0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
     0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
     0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
     0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
     0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
     0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
     0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
     0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
     0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
     0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
     0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
     0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
     0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
     0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
     0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817 ],
  by decide⟩

/-! ## Bit-twiddling primitives (FIPS 180-4 §4.1.3) -/

@[always_inline, inline]
def rotr64 (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

@[always_inline, inline] private def Ch  (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (~~~x &&& z)
@[always_inline, inline] private def Maj (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
@[always_inline, inline] private def bigSigma0   (x : UInt64) : UInt64 := rotr64 x 28 ^^^ rotr64 x 34 ^^^ rotr64 x 39
@[always_inline, inline] private def bigSigma1   (x : UInt64) : UInt64 := rotr64 x 14 ^^^ rotr64 x 18 ^^^ rotr64 x 41
@[always_inline, inline] private def smallSigma0 (x : UInt64) : UInt64 := rotr64 x 1  ^^^ rotr64 x 8  ^^^ (x >>> 7)
@[always_inline, inline] private def smallSigma1 (x : UInt64) : UInt64 := rotr64 x 19 ^^^ rotr64 x 61 ^^^ (x >>> 6)

/-! ## Per-block compression (FIPS 180-4 §6.4.2) -/

/-- Process one 128-byte block at offset `off` of `b`. -/
def compressBlock (s : State) (b : ByteArray) (off : Nat) (h : off + 128 ≤ b.size) : State := Id.run do
  let mut W : Schedule := ⟨Array.replicate 80 0, by decide⟩
  -- W[0..15] = 16 big-endian UInt64 from the block bytes.
  for hi : i in [:16] do
    have _hi' : i + 1 ≤ 16 := hi.upper
    have hb : off + 8*i + 8 ≤ b.size := by omega
    W := W.set i (loadU64BE b (off + 8*i) hb)
  -- W[16..79] via the message schedule recurrence.
  for hj : j in [:64] do
    have _hj' : j + 1 ≤ 64 := hj.upper
    let t := j + 16
    let w15 := W[t - 15]'(by omega)
    let w2  := W[t -  2]'(by omega)
    let w7  := W[t -  7]'(by omega)
    let w16 := W[t - 16]'(by omega)
    let s0 := smallSigma0 w15
    let s1 := smallSigma1 w2
    W := W.set t (s1 + w7 + s0 + w16)
  let mut a := s[0]
  let mut b' := s[1]
  let mut c := s[2]
  let mut d := s[3]
  let mut e := s[4]
  let mut f := s[5]
  let mut g := s[6]
  let mut h' := s[7]
  for ht : t in [:80] do
    have _ht' : t + 1 ≤ 80 := ht.upper
    let T1 := h' + bigSigma1 e + Ch e f g + K[t] + W[t]
    let T2 := bigSigma0 a + Maj a b' c
    h' := g; g := f; f := e; e := d + T1
    d  := c; c := b'; b' := a; a := T1 + T2
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

Padding is applied inline by `Sha512Ctx.finalize`: append `0x80`, zero-fill
until the size is congruent to 112 (mod 128), then append 16 bytes of
big-endian total bit-length (high 8 bytes are 0 — see file header). -/

structure Sha512Ctx where
  state    : State
  buffer   : ByteArray
  totalLen : Nat

def Sha512Ctx.init : Sha512Ctx :=
  { state := IV, buffer := ByteArray.empty, totalLen := 0 }

private def absorb (s : State) (b : ByteArray) : State × ByteArray := Id.run do
  let nBlocks := b.size / 128
  let mut s := s
  for hi : i in [:nBlocks] do
    have _hi' : i + 1 ≤ nBlocks := hi.upper
    let off := i * 128
    have hb : off + 128 ≤ b.size := by
      have h := Nat.div_mul_le_self b.size 128
      omega
    s := compressBlock s b off hb
  return (s, b.extract (nBlocks * 128) b.size)

def Sha512Ctx.update (ctx : Sha512Ctx) (input : ByteArray) : Sha512Ctx :=
  let combined := ctx.buffer ++ input
  let (state, buffer) := absorb ctx.state combined
  { state := state
    buffer := buffer
    totalLen := ctx.totalLen + input.size }

def Sha512Ctx.finalize (ctx : Sha512Ctx) : ByteArray := Id.run do
  let lenBits : UInt64 := UInt64.ofNat (ctx.totalLen * 8)
  let mut tail := ctx.buffer
  tail := tail.push 0x80
  while tail.size % 128 != 112 do
    tail := tail.push 0
  -- 16-byte BE length: high 8 bytes are zero, low 8 are the bit length.
  tail := storeU64BE tail 0
  tail := storeU64BE tail lenBits
  let (state, _) := absorb ctx.state tail
  let mut out := ByteArray.empty
  for hi : i in [:8] do
    have _hi' : i + 1 ≤ 8 := hi.upper
    out := storeU64BE out state[i]
  out

/-- Compute the SHA-512 digest of `msg`. Always returns 64 bytes. -/
def sha512 (msg : ByteArray) : ByteArray :=
  (Sha512Ctx.init.update msg).finalize

end LeanCrypto.Hash.SHA512
