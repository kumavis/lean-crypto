import LeanCrypto.Bytes
import LeanCrypto.Field.Fp25519

/-!
# `LeanCrypto.Curve.Edwards25519`

The edwards25519 twisted-Edwards curve `−x² + y² = 1 + d·x²·y²` over `F_p`
with `p = 2²⁵⁵ − 19`. Points carry the extended-coordinate representation
`(X, Y, Z, T)` with `T·Z = X·Y` (equivalently affine `(X/Z, Y/Z)` with
`T = XY/Z`).

Addition uses **2008-hwcd-3** (8M + 1k + 1A; unified — works for `P + P`),
doubling uses **dbl-2008-hwcd** for `a = −1` (4M + 4S + 1k). References:
[EFD](https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html).

Scalar multiplication is left-to-right double-and-add — total, simple, and
**timing-leaks the scalar**. v1 stance per `docs/PLAN.md` §8: document the
leak, don't fix it.

Encoding/decoding follow RFC 8032 §5.1.2–§5.1.3: 32 little-endian bytes of
`y` with the sign of `x` in the high bit of byte 31. `EdPoint.decode`
rejects `y ≥ p` (strict canonical). The signature module reuses this
helper for both verify modes — ZIP-215 calls a separate decoder that
reduces `y` mod `p` first. -/

set_option autoImplicit false

namespace LeanCrypto.Curve.Edwards25519

open LeanCrypto.Bytes
open LeanCrypto.Field
open LeanCrypto.Field.Fp25519

/-! ## Curve constants -/

/-- `d = −121665/121666 mod p`, the Edwards-curve constant. -/
def d : Fp :=
  0x52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3

/-- `k = 2d mod p`, precomputed for the addition formula. -/
def k2d : Fp := mul 2 d

/-! ## Point types -/

structure EdPoint where
  X : Fp
  Y : Fp
  Z : Fp
  T : Fp
  deriving Inhabited, BEq

structure EdAffine where
  x : Fp
  y : Fp
  deriving Inhabited, BEq

namespace EdPoint

/-- The identity (neutral element): affine `(0, 1)`. -/
def identity : EdPoint := { X := 0, Y := 1, Z := 1, T := 0 }

/-- The standard generator `B` of order `ℓ` (RFC 8032 §5.1). -/
def basePoint : EdPoint :=
  let bx : Fp := 0x216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a
  let by_ : Fp := 0x6666666666666666666666666666666666666666666666666666666666666658
  { X := bx, Y := by_, Z := 1, T := mul bx by_ }

/-! ## Group operations -/

/-- Unified addition (2008-hwcd-3). 8M + 1k + 1A. -/
def add (p1 p2 : EdPoint) : EdPoint :=
  let a  := mul (sub p1.Y p1.X) (sub p2.Y p2.X)
  let b  := mul (Fp25519.add p1.Y p1.X) (Fp25519.add p2.Y p2.X)
  let c  := mul (mul p1.T k2d) p2.T
  let dd := mul (mul p1.Z 2) p2.Z
  let e  := sub b a
  let f  := sub dd c
  let g  := Fp25519.add dd c
  let h  := Fp25519.add b a
  { X := mul e f
    Y := mul g h
    Z := mul f g
    T := mul e h }

/-- Doubling (dbl-2008-hwcd) for `a = −1`. 4M + 4S + 1k. -/
def double (p1 : EdPoint) : EdPoint :=
  let a   := square p1.X
  let b   := square p1.Y
  let c   := mul 2 (square p1.Z)
  let dd  := neg a                            -- D = a·A with a = −1
  let xPy := Fp25519.add p1.X p1.Y
  let e   := sub (sub (square xPy) a) b
  let g   := Fp25519.add dd b
  let f   := sub g c
  let h   := sub dd b
  { X := mul e f
    Y := mul g h
    Z := mul f g
    T := mul e h }

/-- Negate: `(X, Y, Z, T) ↦ (−X, Y, Z, −T)`. -/
def negate (p1 : EdPoint) : EdPoint :=
  { X := neg p1.X, Y := p1.Y, Z := p1.Z, T := neg p1.T }

/-- Scalar multiplication via left-to-right double-and-add. Leaks scalar
timing (see file header). -/
def smul (n : Nat) (p : EdPoint) : EdPoint := Id.run do
  if n == 0 then return identity
  let bits := 256
  let mut acc : EdPoint := identity
  for i in [:bits] do
    let bit := (n >>> (bits - 1 - i)) &&& 1
    acc := double acc
    if bit == 1 then
      acc := add acc p
  return acc

/-! ## Affine view -/

/-- Project to affine coordinates by dividing through by `Z`. -/
def toAffine (p : EdPoint) : EdAffine :=
  let zInv := inv p.Z
  { x := mul p.X zInv
    y := mul p.Y zInv }

/-! ## Encoding (RFC 8032 §5.1.2 / §5.1.3) -/

/-- Encode `P` as 32 little-endian bytes: `y` in low bits, high bit of
byte 31 holds the LSB of canonical affine `x`. -/
def encode (p : EdPoint) : ByteArray := Id.run do
  let af := toAffine p
  let mut out := storeU256LE af.y
  let xBit : UInt8 := UInt8.ofNat (af.x % 2)
  let b31 := out.get! 31
  out := out.set! 31 (b31 ||| (xBit <<< 7))
  return out

/-- Decode 32 LE bytes per RFC 8032 §5.1.3 (strict canonical: rejects
`y ≥ p`). Returns `none` on any failure. -/
def decode (bs : ByteArray) : Option EdPoint := do
  if bs.size != 32 then none
  let b31 := bs.get! 31
  let signBit := (b31 >>> 7) &&& 1
  let bs' := bs.set! 31 (b31 &&& 0x7f)
  let y := loadU256LE! bs' 0
  if y >= p then none
  let y2 := square y
  let u  := sub y2 1
  let v  := Fp25519.add (mul d y2) 1
  -- x² = u/v. Solve via the p ≡ 5 (mod 8) recipe:
  --   x = u·v³·(u·v⁷)^((p−5)/8)
  let v3 := mul (mul v v) v
  let v7 := mul (mul v3 v3) v
  let candidate := mul (mul u v3) (pow (mul u v7) ((p - 5) / 8))
  let cv := mul (square candidate) v
  let x ←
    if cv == u then some candidate
    else if cv == neg u then some (mul candidate sqrtM1)
    else none
  if x == 0 ∧ signBit == 1 then none
  let x := if (UInt8.ofNat (x % 2)) == signBit then x else neg x
  some { X := x, Y := y, Z := 1, T := mul x y }

end EdPoint

end LeanCrypto.Curve.Edwards25519
