import LeanCrypto.Bytes

/-!
# `LeanCrypto.Field.ScalarL`

Arithmetic in the scalar field `ℤ / ℓ` of edwards25519, where
`ℓ = 2²⁵² + 27742317777372353535851937790883648493`.

This is a different ring from `Fp25519` (the base field of the curve) —
mixing the two is a category error. We keep the abbrev distinct to make
that explicit at every call site.

v1 is `Nat`-backed; reductions are `Nat.mod`. Barrett / Montgomery
reductions are post-v1 optimisations. -/

set_option autoImplicit false

namespace LeanCrypto.Field.ScalarL

open LeanCrypto.Bytes

/-- A scalar element, represented as a `Nat` in `[0, L)`. -/
abbrev Scalar : Type := Nat

/-- The group order `ℓ = 2²⁵² + 27742317777372353535851937790883648493`. -/
def L : Nat := 2^252 + 27742317777372353535851937790883648493

@[inline] def zero : Scalar := 0
@[inline] def reduce (n : Nat) : Scalar := n % L
@[inline] def add (a b : Scalar) : Scalar := (a + b) % L
@[inline] def sub (a b : Scalar) : Scalar := (a + L - b % L) % L
@[inline] def mul (a b : Scalar) : Scalar := (a * b) % L

/-- Read 64 little-endian bytes and reduce mod ℓ. RFC 8032 §5.1.6 uses this
to convert `SHA-512(...)` outputs into scalars. -/
def reduce512Bit (b : ByteArray) : Scalar := Id.run do
  let mut acc : Nat := 0
  for i in [:b.size] do
    acc := acc ||| ((b.get! i).toNat <<< (i * 8))
  return acc % L

end LeanCrypto.Field.ScalarL
