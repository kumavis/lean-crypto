/-!
# `LeanCrypto.Field.Fp25519`

Arithmetic in `F_p` where `p = 2²⁵⁵ − 19` — the prime field of edwards25519.

v1 is `Nat`-backed: a `Fp` value is a `Nat` carrying the public invariant
`0 ≤ v < p`. Every operation here normalises its result to `[0, p)`.
Future optimisation (limb representation) can replace this without touching
call sites, provided they always go through the named operations rather
than raw `+`/`*` on `Nat`.

* `inv` uses Fermat's little theorem: `a⁻¹ ≡ a^(p−2) (mod p)`.
* `sqrt` uses the `p ≡ 5 (mod 8)` formula:
  `r = a^((p+3)/8)`; if `r² ≡ a` return `r`; else if `(r·√−1)² ≡ a` return that;
  else `none`.

`pow` is square-and-multiply with a fixed 256-iteration upper bound — every
exponent in this library fits in 256 bits and the constant-iteration shape
sidesteps termination-proof noise. -/

set_option autoImplicit false

namespace LeanCrypto.Field.Fp25519

/-- A field element, represented as a `Nat` in `[0, p)`. Operations preserve
the canonical-representative invariant. -/
abbrev Fp : Type := Nat

/-- The field prime `p = 2²⁵⁵ − 19`. -/
def p : Nat := 2^255 - 19

/-- Reduce an arbitrary `Nat` to a canonical field element. -/
@[inline] def reduce (n : Nat) : Fp := n % p

@[inline] def zero : Fp := 0
@[inline] def one  : Fp := 1

@[inline] def add (a b : Fp) : Fp := (a + b) % p
@[inline] def sub (a b : Fp) : Fp := (a + p - b % p) % p
@[inline] def neg (a : Fp) : Fp := (p - a % p) % p
@[inline] def mul (a b : Fp) : Fp := (a * b) % p
@[inline] def square (a : Fp) : Fp := mul a a

/-- Square-and-multiply with a fixed 256-iteration bound. Any exponent we
care about fits in 256 bits. -/
def pow (a : Fp) (e : Nat) : Fp := Id.run do
  let mut result : Fp := 1
  let mut base : Fp := a % p
  let mut exp := e
  for _ in [:256] do
    if exp % 2 == 1 then
      result := (result * base) % p
    base := (base * base) % p
    exp := exp / 2
  return result

/-- Modular inverse via Fermat's little theorem. Returns `0` when `a ≡ 0`. -/
def inv (a : Fp) : Fp := pow a (p - 2)

/-- The square root of `-1` mod `p`. Equal to `2^((p-1)/4) mod p`; hard-coded
to avoid recomputation on every call. Independently verified to match
noble-ed25519's `RM1`. -/
def sqrtM1 : Fp :=
  0x2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0

/-- Modular square root, valid for `p ≡ 5 (mod 8)`. Returns `none` when
`a` is not a quadratic residue. -/
def sqrt (a : Fp) : Option Fp :=
  let a := a % p
  let r := pow a ((p + 3) / 8)
  if square r == a then some r
  else
    let r' := (r * sqrtM1) % p
    if square r' == a then some r'
    else none

end LeanCrypto.Field.Fp25519
