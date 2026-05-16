import LeanCryptoProofs.Edwards25519.AddSpike

/-!
# Easy group laws on `add` (M22)

The Setoid-style `ProjEq` from M19 quantifies its witness over `(ZMod p)ˣ`
(units in `ZMod p`), which is great for transitivity (composition of
units) but inconvenient for proving group laws whose natural projective
witness involves products like `4·Z`. Constructing `(4·Z : ZMod p)ˣ`
requires proving that both `4` and `Z` are nonzero in `ZMod p`, which
ultimately rests on `Fact (Nat.Prime p)` for `p = 2^255 - 19` — a fact
we haven't established yet (and which is itself a substantial computation
to discharge formally).

For the M22 group lemmas we sidestep this by defining `CrossEq`, the
*cross-product* projective equivalence

  `X₁·Z₂ = X₂·Z₁ ∧ Y₁·Z₂ = Y₂·Z₁  (in ZMod p)`

This is exactly the form the runtime `projEq` Bool inside
`LeanCrypto.Signature.Ed25519.verify` checks (it ignores `T` because the
extended-coord invariant `T·Z = X·Y` is preserved by every operation).
`CrossEq` is reflexive and symmetric without preconditions; it is **not**
transitive in general (transitivity needs `Z ≠ 0` somewhere), but for
the group lemmas in this milestone we only need reflexivity and the
polynomial identities themselves.

Lemmas in M22:

* `ProjEq.cross` — every `ProjEq` implies `CrossEq` (so M19/M21 work
  flows through).
* `CrossEq.refl`, `CrossEq.symm`.
* `add_zero_left_crossEq`  — `add identity P ≡_cross P`. No hypothesis.
* `add_zero_right_crossEq` — `add P identity ≡_cross P`. No hypothesis.
* `OnCurve P` — the curve equation `-X² + Y² = Z² + d·T²` in extended
  coords.
* `add_negate_cancel_crossEq` — `add P (negate P) ≡_cross identity`
  for any `P` satisfying `OnCurve`.

`add_assoc_crossEq` is **not** attempted here; it's the M23 stretch goal
and remains the open question for the universal proof.
-/

set_option autoImplicit false

namespace LeanCrypto.Curve.Edwards25519
namespace EdPoint

open LeanCrypto.Field
open LeanCrypto.Field.Fp25519 (Fp p)

/-! ## Cross-product projective equality -/

/-- Cross-product projective equality: two points are `CrossEq` iff
`X₁·Z₂ = X₂·Z₁` and `Y₁·Z₂ = Y₂·Z₁` in `ZMod p`. -/
def CrossEq (p₁ p₂ : EdPoint) : Prop :=
  ((p₁.X : ZMod p) * (p₂.Z : ZMod p) = (p₂.X : ZMod p) * (p₁.Z : ZMod p)) ∧
  ((p₁.Y : ZMod p) * (p₂.Z : ZMod p) = (p₂.Y : ZMod p) * (p₁.Z : ZMod p))

@[refl] lemma CrossEq.refl (q : EdPoint) : CrossEq q q :=
  ⟨rfl, rfl⟩

@[symm] lemma CrossEq.symm {p₁ p₂ : EdPoint} (h : CrossEq p₁ p₂) :
    CrossEq p₂ p₁ :=
  ⟨h.1.symm, h.2.symm⟩

/-- Every `ProjEq` (the M19 Setoid form) implies `CrossEq`. -/
lemma ProjEq.cross {p₁ p₂ : EdPoint} (h : ProjEq p₁ p₂) : CrossEq p₁ p₂ := by
  obtain ⟨lam, hx, hy, hz⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hx, hz]; ring
  · rw [hy, hz]; ring

/-! ## Curve equation in extended coordinates

Twisted Edwards: `-x² + y² = 1 + d·x²·y²` (affine).  Substituting
`x = X/Z`, `y = Y/Z`, `T = X·Y/Z` and clearing `Z²` gives
`-X² + Y² = Z² + d·T²`. -/

/-- The extended-Edwards curve equation `-X² + Y² = Z² + d·T²` in `ZMod p`. -/
def OnCurve (q : EdPoint) : Prop :=
  -((q.X : ZMod p))^2 + ((q.Y : ZMod p))^2
    = ((q.Z : ZMod p))^2 + ((d : ZMod p)) * ((q.T : ZMod p))^2

/-! ## `add identity P` and `add P identity` -/

/-- Left identity: `add identity P ≡_cross P`. Pure polynomial identity,
no curve-equation hypothesis required. -/
lemma add_zero_left_crossEq (q : EdPoint) : CrossEq (add identity q) q := by
  refine ⟨?_, ?_⟩ <;>
  · -- After unfolding `add` and pushing casts through, both components
    -- collapse to a polynomial identity in (X, Y, Z, T) over ZMod p.
    show ((_ : Nat) : ZMod p) * _ = _ * ((_ : Nat) : ZMod p)
    simp only [add, identity, k2d, castZMod_fp25519_mul, castZMod_fp25519_add,
               castZMod_fp25519_sub, Nat.cast_one]
    ring

/-- Right identity: `add P identity ≡_cross P`. -/
lemma add_zero_right_crossEq (q : EdPoint) : CrossEq (add q identity) q := by
  refine ⟨?_, ?_⟩ <;>
  · show ((_ : Nat) : ZMod p) * _ = _ * ((_ : Nat) : ZMod p)
    simp only [add, identity, k2d, castZMod_fp25519_mul, castZMod_fp25519_add,
               castZMod_fp25519_sub, Nat.cast_one]
    ring

/-! ## `add P (negate P)` for `P` on the curve -/

/-- For any point on the curve, `add P (negate P) ≡_cross identity`.
First lemma in this file requiring the curve equation as a side
hypothesis. The Y-component goal reduces to

  `4·(Z² − d·T²) · ((Y² − X²) − (Z² + d·T²)) = 0`

after expansion; the bracketed factor is `(LHS − RHS)` of `hq`, so the
linear-combination witness is `4·(Z² − d·T²)`. The plumbing dance:

* `linear_combination` needs the coefficient ascribed to `ZMod p`
  explicitly (otherwise the outer `4` is parsed as `Nat` and gets
  stripped, with the linter warning "this constant has no effect").
* The post-`simp` goal has un-normalised casts (`↑2`, `↑(2·d)`);
  `push_cast` normalises them so `ring` can close the residual.
* The hypothesis comes in as `-X² + Y² = Z² + d·T²`; rearranging to
  `Y² − X² = Z² + d·T²` (the form that matches the bracketed factor)
  needs `linear_combination this` rather than `linarith` (which
  doesn't apply over `ZMod p`). -/
lemma add_negate_cancel_crossEq (q : EdPoint) (hq : OnCurve q) :
    CrossEq (add q (negate q)) identity := by
  refine ⟨?_, ?_⟩
  · -- First component: (add P (-P)).X = 0, identity.X = 0 — both sides 0.
    show ((_ : Nat) : ZMod p) * _ = _ * ((_ : Nat) : ZMod p)
    simp only [add, negate, identity, k2d, castZMod_fp25519_mul,
               castZMod_fp25519_add, castZMod_fp25519_sub,
               castZMod_fp25519_neg, Nat.cast_one]
    ring
  · -- Second component: the polynomial identity above. Goal at this
    -- point is `(2Z² − 2d·T²)·2(Y² − X²) · 1 = 1 · (2Z² + 2d·T²)(2Z² − 2d·T²)`
    -- after pushing the cast through. We rearrange `hq` into
    -- `Y² − X² = Z² + d·T²` form, then dispatch with the explicit
    -- witness via `linear_combination`.
    show ((_ : Nat) : ZMod p) * _ = _ * ((_ : Nat) : ZMod p)
    simp only [add, negate, identity, k2d, castZMod_fp25519_mul,
               castZMod_fp25519_add, castZMod_fp25519_sub,
               castZMod_fp25519_neg, Nat.cast_one]
    push_cast
    have hq' : (q.Y : ZMod p)^2 - (q.X : ZMod p)^2
                = (q.Z : ZMod p)^2 + (d : ZMod p) * (q.T : ZMod p)^2 := by
      unfold OnCurve at hq
      linear_combination hq
    linear_combination
      ((4 : ZMod p) * ((q.Z : ZMod p)^2 - (d : ZMod p) * (q.T : ZMod p)^2)) * hq'

end EdPoint
end LeanCrypto.Curve.Edwards25519
