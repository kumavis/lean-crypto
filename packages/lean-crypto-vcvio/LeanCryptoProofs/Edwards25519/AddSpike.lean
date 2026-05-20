import LeanCryptoProofs.Edwards25519.ProjEq
import Mathlib.Tactic.LinearCombination

/-!
# M21 spike — probe `ring` / `linear_combination` on the 2008-HWCD formula

Goal of the spike: find out whether Mathlib's `ring`/`linear_combination`
tactics can mechanically close polynomial identities in the 2008-HWCD-3
addition formula on extended Edwards coordinates, when cast through
`castZMod_fp25519_*` from M19.

This file deliberately attempts the **easiest** group-law obligation first
— **commutativity** of `add`. It needs no curve-equation hypothesis (the
2008-HWCD formula is syntactically symmetric in its two arguments after
unfolding multiplications and additions). If `ring` closes this in seconds,
that's strong evidence the harder lemmas (`add_assoc`, `add_neg_cancel`,
inverse, identity) are tractable too — they would need
`linear_combination` with the curve equation `-X² + Y² = Z² + d·T²/Z²` as
a hypothesis, mirroring the pattern in Mathlib's `EllipticCurve/Projective/
Formula.lean`.

If `ring` chokes on this spike, that's a strong signal Path C is harder
than the M20 plan estimated.

The result of running this spike is reported back in the M21 commit
message and PR comment thread; downstream-planning decisions (whether to
scope M22 or document Path C as infeasible) depend on it.
-/

set_option autoImplicit false

namespace LeanCrypto.Curve.Edwards25519
namespace EdPoint

open LeanCrypto.Field
open LeanCrypto.Field.Fp25519 (Fp p)

/-- `Fp25519.sub` casts to subtraction in `ZMod p`. Needed because the
2008-HWCD formula's body uses `sub` in several intermediate quantities
(`a = (Y₁ − X₁)·(Y₂ − X₂)`, `e = b − a`, `f = D − C`). -/
@[simp] lemma castZMod_fp25519_sub (a b : Fp) :
    ((Fp25519.sub a b : Nat) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  -- sub a b := (a + p - b % p) % p
  show (((a + p - b % p) % p : Nat) : ZMod p) = (a : ZMod p) - (b : ZMod p)
  rw [ZMod.natCast_mod]
  have hp_pos : (0 : Nat) < p := by decide
  have hbp : b % p ≤ a + p :=
    (Nat.le_of_lt (Nat.mod_lt b hp_pos)).trans (Nat.le_add_left p a)
  rw [Nat.cast_sub hbp, Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_mod]

/-- `Fp25519.neg` casts to negation in `ZMod p`. Needed because the curve
operation `negate` and the negated-`T` branch of the addition formula
introduce `Fp25519.neg`. -/
@[simp] lemma castZMod_fp25519_neg (a : Fp) :
    ((Fp25519.neg a : Nat) : ZMod p) = -((a : ZMod p)) := by
  -- neg a := (p - a % p) % p
  show (((p - a % p) % p : Nat) : ZMod p) = -((a : ZMod p))
  rw [ZMod.natCast_mod]
  have hp_pos : (0 : Nat) < p := by decide
  have h1 : a % p ≤ p := (Nat.mod_lt _ hp_pos).le
  rw [Nat.cast_sub h1, ZMod.natCast_self, ZMod.natCast_mod]
  ring

/-- Commutativity of `add` *modulo* `ProjEq`. With the 2008-HWCD-3
formula this is in fact componentwise equality after casting to
`ZMod p`, with `λ = 1`. -/
lemma add_comm_projEq (p₁ p₂ : EdPoint) : ProjEq (add p₁ p₂) (add p₂ p₁) := by
  refine ⟨1, ?_, ?_, ?_⟩ <;>
  · -- Unfold `add`, push the cast through via the `castZMod_fp25519_*` simp
    -- lemmas, then close by `ring`.
    show ((_ : Nat) : ZMod p) = (1 : ZMod p) * ((_ : Nat) : ZMod p)
    simp only [add, castZMod_fp25519_mul, castZMod_fp25519_add,
               castZMod_fp25519_sub, one_mul]
    ring

end EdPoint
end LeanCrypto.Curve.Edwards25519
