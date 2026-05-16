import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import LeanCrypto.Curve.Edwards25519

/-!
# Projective equality on `EdPoint`

Foundational lemmas for reasoning about edwards25519 points modulo the
projective equivalence used by all of our group operations.

We define `ProjEq p₁ p₂` as

> ∃ λ ∈ (ZMod p)ˣ, X₂ = λ·X₁ ∧ Y₂ = λ·Y₁ ∧ Z₂ = λ·Z₁

— there's a nonzero scalar `λ` such that the second point's coordinates
are `λ` times the first's. This is the proper projective equivalence and
yields a clean `Setoid` (reflexive via `λ = 1`, symmetric via `λ⁻¹`,
transitive via `λ₁·λ₂`) without case-splits on whether `Z` is zero.

The runtime helper `LeanCrypto.Curve.Edwards25519.EdPoint.projEq`-style
Bool used inside `Ed25519.verify` checks the cross-product form
`X₁·Z₂ = X₂·Z₁ ∧ Y₁·Z₂ = Y₂·Z₁`. The two coincide when at least one `Z`
is a unit in `ZMod p`. Linking them (and the heavier group laws, encode
invariance, distributivity of `smul`, order of `basePoint`) is scoped to
the M20 proof roadmap; M19 ships just the Setoid foundation plus the
`Fp25519`-to-`ZMod` casting lemmas every later proof will use.
-/

set_option autoImplicit false

namespace LeanCrypto.Curve.Edwards25519
namespace EdPoint

open LeanCrypto.Field
open LeanCrypto.Field.Fp25519 (Fp p)

/-! ## Casting `Fp25519` operations into `ZMod p` -/

/-- `Fp25519`'s `Nat`-backed `add` casts to plain addition in `ZMod p`. -/
@[simp] lemma castZMod_fp25519_add (a b : Fp) :
    ((Fp25519.add a b : Nat) : ZMod p) = (a : ZMod p) + (b : ZMod p) := by
  simp [Fp25519.add, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod]

/-- `Fp25519`'s `Nat`-backed `mul` casts to plain multiplication in `ZMod p`. -/
@[simp] lemma castZMod_fp25519_mul (a b : Fp) :
    ((Fp25519.mul a b : Nat) : ZMod p) = (a : ZMod p) * (b : ZMod p) := by
  simp [Fp25519.mul, Nat.cast_mul, ZMod.natCast_mod, ZMod.natCast_mod]

/-! ## Projective equality -/

/-- Projective equivalence on `EdPoint`: there is a unit `λ` in `(ZMod p)ˣ`
such that the second point's coordinates are `λ` times the first's. -/
def ProjEq (p₁ p₂ : EdPoint) : Prop :=
  ∃ (lam : (ZMod p)ˣ),
    (p₂.X : ZMod p) = (lam : ZMod p) * (p₁.X : ZMod p) ∧
    (p₂.Y : ZMod p) = (lam : ZMod p) * (p₁.Y : ZMod p) ∧
    (p₂.Z : ZMod p) = (lam : ZMod p) * (p₁.Z : ZMod p)

@[refl] lemma ProjEq.refl (q : EdPoint) : ProjEq q q :=
  ⟨1, by simp, by simp, by simp⟩

@[symm] lemma ProjEq.symm {p₁ p₂ : EdPoint} (h : ProjEq p₁ p₂) :
    ProjEq p₂ p₁ := by
  obtain ⟨lam, hx, hy, hz⟩ := h
  refine ⟨lam⁻¹, ?_, ?_, ?_⟩
  · -- Goal: p₁.X = lam⁻¹.val * p₂.X.  Substitute hx, then use lam⁻¹·lam = 1.
    calc (p₁.X : ZMod p)
        = 1 * (p₁.X : ZMod p) := by ring
      _ = ((lam⁻¹ : (ZMod p)ˣ) : ZMod p) * ((lam : ZMod p) * (p₁.X : ZMod p)) := by
          rw [← Units.inv_mul lam, mul_assoc]
      _ = ((lam⁻¹ : (ZMod p)ˣ) : ZMod p) * (p₂.X : ZMod p) := by rw [← hx]
  · calc (p₁.Y : ZMod p)
        = 1 * (p₁.Y : ZMod p) := by ring
      _ = ((lam⁻¹ : (ZMod p)ˣ) : ZMod p) * ((lam : ZMod p) * (p₁.Y : ZMod p)) := by
          rw [← Units.inv_mul lam, mul_assoc]
      _ = ((lam⁻¹ : (ZMod p)ˣ) : ZMod p) * (p₂.Y : ZMod p) := by rw [← hy]
  · calc (p₁.Z : ZMod p)
        = 1 * (p₁.Z : ZMod p) := by ring
      _ = ((lam⁻¹ : (ZMod p)ˣ) : ZMod p) * ((lam : ZMod p) * (p₁.Z : ZMod p)) := by
          rw [← Units.inv_mul lam, mul_assoc]
      _ = ((lam⁻¹ : (ZMod p)ˣ) : ZMod p) * (p₂.Z : ZMod p) := by rw [← hz]

lemma ProjEq.trans {p₁ p₂ p₃ : EdPoint}
    (h₁₂ : ProjEq p₁ p₂) (h₂₃ : ProjEq p₂ p₃) :
    ProjEq p₁ p₃ := by
  obtain ⟨lam₁, hx₁, hy₁, hz₁⟩ := h₁₂
  obtain ⟨lam₂, hx₂, hy₂, hz₂⟩ := h₂₃
  refine ⟨lam₂ * lam₁, ?_, ?_, ?_⟩
  · rw [hx₂, hx₁, Units.val_mul]; ring
  · rw [hy₂, hy₁, Units.val_mul]; ring
  · rw [hz₂, hz₁, Units.val_mul]; ring

/-- `Setoid` instance packaging the equivalence lemmas. -/
instance : Setoid EdPoint where
  r := ProjEq
  iseqv := ⟨ProjEq.refl, ProjEq.symm, ProjEq.trans⟩

end EdPoint
end LeanCrypto.Curve.Edwards25519
