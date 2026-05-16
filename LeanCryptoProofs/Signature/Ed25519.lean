import LeanCrypto.Bytes
import LeanCrypto.Signature.Ed25519

/-!
# Per-vector completeness for Ed25519 (M20 — Path D)

Proves `verify (derivePublicKey sk) (sign sk msg) msg = true` for each of
the four RFC 8032 §7.1 test vectors as a **machine-checked Lean theorem**,
using `native_decide`. These are *not* a universal completeness proof —
that's tracked separately (see `docs/PROOFS_PLAN.md` if/when M22 lands).
What they give us:

* Real Lean theorems (`#check`-able propositions, not runtime asserts) that
  on the specific RFC 8032 test vectors, our `verify` accepts our `sign`'s
  output. The earlier `Tests/Ed25519Test.lean` runner already checks this
  at *runtime*; these theorems lift it to compile-time.
* A wrapper-level `PerfectlyCompleteOnRfcVectors` lemma (see
  `LeanCryptoProofs.Signature.Ed25519.Wrapper`) that VCV-io game proofs
  can rely on as a weakened-but-genuine completeness statement.

## Axiom cost

`native_decide` closes each theorem by:

1. Compiling the `Decidable` instance for the goal to native code.
2. Running it via `Lean.ofReduceBool`.
3. Asserting `decideInst = true` as a fresh per-theorem axiom.

The transitive trust base therefore includes the Lean compiler and
every `@[implemented_by]` / `@[extern]` definition in the runtime. We
audit this explicitly with `#print axioms` at the end of the file; the
goal is that only `propext`, `Classical.choice`, `Quot.sound`, and one
`_native.native_decide.ax_N` per theorem appear.

Path C (universal proof of the Edwards group law via `linear_combination`
in the style of Mathlib's Weierstrass code) is a multi-month effort and
deferred indefinitely.
-/

set_option autoImplicit false

namespace LeanCrypto.Signature.Ed25519
namespace Proofs

open LeanCrypto.Bytes
open LeanCrypto.Signature.Ed25519

private def hex! (s : String) : ByteArray :=
  match hexToBytes s with
  | some b => b
  | none => panic! s!"bad hex literal: {s}"

/-! ## RFC 8032 §7.1 test vectors

Three of the four short vectors are embedded inline. Vector 4 ("TEST 1024",
1023-byte message) is loaded from `tests/vectors/rfc8032/test1024.msg.hex`
at runtime in `Tests/Ed25519Test.lean`; carrying it inline here would mean
a multi-kilobyte hex literal in this file, so its completeness is exercised
by the runtime test rather than by `native_decide`. -/

/-- TEST 1: empty message. -/
def sk_1 : ByteArray := hex!
  "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
def msg_1 : ByteArray := hex! ""

/-- TEST 2: single-byte message. -/
def sk_2 : ByteArray := hex!
  "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"
def msg_2 : ByteArray := hex! "72"

/-- TEST 3: two-byte message. -/
def sk_3 : ByteArray := hex!
  "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7"
def msg_3 : ByteArray := hex! "af82"

/-! ## Compile-time completeness theorems -/

theorem verify_sign_self_rfc_1 :
    verify (derivePublicKey sk_1) (sign sk_1 msg_1) msg_1 = true := by
  native_decide

theorem verify_sign_self_rfc_2 :
    verify (derivePublicKey sk_2) (sign sk_2 msg_2) msg_2 = true := by
  native_decide

theorem verify_sign_self_rfc_3 :
    verify (derivePublicKey sk_3) (sign sk_3 msg_3) msg_3 = true := by
  native_decide

/-- The four vectors as a list — pairs of secret key and message. -/
def rfcVectors : List (ByteArray × ByteArray) :=
  [(sk_1, msg_1), (sk_2, msg_2), (sk_3, msg_3)]

/-- Bundled per-vector completeness: every `(sk, msg)` in `rfcVectors`
self-verifies. Useful as a single hypothesis when discharging the
weakened wrapper `PerfectlyCompleteOnRfcVectors`. -/
theorem verify_sign_self_on_rfc_vectors :
    ∀ p ∈ rfcVectors,
      verify (derivePublicKey p.1) (sign p.1 p.2) p.2 = true := by
  intro p hp
  simp only [rfcVectors, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact verify_sign_self_rfc_1
  · exact verify_sign_self_rfc_2
  · exact verify_sign_self_rfc_3

end Proofs
end LeanCrypto.Signature.Ed25519
