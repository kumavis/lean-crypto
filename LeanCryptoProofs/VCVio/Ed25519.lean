import LeanCryptoVCVio.Signature.Ed25519
import LeanCryptoProofs.Signature.Ed25519

/-!
# Wrapper-level completeness lemma for `ed25519` on the RFC 8032 vectors

Connects the per-vector core theorems in
`LeanCryptoProofs.Signature.Ed25519` to the `SignatureAlg`-level pipeline
`ed25519.sign` / `ed25519.verify` exposed by the VCV-io wrapper.

This is the weakened-but-genuine completeness statement that any
downstream VCV-io game proof can rely on: for every `(sk, msg)` in the
RFC 8032 §7.1 test vectors, the SignatureAlg's sign-then-verify pipeline
returns `pure true` definitionally.

For the universal completeness statement (quantified over all `(sk, msg)`)
see the `M22+` notes in the wrapper plan: it requires the algebraic
correctness of the 2008-HWCD addition formula, deliberately out of scope
for this PR.
-/

set_option autoImplicit false

namespace LeanCryptoVCVio
namespace Ed25519Proofs

open LeanCrypto.Signature.Ed25519
open LeanCrypto.Signature.Ed25519.Proofs

/-- For each `(sk, msg)` in `Proofs.rfcVectors`, threading the pair
through the wrapper's `ed25519.sign` and then `ed25519.verify` yields
`pure true` in `ProbComp Bool`. -/
theorem ed25519_completes_on_rfc_vectors :
    ∀ p ∈ rfcVectors,
      (do let pk := derivePublicKey p.1
          let sig ← ed25519.sign pk p.1 p.2
          ed25519.verify pk p.2 sig)
        = (pure true : ProbComp Bool) := by
  intro p hp
  -- `ed25519.sign pk sk msg = pure (sign sk msg)` and similarly for verify;
  -- both are `rfl` simp lemmas. The `bind ∘ pure` collapses, then we
  -- reduce the inner verify-of-sign on this specific (sk, msg) to `true`
  -- via the native_decide theorem bundled in `verify_sign_self_on_rfc_vectors`.
  simp only [ed25519_sign, ed25519_verify, pure_bind]
  rw [verify_sign_self_on_rfc_vectors p hp]

end Ed25519Proofs
end LeanCryptoVCVio
