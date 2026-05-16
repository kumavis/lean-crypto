# `lean-crypto` — Proof-work roadmap (M19–M24)

The VCV-io wrapper (M12–M18) ships a working `SignatureAlg` instance for
Ed25519 but defers the algebraic-correctness proof of the verify
equation. M19–M24 build the foundations and probe how close we can get
to universal `verify_sign_self` with Lean 4 + Mathlib v4.29.0's current
tactic infrastructure.

The proof work lives in a separate `lean_lib LeanCryptoProofs` (alongside
`LeanCrypto` and `LeanCryptoVCVio`). It depends on Mathlib — core
`LeanCrypto/` stays Mathlib-free as before.

## Status snapshot

| Milestone | Deliverable | Outcome |
|-----------|-------------|---------|
| **M19** | `ProjEq` Setoid + `Fp25519` ↔ `ZMod p` cast lemmas | ✅ landed |
| **M20** | `verify_sign_self` for RFC 8032 §7.1 vectors via `native_decide` | ✅ landed (3 theorems + bundle, +3 axioms) |
| **M21** | Spike: `add_comm` via `ring` | ✅ landed |
| **M22** | `add_zero_left/right_crossEq` via `CrossEq` | ✅ landed |
| **M23** | `add_negate_cancel_crossEq` with curve-equation hypothesis | ✅ landed |
| **M24** | Spike: `add_assoc_crossEq` via `grobner` | ❌ deferred — see findings |

Universal `verify_sign_self` is **deferred indefinitely**. The associativity
of `add` modulo `CrossEq` exceeds what Lean's current `grind`-backed
`grobner` heuristic can dispatch within reasonable budgets, and computing
a witness manually is multi-week work that hasn't been justified by a
downstream proof obligation.

---

## M19 · `ProjEq` Setoid + cast lemmas

Foundation for any algebraic reasoning over edwards25519. The challenge:
our `Fp = Nat` (modular operations via `% p`) doesn't carry a ring
structure directly; everything has to flow through `ZMod p` to use
`ring`, `linear_combination`, etc.

**Landed** in `LeanCryptoProofs/Edwards25519/ProjEq.lean`:

- `castZMod_fp25519_add : ((Fp25519.add a b : Nat) : ZMod p) = (a : ZMod p) + (b : ZMod p)`
- `castZMod_fp25519_mul : ((Fp25519.mul a b : Nat) : ZMod p) = (a : ZMod p) * (b : ZMod p)`
- `ProjEq p₁ p₂ := ∃ (λ : (ZMod p)ˣ), X₂ = λ·X₁ ∧ Y₂ = λ·Y₁ ∧ Z₂ = λ·Z₁`
- `Setoid EdPoint` (refl via λ=1, symm via λ⁻¹, trans via λ₁·λ₂)

The Units-quantified `ProjEq` is great for transitivity but inconvenient
when the natural projective witness involves products like `4·Z` that
need `Z` to be a unit. M22 introduces `CrossEq` as a sibling for those.

---

## M20 · `native_decide` per-RFC-vector completeness

A pragmatic completeness story for the RFC 8032 §7.1 vectors. Each
theorem is a real Lean proposition (not a runtime assertion) closed by
`native_decide`, which compiles the `Decidable` instance to native code,
runs it, and asserts the result as a fresh axiom of the proof.

**Landed** in `LeanCryptoProofs/Signature/Ed25519.lean`:

- `verify_sign_self_rfc_1`, `verify_sign_self_rfc_2`,
  `verify_sign_self_rfc_3` — each `∼1.2s` `native_decide` elaboration.
- `rfcVectors : List (ByteArray × ByteArray)` and bundled
  `verify_sign_self_on_rfc_vectors : ∀ p ∈ rfcVectors, ...`.

**Wrapper-level** lemma in `LeanCryptoProofs/VCVio/Ed25519.lean`:

- `ed25519_completes_on_rfc_vectors : ∀ p ∈ rfcVectors,
    (do let pk := …; let sig ← ed25519.sign …; ed25519.verify pk … sig)
      = pure true`

This is the weakened-but-genuine `PerfectlyComplete`-shaped statement
that downstream VCV-io game proofs can rely on.

**Axiom cost** (audited via `#print axioms`): each theorem adds one
`_native_decide.ax_N` axiom on top of the standard Lean trust base
(`propext`, `Classical.choice`, `Quot.sound`). The bundled lemma
transitively trusts all three. Mathlib explicitly forbids `native_decide`
via its style linter — we're outside Mathlib, so this is a documented
trade-off.

**Why plain `decide` doesn't work:** the Ed25519 stack is built on
`Id.run do { for h : i in [:n] do ... }`, which desugars to
`ForIn'.forIn'` with opaque proof-carrying loop hypotheses that the
kernel reducer can't unfold. `decide` fails *structurally* (in ~1s,
not via timeout) — there's no kernel-reduction path through the
runtime. Only `native_decide`, which compiles the decidability check
to native code, gets through.

---

## M21 · `add_comm_projEq` via `ring`

The first non-trivial polynomial-identity lemma. The 2008-HWCD-3
addition formula is syntactically symmetric in its two arguments, so
after pushing casts through the `castZMod_fp25519_*` simp set, `ring`
closes the equality with `λ = 1` as the `ProjEq` witness.

**Landed** in `LeanCryptoProofs/Edwards25519/AddSpike.lean`:

- `castZMod_fp25519_sub` — extends the M19 cast surface to subtraction
  (needed because the HWCD formula uses `Fp25519.sub` in three sub-terms).
- `ProjEq.add_comm_projEq : ProjEq (add p₁ p₂) (add p₂ p₁)`.

This validated the path: Mathlib's `EllipticCurve/Projective/Formula.lean`
idiom transfers cleanly to our setup. **The probe took ~1 hour total to
land** (1.1s elaboration).

---

## M22 · `add_zero_*` via `CrossEq`

The first lemmas where the natural witness *isn't* `λ = 1`. For
`add identity P ≡_proj P`, the implicit witness is `4·Z`, which needs
`Z` and `4` to both be units in `ZMod p`. Without `Fact (Nat.Prime p)`
(itself a multi-day proof for `p = 2²⁵⁵−19`), constructing this unit
is awkward.

**Workaround:** define a sibling notion `CrossEq` using the cross-product
form (`X₁·Z₂ = X₂·Z₁ ∧ Y₁·Z₂ = Y₂·Z₁` in `ZMod p`) — which is exactly
what the runtime `projEq` Bool inside `Ed25519.verify` checks. `CrossEq`
is reflexive and symmetric *without* preconditions; transitivity is
conditional on a unit `Z` somewhere, which we don't need for the M22
lemmas. The proper `ProjEq` implies `CrossEq` (`ProjEq.cross`), so M19
work flows through.

**Landed** in `LeanCryptoProofs/Edwards25519/GroupLaws.lean`:

- `CrossEq` definition + `refl`, `symm`.
- `ProjEq.cross : ProjEq → CrossEq` (M19 → M22 bridge).
- `OnCurve q := -X² + Y² = Z² + d·T²` in `ZMod p` (curve equation in
  extended coordinates).
- `add_zero_left_crossEq : CrossEq (add identity q) q`.
- `add_zero_right_crossEq : CrossEq (add q identity) q`.

Both `add_zero_*` lemmas close via `simp + ring` without needing the
curve equation as a hypothesis.

---

## M23 · `add_negate_cancel_crossEq` (curve-equation-conditioned)

First lemma in this file requiring `OnCurve q` as a hypothesis. The
Y-component reduces (after expansion) to

> 4·(Z² − d·T²) · ((Y² − X²) − (Z² + d·T²)) = 0

where the bracketed factor is `(LHS − RHS)` of `OnCurve`. The
`linear_combination` witness is `4·(Z² − d·T²)`.

**Three pieces of plumbing required**, none of which the M22 attempt
had right:

1. **`push_cast` after the initial `simp`.** The post-simp form has
   un-normalised `↑2` / `↑(2·d)` casts that `linear_combination`'s
   coefficient inference doesn't manipulate; `push_cast` normalises
   them so the residual closes by `ring`.
2. **`(4 : ZMod p)` coefficient ascription.** Without the type
   annotation, Lean parses the outer `4` as `Nat`, and
   `linear_combination` strips it (the diagnostic warning was *"this
   constant has no effect on the linear combination"*).
3. **`linear_combination hq` (not `linarith`).** The trivial
   rearrangement from `-X² + Y² = Z² + d·T²` to `Y² − X² = Z² + d·T²`
   needs a ring tactic; `linarith` doesn't apply over `ZMod p`.

**Landed** in `GroupLaws.lean`:

- `add_negate_cancel_crossEq : OnCurve q → CrossEq (add q (negate q)) identity`

Closes in 1.3s. **Implication for the universal proof:** the
`linear_combination` pattern from Mathlib's Weierstrass code transfers
cleanly to our setup once the cast plumbing is right. Per-lemma effort
is minutes-to-hours, not days. The M21 4–8 person-months estimate from
the external survey looks pessimistic by a factor of ~3-5 for the
"easy" lemmas of this shape — but associativity is a different beast
(see M24).

---

## M24 (spike) · `add_assoc_crossEq` — not closed

The next natural lemma after M23 is associativity:

> `add (add p₁ p₂) p₃ ≡_cross add p₁ (add p₂ p₃)`,
> given `OnCurve p₁`, `OnCurve p₂`, `OnCurve p₃`.

A polynomial identity in 12 variables conditioned by three curve
equations.

**Probed** with the same `simp + push_cast + grobner` pipeline that
closed `add_negate_cancel_crossEq`. **Result:** `grobner` hits Lean's
E-matching round limit + `maxRecDepth` before completing. The
diagnostic output confirms it correctly identified all three OnCurve
hypotheses as facts in distinct equivalence classes, but couldn't
synthesise a Gröbner-style witness within the default heuristic budget.

Raising `maxHeartbeats` to 1,000,000 did not help.

Closing this lemma would require either:

* hand-computing a `linear_combination` witness across the three
  hypotheses (the Fiat-Crypto `nsatz` / Hales–Raya elementary-polynomial-
  division precedents both effectively do this); or
* a more capable Gröbner-basis backend than Lean's current `grind`-
  based heuristics provide.

Both options are out of scope for this PR.

**Per the M21 external survey:** every project at HACL\*/s2n-bignum/
EasyCrypt scale axiomatises the group structure here. The canonical
completeness statements for `ed25519` in this codebase remain M20's
per-RFC-vector `native_decide` theorems and the wrapper-level
`ed25519_completes_on_rfc_vectors`.

---

## Cross-cutting status

- **No `sorry`/`partial`/`unsafe`/`extern`** in any of the proof
  modules. CI's forbidden-tokens grep covers `LeanCryptoProofs/`.
- **Core `LeanCrypto/**.lean` stays Mathlib-free**; only the proofs
  library imports Mathlib (mirroring the wrapper library's posture).
- **Axiom inventory:** standard Lean (`propext`, `Classical.choice`,
  `Quot.sound`) plus three `_native_decide.ax_N` axioms — one per
  M20 RFC-vector theorem. No other axioms beyond Mathlib's own.
- **Build time** (`lake build LeanCryptoProofs`, warm): ~2 seconds,
  dominated by the `native_decide` elaborations.

## If we ever come back to associativity

The path forward is one of:

1. **Hand witness.** Compute the `linear_combination` coefficients
   for `add_assoc_crossEq` over the three OnCurve hypotheses by hand
   (or via an offline Gröbner basis tool, then transcribe the witness
   into Lean). Effort: 1-2 weeks.
2. **Port Fiat-Crypto.** Their `Curves/Edwards/AffineProofs.v` proves
   affine associativity via `nsatz`; `Curves/Edwards/XYZT/Basic.v`
   transfers to extended coords via an explicit homomorphism. Effort:
   the agent survey estimated 1-2 person-months for the affine port +
   2-4 weeks for the XYZT transfer.
3. **Port Hales–Raya.** Isabelle/HOL formalisation (arXiv:2004.12030)
   proves associativity *elementarily* via polynomial division. The
   math is the cleanest blueprint; Lean's `polyrith`/`linear_combination`
   suit the style. Effort: similar to Fiat-Crypto.

In all three cases the order-of-`basePoint` fact (`ℓ·B = identity`) is
a separate problem — typically dispatched via `native_decide` on a
fixed-input computation, with the same axiomatic trade-off as M20.
