import LeanCrypto.Bytes
import LeanCrypto.Hash.SHA512
import LeanCrypto.Field.Fp25519
import LeanCrypto.Field.ScalarL
import LeanCrypto.Curve.Edwards25519

/-!
# `LeanCrypto.Signature.Ed25519`

Pure-EdDSA over edwards25519 with SHA-512 (RFC 8032 §5.1).

* `derivePublicKey : ByteArray → ByteArray` — 32-byte secret → 32-byte public
* `sign : ByteArray → ByteArray → ByteArray` — sk, msg → 64-byte signature
* `verify : ByteArray → ByteArray → ByteArray → Bool` — strict RFC 8032
* `verifyZip215` — noble-compatible: accepts non-canonical encodings and
  small-order public keys; still requires `S < ℓ`

Both verify modes share the cofactored equation `[8](S·B) = [8](R + k·A)`
and the `S < ℓ` malleability check. They differ in:

* canonical encoding strictness (strict rejects `y ≥ p`; ZIP-215 reduces y
  mod p and accepts)
* small-order public-key rejection (strict requires `[8] A ≠ 0`; ZIP-215
  allows it). -/

set_option autoImplicit false

namespace LeanCrypto.Signature.Ed25519

open LeanCrypto.Bytes
open LeanCrypto.Field.Fp25519
open LeanCrypto.Curve.Edwards25519
open LeanCrypto.Curve.Edwards25519.EdPoint

-- Disambiguate names from the multiple opened namespaces.
private abbrev Scalar := LeanCrypto.Field.ScalarL.Scalar
private def L : Nat := LeanCrypto.Field.ScalarL.L
private def reduceL : Nat → Scalar := LeanCrypto.Field.ScalarL.reduce
private def addL : Scalar → Scalar → Scalar := LeanCrypto.Field.ScalarL.add
private def mulL : Scalar → Scalar → Scalar := LeanCrypto.Field.ScalarL.mul
private def reduce512Bit : ByteArray → Scalar := LeanCrypto.Field.ScalarL.reduce512Bit
private def sha512 : ByteArray → ByteArray := LeanCrypto.Hash.SHA512.sha512

/-! ## Helpers -/

/-- RFC 8032 §5.1.5 clamp: clear bits 0, 1, 2 of byte 0 and bit 255; set
bit 254. Operates on a 32-byte input; returns the clamped scalar as a Nat
(may exceed ℓ — that's intentional). -/
private def clampScalar (h32 : ByteArray) : Nat := Id.run do
  let mut bytes := h32
  let b0  := bytes.get! 0
  let b31 := bytes.get! 31
  bytes := bytes.set! 0  (b0  &&& 0xf8)
  bytes := bytes.set! 31 ((b31 &&& 0x7f) ||| 0x40)
  return loadU256LE! bytes 0

/-- Projective equality: `(X₁:Y₁:Z₁) = (X₂:Y₂:Z₂)` iff `X₁·Z₂ = X₂·Z₁` and
`Y₁·Z₂ = Y₂·Z₁`. Avoids a `Z`-inversion per comparison. -/
private def projEq (p q : EdPoint) : Bool :=
  decide (mul p.X q.Z = mul q.X p.Z) && decide (mul p.Y q.Z = mul q.Y p.Z)

/-! ## Sign / public-key derivation -/

/-- Derive the 32-byte public key from a 32-byte secret. The
precondition `sk.size = 32` is enforced with a runtime panic — passing
a different length is almost always a caller bug (e.g. confusing the
32-byte seed with a 64-byte expanded `sk ‖ pk` keypair, a frequent
cross-library footgun). Refusing loudly is safer than returning a junk
public key that no peer will verify against. -/
def derivePublicKey (sk : ByteArray) : ByteArray :=
  if sk.size != 32 then
    panic! s!"Ed25519.derivePublicKey: sk.size = {sk.size}, expected 32"
  else
    let h := sha512 sk
    let s := clampScalar (h.extract 0 32)
    let A := smul s basePoint
    encode A

/-- Sign `msg` with secret `sk`. Returns 64 bytes.

The precondition `sk.size = 32` is enforced with a runtime panic — see
`derivePublicKey` for the rationale. -/
def sign (sk msg : ByteArray) : ByteArray :=
  if sk.size != 32 then
    panic! s!"Ed25519.sign: sk.size = {sk.size}, expected 32"
  else
    let h := sha512 sk
    let s := clampScalar (h.extract 0 32)
    let pre := h.extract 32 64
    let A := smul s basePoint
    let encA := encode A
    let r := reduce512Bit (sha512 (pre ++ msg))
    let R := smul r basePoint
    let encR := encode R
    let k := reduce512Bit (sha512 (encR ++ encA ++ msg))
    let S := addL r (mulL k (reduceL s))
    encR ++ storeU256LE S

/-! ## Verify -/

inductive VerifyMode where
  | strict   -- RFC 8032 §5.1.7 default
  | zip215   -- noble-ed25519 default
  deriving Inhabited, BEq

/-- Decode a 32-byte encoded point, dispatching on `mode` for whether to
accept non-canonical y-coordinates. -/
private def decodeForMode (mode : VerifyMode) (bs : ByteArray) : Option EdPoint :=
  match mode with
  | .strict => decode bs
  | .zip215 =>
      if bs.size != 32 then none
      else
        -- Reduce y mod p, then run the standard decode with the reduced
        -- value re-encoded into a canonical 32-byte form.
        let b31 := bs.get! 31
        let signBit := (b31 >>> 7) &&& 1
        let bs' := bs.set! 31 (b31 &&& 0x7f)
        let yRaw := loadU256LE! bs' 0
        let yCanon := yRaw % p
        let bsCanon := storeU256LE yCanon
        let bsCanon := bsCanon.set! 31 (bsCanon.get! 31 ||| (signBit <<< 7))
        decode bsCanon

/-- Shared verify body. -/
private def verifyWith (mode : VerifyMode) (pk sig msg : ByteArray) : Bool :=
  if pk.size != 32 || sig.size != 64 then false
  else
    let encR := sig.extract 0 32
    let sBytes := sig.extract 32 64
    let S := loadU256LE! sBytes 0
    if S ≥ L then false
    else
      match decodeForMode mode encR, decodeForMode mode pk with
      | some R, some A =>
          -- Strict mode also rejects small-order public keys.
          let smallOrderOk :=
            match mode with
            | .strict => !projEq (smul 8 A) identity
            | .zip215 => true
          if !smallOrderOk then false
          else
            let k := reduce512Bit (sha512 (encR ++ pk ++ msg))
            let lhs := smul 8 (smul S basePoint)
            let rhs := smul 8 (add R (smul k A))
            projEq lhs rhs
      | _, _ => false

/-- Strict RFC 8032 verify (default). -/
def verify (pk sig msg : ByteArray) : Bool := verifyWith .strict pk sig msg

/-- ZIP-215 verify. Accepts non-canonical encodings and small-order
public keys; still rejects `S ≥ ℓ`. -/
def verifyZip215 (pk sig msg : ByteArray) : Bool := verifyWith .zip215 pk sig msg

end LeanCrypto.Signature.Ed25519
