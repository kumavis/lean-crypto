import LeanCryptoVCVio.Prelude

/-!
# Ed25519 with SHA-512 modeled as a Random Oracle

Re-implements Ed25519's `derivePublicKey`, `sign`, and `verify` as
`OracleComp sha512ROSpec`-valued functions, replacing every internal
`LeanCrypto.Hash.SHA512.sha512` call with a `query () _` against an
abstract hash oracle. Sampling-side randomness for `keygen` is **not**
included here — assembling the full `SignatureAlg` over a combined
`unifSpec + sha512ROSpec` spec is M17 territory; M16 ships the building
blocks and verifies them by instantiating the oracle with real SHA-512
and round-tripping the RFC 8032 §7.1 vectors.

`PerfectlyComplete` for the ROM variant is deferred for the same reason
as the non-ROM `ed25519` instance (M15): the underlying algebraic
identity `verify (derivePublicKey sk) (sign sk msg) msg = true` is the
correctness theorem of the scheme itself.
-/

namespace LeanCryptoVCVio

open LeanCrypto.Bytes
open LeanCrypto.Field.Fp25519 (p)
open LeanCrypto.Curve.Edwards25519
open LeanCrypto.Curve.Edwards25519.EdPoint
open OracleComp (query)

/-- SHA-512 modeled as a single random oracle: input `ByteArray`, output
`ByteArray`. (Same shape as `ByteArray →ₒ ByteArray`.) -/
def sha512ROSpec : OracleSpec ByteArray := fun _ => ByteArray

/-- Local copy of the RFC 8032 §5.1.5 clamp; the LeanCrypto core keeps it
`private`, so we re-state it here verbatim. -/
private def clampScalar (h32 : ByteArray) : Nat := Id.run do
  let mut bytes := h32
  let b0  := bytes.get! 0
  let b31 := bytes.get! 31
  bytes := bytes.set! 0  (b0  &&& 0xf8)
  bytes := bytes.set! 31 ((b31 &&& 0x7f) ||| 0x40)
  return loadU256LE! bytes 0

/-- Local copy of `projEq` from the core Ed25519 module. -/
private def projEq (a b : EdPoint) : Bool :=
  decide (LeanCrypto.Field.Fp25519.mul a.X b.Z =
          LeanCrypto.Field.Fp25519.mul b.X a.Z) &&
  decide (LeanCrypto.Field.Fp25519.mul a.Y b.Z =
          LeanCrypto.Field.Fp25519.mul b.Y a.Z)

private def reduceL := LeanCrypto.Field.ScalarL.reduce
private def addL := LeanCrypto.Field.ScalarL.add
private def mulL := LeanCrypto.Field.ScalarL.mul
private def reduce512Bit := LeanCrypto.Field.ScalarL.reduce512Bit
private def Lconst := LeanCrypto.Field.ScalarL.L

/-- `derivePublicKey` with SHA-512 abstracted as an oracle query. -/
def derivePublicKeyROM (sk : ByteArray) : OracleComp sha512ROSpec ByteArray := do
  let h ← query (spec := sha512ROSpec) sk
  let s := clampScalar (h.extract 0 32)
  let A := smul s basePoint
  return encode A

/-- `sign` with SHA-512 abstracted as an oracle query. -/
def signROM (sk msg : ByteArray) : OracleComp sha512ROSpec ByteArray := do
  let h ← query (spec := sha512ROSpec) sk
  let s := clampScalar (h.extract 0 32)
  let pre := h.extract 32 64
  let A := smul s basePoint
  let encA := encode A
  let h2 ← query (spec := sha512ROSpec) (pre ++ msg)
  let r := reduce512Bit h2
  let R := smul r basePoint
  let encR := encode R
  let h3 ← query (spec := sha512ROSpec) (encR ++ encA ++ msg)
  let k := reduce512Bit h3
  let S := addL r (mulL k (reduceL s))
  return encR ++ storeU256LE S

/-- Strict-mode `verify` with SHA-512 abstracted as an oracle query.
Mirrors `verifyWith .strict` from the core module. -/
def verifyROM (pk sig msg : ByteArray) : OracleComp sha512ROSpec Bool := do
  if pk.size != 32 || sig.size != 64 then return false
  else
    let encR := sig.extract 0 32
    let sBytes := sig.extract 32 64
    let S := loadU256LE! sBytes 0
    if S ≥ Lconst then return false
    else
      match decode encR, decode pk with
      | some R, some A =>
          -- Strict mode: reject small-order public keys.
          if projEq (smul 8 A) identity then return false
          else
            let h ← query (spec := sha512ROSpec) (encR ++ pk ++ msg)
            let k := reduce512Bit h
            let lhs := smul 8 (smul S basePoint)
            let rhs := smul 8 (add R (smul k A))
            return projEq lhs rhs
      | _, _ => return false

/-- Concrete `QueryImpl` that instantiates the SHA-512 random oracle with
the real `LeanCrypto.Hash.SHA512.sha512`. Lets us test that the ROM
variant computes the same answer as the standard scheme when the oracle
is honest. -/
@[reducible] def sha512Impl : QueryImpl sha512ROSpec Id :=
  fun (input : ByteArray) => pure (LeanCrypto.Hash.SHA512.sha512 input)

end LeanCryptoVCVio
