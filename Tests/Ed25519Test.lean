import LeanCrypto.Bytes
import LeanCrypto.Signature.Ed25519

open LeanCrypto.Bytes
open LeanCrypto.Signature.Ed25519

/-! M9 test runner: RFC 8032 §7.1 vectors for derivePublicKey / sign /
verify / verifyZip215, plus tamper-rejection. -/

structure RfcVector where
  name : String
  sk   : ByteArray
  pk   : ByteArray
  msg  : ByteArray
  sig  : ByteArray

private def hex! (s : String) : ByteArray :=
  match hexToBytes s with
  | some b => b
  | none => panic! s!"bad hex literal: {s}"

/-- Hand-typed from RFC 8032 §7.1.

Test 1024's message comes verbatim from the RFC; the sk/pk/sig values
come from the same section. -/
def rfcVectors : List RfcVector := [
  { name := "TEST 1 (empty)"
    sk  := hex! "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
    pk  := hex! "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
    msg := hex! ""
    sig := hex! "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b" },
  { name := "TEST 2 (1 byte)"
    sk  := hex! "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"
    pk  := hex! "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c"
    msg := hex! "72"
    sig := hex! "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00" },
  { name := "TEST 3 (2 bytes)"
    sk  := hex! "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7"
    pk  := hex! "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025"
    msg := hex! "af82"
    sig := hex! "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a" }
]

/-- TEST 1024 (RFC 8032 §7.1, 1023-byte message). The message is loaded
from a file rather than embedded inline to keep the Lean source readable. -/
def test1024Vector : IO RfcVector := do
  let msgHex ← IO.FS.readFile "tests/vectors/rfc8032/test1024.msg.hex"
  match hexToBytes msgHex.trimAscii.toString with
  | none => throw <| IO.userError "test1024.msg.hex: not valid hex"
  | some msg =>
    let v : RfcVector :=
      { name := "TEST 1024 (1023-byte msg)"
        sk  := hex! "f5e5767cf153319517630f226876b86c8160cc583bc013744c6bf255f5cc0ee5"
        pk  := hex! "278117fc144c72340f67d0f2316e8386ceffbf2b2428c9c51fef7c597f1d426e"
        msg := msg
        sig := hex! "0aab4c900501b3e24d7cdf4663326a3a87df5e4843b2cbdb67cbf6e460fec350aa5371b1508f9f4528ecea23c436d94b5e8fcd4f681e30a6ac00a9704a188a03" }
    return v

abbrev TestM := StateM (Nat × Option String)

def ok : TestM Unit := modify fun (n, e) => (n + 1, e)

def fail (msg : String) : TestM Unit :=
  modify fun (n, e) => (n, e.orElse (fun () => some msg))

def checkEq [BEq α] [ToString α] (name : String) (expected actual : α) : TestM Unit :=
  if expected == actual then ok
  else fail s!"{name}: expected {expected}, got {actual}"

/-- Flip a single bit in a fresh copy of `b` at byte index `i`. -/
def flipByte (b : ByteArray) (i : Nat) : ByteArray :=
  b.set! i ((b.get! i) ^^^ 0x01)

def tests (extra : List RfcVector) : TestM Unit := do
  for v in rfcVectors ++ extra do
    -- derivePublicKey
    let derivedPk := derivePublicKey v.sk
    checkEq s!"{v.name} derivePublicKey" (bytesToHex v.pk) (bytesToHex derivedPk)
    -- sign
    let producedSig := sign v.sk v.msg
    checkEq s!"{v.name} sign" (bytesToHex v.sig) (bytesToHex producedSig)
    -- verify (strict)
    if !verify v.pk v.sig v.msg then
      fail s!"{v.name} verify (strict) rejected a valid signature"
    else ok
    -- verifyZip215 (also accepts canonical valid signatures)
    if !verifyZip215 v.pk v.sig v.msg then
      fail s!"{v.name} verifyZip215 rejected a valid signature"
    else ok
    -- Tamper with the sig (flip bit 0 of byte 0)
    let badSig := flipByte v.sig 0
    if verify v.pk badSig v.msg then
      fail s!"{v.name} verify accepted tampered sig"
    else ok
    if verifyZip215 v.pk badSig v.msg then
      fail s!"{v.name} verifyZip215 accepted tampered sig"
    else ok
    -- Tamper with the msg (only for non-empty messages)
    if v.msg.size > 0 then
      let badMsg := flipByte v.msg 0
      if verify v.pk v.sig badMsg then
        fail s!"{v.name} verify accepted with tampered msg"
      else ok
      if verifyZip215 v.pk v.sig badMsg then
        fail s!"{v.name} verifyZip215 accepted with tampered msg"
      else ok

def main : IO UInt32 := do
  let v1024 ← test1024Vector
  let ((), (n, err)) := (tests [v1024]).run (0, none)
  match err with
  | some msg => IO.eprintln s!"FAIL {msg} (after {n} passing)"; return 1
  | none => IO.println s!"OK {n} vectors"; return 0
