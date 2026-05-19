import LeanCryptoVCVio

open LeanCrypto.Bytes
open LeanCrypto.Signature.Ed25519
open LeanCryptoVCVio

/-! M15 acceptance: the `ed25519` `SignatureAlg` instance routes `sign` and
`verify` through `LeanCrypto`'s pure functions byte-for-byte.

We don't exercise `keygen` here because that would require an interpreter
for `unifSpec` that yields the RFC vector's 32-byte seed exactly — fragile
and not where the value lies. Instead we drive `sign` and `verify` directly
through `simulateQ` with the trivial `constUnifImpl` (returns 0 to every
uniform query; sign/verify don't query under the hood, so the impl is
irrelevant) and check byte-equality with the RFC 8032 §7.1 vectors. -/

private def hex! (s : String) : ByteArray :=
  match hexToBytes s with
  | some b => b
  | none => panic! s!"bad hex literal: {s}"

structure RfcVec where
  name : String
  sk   : ByteArray
  pk   : ByteArray
  msg  : ByteArray
  sig  : ByteArray

def rfcVectors : List RfcVec := [
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

def main : IO UInt32 := do
  let mut failed : Nat := 0
  let mut checked : Nat := 0
  for v in rfcVectors do
    -- sign through the SignatureAlg, simulate with the trivial unif impl
    let sigOut : ByteArray := simulateQ constUnifImpl (ed25519.sign v.pk v.sk v.msg) |>.run
    let verOut : Bool := simulateQ constUnifImpl (ed25519.verify v.pk v.msg v.sig) |>.run
    let zipOut : Bool := simulateQ constUnifImpl (ed25519Zip215.verify v.pk v.msg v.sig) |>.run
    checked := checked + 3
    if sigOut != v.sig then
      IO.eprintln ("FAIL sign " ++ v.name)
      failed := failed + 1
    if verOut != true then
      IO.eprintln ("FAIL verify " ++ v.name)
      failed := failed + 1
    if zipOut != true then
      IO.eprintln ("FAIL verifyZip215 " ++ v.name)
      failed := failed + 1
  if failed = 0 then
    IO.println ("OK " ++ toString checked ++
      " vectors (ed25519 SignatureAlg sign/verify/verifyZip215 vs RFC 8032 §7.1)")
    return 0
  else
    IO.eprintln ("FAILED " ++ toString failed)
    return 1
