import LeanCrypto.Bytes
import LeanCrypto.Hash.SHA512
import LeanCrypto.Data.CAVS

open LeanCrypto.Bytes
open LeanCrypto.Hash.SHA512
open LeanCrypto.Data.CAVS

/-! SHA-512 test runner — mirrors `Tests.Sha256Test` in shape. -/

def sha512Chunked (msg : ByteArray) (chunk : Nat) : ByteArray := Id.run do
  let step := max chunk 1
  let mut ctx := Sha512Ctx.init
  let mut i := 0
  while i < msg.size do
    let stop := min (i + step) msg.size
    ctx := ctx.update (msg.extract i stop)
    i := stop
  return ctx.finalize

def runMonteSha512 (seed : ByteArray) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := #[]
  let mut s := seed
  for _ in [:100] do
    let mut a := s
    let mut b := s
    let mut c := s
    for _ in [:1000] do
      let md := sha512 (a ++ b ++ c)
      a := b
      b := c
      c := md
    out := out.push c
    s := c
  return out

def runMsgFile (label : String) (path : System.FilePath)
    (chunkSizes : List Nat) (nPass : Nat) : IO (Except (String × Nat) Nat) := do
  let text ← IO.FS.readFile path
  let records ← IO.ofExcept (parseMsgFile text)
  let mut nPass := nPass
  for i in [:records.size] do
    let r := records[i]!
    let got := sha512 r.msg
    if got != r.md then
      return .error (s!"{label} #{i} one-shot: expected {bytesToHex r.md}, got {bytesToHex got}", nPass)
    nPass := nPass + 1
    for chunk in chunkSizes do
      let gotC := sha512Chunked r.msg chunk
      if gotC != r.md then
        return .error
          (s!"{label} #{i} streaming chunk={chunk}: expected {bytesToHex r.md}, got {bytesToHex gotC}", nPass)
      nPass := nPass + 1
  return .ok nPass

def main : IO UInt32 := do
  let mut nPass : Nat := 0

  -- Sanity: rotr64
  let r := rotr64 0x0123456789abcdef 16
  if r != 0xcdef0123456789ab then
    IO.eprintln s!"FAIL rotr64 0x0123456789abcdef 16: got {bytesToHex (storeU64BE ByteArray.empty r)}"
    return 1
  nPass := nPass + 1

  -- Sanity: empty
  let h := sha512 ByteArray.empty
  let want := "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
  if bytesToHex h != want then
    IO.eprintln s!"FAIL sha512(\"\"): expected {want}, got {bytesToHex h}"
    return 1
  nPass := nPass + 1

  match ← runMsgFile "ShortMsg" "tests/vectors/sha512/SHA512ShortMsg.rsp" [] nPass with
  | .error (msg, n) => IO.eprintln s!"FAIL {msg} (after {n} passing)"; return 1
  | .ok n => nPass := n

  match ← runMsgFile "LongMsg" "tests/vectors/sha512/SHA512LongMsg.rsp" [1, 7, 127, 128, 129, 1024] nPass with
  | .error (msg, n) => IO.eprintln s!"FAIL {msg} (after {n} passing)"; return 1
  | .ok n => nPass := n

  let monteText ← IO.FS.readFile "tests/vectors/sha512/SHA512Monte.rsp"
  let monte ← IO.ofExcept (parseMonteFile monteText)
  let got := runMonteSha512 monte.seed
  if got.size != monte.mds.size then
    IO.eprintln s!"FAIL Monte: got {got.size} digests, expected {monte.mds.size}"
    return 1
  for i in [:got.size] do
    if got[i]! != monte.mds[i]! then
      IO.eprintln s!"FAIL Monte #{i}: expected {bytesToHex monte.mds[i]!}, got {bytesToHex got[i]!}"
      return 1
    nPass := nPass + 1

  IO.println s!"OK {nPass} vectors"
  return 0
