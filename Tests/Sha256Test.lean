import LeanCrypto.Bytes
import LeanCrypto.Hash.SHA256
import LeanCrypto.Data.CAVS

open LeanCrypto.Bytes
open LeanCrypto.Hash.SHA256
open LeanCrypto.Data.CAVS

/-! SHA-256 test runner.

Sanity checks → NIST CAVP short → long → chunked-streaming differential →
Monte Carlo (M3 + M4).

Prints `OK <N> vectors` on success; on first mismatch prints the test
context, expected digest, actual digest, and exits 1. -/

/-- Stream `msg` through `Sha256Ctx.update` in slices of `chunk` bytes. -/
def sha256Chunked (msg : ByteArray) (chunk : Nat) : ByteArray := Id.run do
  let step := max chunk 1
  let mut ctx := Sha256Ctx.init
  let mut i := 0
  while i < msg.size do
    let stop := min (i + step) msg.size
    ctx := ctx.update (msg.extract i stop)
    i := stop
  return ctx.finalize

/-- One Monte Carlo run per FIPS 180-4: 100 outputs, each the result of
1000 chained hashes starting from the current seed. -/
def runMonteSha256 (seed : ByteArray) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := #[]
  let mut s := seed
  for _ in [:100] do
    let mut a := s
    let mut b := s
    let mut c := s
    for _ in [:1000] do
      let md := sha256 (a ++ b ++ c)
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
    -- One-shot
    let got := sha256 r.msg
    if got != r.md then
      return .error (s!"{label} #{i} one-shot: expected {bytesToHex r.md}, got {bytesToHex got}", nPass)
    nPass := nPass + 1
    -- Streaming at each chunk size — differential test.
    for chunk in chunkSizes do
      let gotC := sha256Chunked r.msg chunk
      if gotC != r.md then
        return .error
          (s!"{label} #{i} streaming chunk={chunk}: expected {bytesToHex r.md}, got {bytesToHex gotC}", nPass)
      nPass := nPass + 1
  return .ok nPass

def main : IO UInt32 := do
  let mut nPass : Nat := 0

  -- Sanity: rotr32
  let r := rotr32 0x12345678 8
  if r != 0x78123456 then
    IO.eprintln s!"FAIL rotr32 0x12345678 8: got {bytesToHex (storeU32BE ByteArray.empty r)}"
    return 1
  nPass := nPass + 1

  -- Sanity: empty string
  let h := sha256 ByteArray.empty
  let want := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  if bytesToHex h != want then
    IO.eprintln s!"FAIL sha256(\"\"): expected {want}, got {bytesToHex h}"
    return 1
  nPass := nPass + 1

  -- NIST CAVP short — one-shot only (short messages don't exercise chunking enough).
  match ← runMsgFile "ShortMsg" "tests/vectors/sha256/SHA256ShortMsg.rsp" [] nPass with
  | .error (msg, n) => IO.eprintln s!"FAIL {msg} (after {n} passing)"; return 1
  | .ok n => nPass := n

  -- NIST CAVP long — one-shot + streaming at multiple chunk granularities.
  match ← runMsgFile "LongMsg" "tests/vectors/sha256/SHA256LongMsg.rsp" [1, 7, 63, 64, 65, 1024] nPass with
  | .error (msg, n) => IO.eprintln s!"FAIL {msg} (after {n} passing)"; return 1
  | .ok n => nPass := n

  -- NIST CAVP Monte Carlo: 100 chained outputs (1000 hashes each).
  let monteText ← IO.FS.readFile "tests/vectors/sha256/SHA256Monte.rsp"
  let monte ← IO.ofExcept (parseMonteFile monteText)
  let got := runMonteSha256 monte.seed
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
