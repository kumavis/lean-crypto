import LeanCrypto.Bytes
import LeanCrypto.Hash.SHA256
import LeanCrypto.Hash.SHA512
import LeanCrypto.Signature.Ed25519

open LeanCrypto.Bytes
open LeanCrypto.Hash.SHA256 (sha256)
open LeanCrypto.Hash.SHA512 (sha512)
open LeanCrypto.Signature.Ed25519

/-! `Tests.DiffCli` — request/response harness for the differential fuzzer.

Reads commands from stdin (one per line) and writes a single-line response
per command. The driver scripts in `tests/diff/` spawn this binary once per
fuzz run and feed it many commands, avoiding subprocess fork overhead.

Commands:
  `sha256 <hex>`                                  → digest hex (one-shot)
  `sha512 <hex>`                                  → digest hex (one-shot)
  `sha256-chunks <hex1> <hex2> ... <hexN>`        → digest hex (streaming)
  `sha512-chunks <hex1> <hex2> ... <hexN>`        → digest hex (streaming)
  `ed25519-pubkey <sk-hex>`                       → 32-byte pubkey hex
  `ed25519-sign <sk-hex> <msg-hex>`               → 64-byte sig hex
  `ed25519-verify <pk-hex> <sig-hex> <msg-hex>`   → `true` or `false`
  `ed25519-verify-zip215 <pk-hex> <sig-hex> <msg-hex>` → `true` or `false`

The streaming commands accept 0 or more chunks (zero chunks ⇒ digest of
the empty message). Each chunk argument is independent hex; concatenating
all chunks yields the equivalent one-shot input.

Errors are emitted as `ERR <reason>` on a single line. -/

private def hexOr (label : String) (s : String) (k : ByteArray → String) : String :=
  match hexToBytes s with
  | some b => k b
  | none => s!"ERR bad-hex({label}): {s}"

/-- Decode a list of hex chunks; returns `none` on first bad chunk. -/
private def hexChunks (hexes : List String) : Option (List ByteArray) :=
  hexes.foldr (init := some []) fun h acc => do
    let bs ← hexToBytes h
    let rest ← acc
    return bs :: rest

/-- SHA-256 over a sequence of chunks via the streaming API. -/
private def sha256Streaming (chunks : List ByteArray) : ByteArray :=
  let ctx := chunks.foldl
    (init := LeanCrypto.Hash.SHA256.Sha256Ctx.init)
    (fun c chunk => c.update chunk)
  ctx.finalize

/-- SHA-512 over a sequence of chunks via the streaming API. -/
private def sha512Streaming (chunks : List ByteArray) : ByteArray :=
  let ctx := chunks.foldl
    (init := LeanCrypto.Hash.SHA512.Sha512Ctx.init)
    (fun c chunk => c.update chunk)
  ctx.finalize

def respond (line : String) : String :=
  -- Split on a single space; do NOT trim, so an empty hex arg (after a
  -- trailing space) is preserved as `""` and decodes to an empty
  -- ByteArray.  Drivers must use exactly one space between fields.
  let parts := line.splitOn " "
  match parts with
  | ["sha256", h] => hexOr "msg" h (fun b => bytesToHex (sha256 b))
  | ["sha512", h] => hexOr "msg" h (fun b => bytesToHex (sha512 b))
  | "sha256-chunks" :: hexes =>
      match hexChunks hexes with
      | some chunks => bytesToHex (sha256Streaming chunks)
      | none => s!"ERR bad-hex(chunks): {line}"
  | "sha512-chunks" :: hexes =>
      match hexChunks hexes with
      | some chunks => bytesToHex (sha512Streaming chunks)
      | none => s!"ERR bad-hex(chunks): {line}"
  | ["ed25519-pubkey", sk] => hexOr "sk" sk (fun s => bytesToHex (derivePublicKey s))
  | ["ed25519-sign", sk, msg] =>
      hexOr "sk" sk fun s =>
        hexOr "msg" msg fun m => bytesToHex (sign s m)
  | ["ed25519-verify", pk, sig, msg] =>
      hexOr "pk" pk fun p =>
        hexOr "sig" sig fun s =>
          hexOr "msg" msg fun m => toString (verify p s m)
  | ["ed25519-verify-zip215", pk, sig, msg] =>
      hexOr "pk" pk fun p =>
        hexOr "sig" sig fun s =>
          hexOr "msg" msg fun m => toString (verifyZip215 p s m)
  | _ => s!"ERR unknown-cmd: {line}"

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let all ← stdin.readToEnd
  for line in all.splitOn "\n" do
    if line.trimAscii.toString.isEmpty then continue
    IO.println (respond line)
  return 0
