import LeanCrypto.Bytes

/-!
# `LeanCrypto.Data.CAVS`

Tiny line-based parser for NIST CAVP `.rsp` files used to validate hash
implementations. Format example:

```
#  CAVS 11.0
#  "SHA-256 ShortMsg" information

[L = 32]

Len = 0
Msg = 00
MD = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855

Len = 8
Msg = d3
MD = 28969cdfa74a12c82f3bad960b0b000aca2ac329deea5c2328ebc6f2ba9802c1
```

`Len` is the message length in **bits**. When `Len = 0` the `Msg` field is
`00` by convention but the actual input is empty. Comments (`#`) and
section headers (`[…]`) are skipped.
-/

set_option autoImplicit false

namespace LeanCrypto.Data.CAVS

open LeanCrypto.Bytes

structure MsgRecord where
  /-- Length of the message in **bits** (so a 1-byte message has `lenBits = 8`). -/
  lenBits : Nat
  msg     : ByteArray
  md      : ByteArray
  deriving Inhabited

structure MonteRecord where
  /-- The seed for a Monte Carlo run. -/
  seed : ByteArray
  /-- 100 expected output digests, in order. -/
  mds  : Array ByteArray
  deriving Inhabited

/-- Strip a comment / section header / blank line, returning `none` for
lines the caller should skip entirely. Operates on the `Substring`
returned by `trimAscii` and only allocates a fresh `String` for lines
the caller will keep — avoids per-line `String` allocation on
multi-megabyte vector files. -/
private def stripComments (line : String) : Option String :=
  let s := line.trimAscii
  if s.isEmpty || s.startsWith "#" || s.startsWith "[" then none
  else some s.toString

/-- Parse a `*ShortMsg.rsp` / `*LongMsg.rsp` file body. Errors on any
unrecognised non-empty line (after stripping comments / section headers
/ whitespace) so a typo like `Len: 0` (using `:` instead of `=`) is
caught at parse time rather than silently dropped. -/
def parseMsgFile (text : String) : Except String (Array MsgRecord) := do
  let mut records : Array MsgRecord := #[]
  let mut len  : Option Nat       := none
  let mut msgH : Option String    := none
  for raw in text.splitOn "\n" do
    let some line := stripComments raw | continue
    let parts := line.splitOn "="
    match parts with
    | [k, v] =>
        let k := k.trimAscii.toString
        let v := v.trimAscii.toString
        if k == "Len" then
          let some n := v.toNat? | throw s!"Len: bad Nat: {v}"
          len  := some n
          msgH := none
        else if k == "Msg" then
          msgH := some v
        else if k == "MD" then
          let some lenN := len     | throw s!"MD without Len: {line}"
          let some msgX := msgH    | throw s!"MD without Msg: {line}"
          let msgBytes ← (do
            if lenN == 0 then
              -- CAVS convention: zero-length input is encoded as `Msg = 00`.
              -- Don't try to decode the literal; just emit empty bytes.
              return ByteArray.empty
            match hexToBytes msgX with
            | some bs => return bs
            | none    => throw s!"bad Msg hex: {msgX}")
          let some mdBytes := hexToBytes v | throw s!"bad MD hex: {v}"
          records := records.push { lenBits := lenN, msg := msgBytes, md := mdBytes }
          len  := none
          msgH := none
        else throw s!"parseMsgFile: unknown key {repr k}: {line}"
    | _ => throw s!"parseMsgFile: unrecognised line (not 'k = v'): {line}"
  return records

/-- Parse a `*Monte.rsp` file body. Errors on any unrecognised non-empty
line — `COUNT = N` lines are explicitly recognised and skipped. -/
def parseMonteFile (text : String) : Except String MonteRecord := do
  let mut seed : Option ByteArray := none
  let mut mds  : Array ByteArray := #[]
  for raw in text.splitOn "\n" do
    let some line := stripComments raw | continue
    let parts := line.splitOn "="
    match parts with
    | [k, v] =>
        let k := k.trimAscii.toString
        let v := v.trimAscii.toString
        if k == "Seed" then
          let some s := hexToBytes v | throw s!"bad Seed hex: {v}"
          seed := some s
        else if k == "MD" then
          let some s := hexToBytes v | throw s!"bad MD hex: {v}"
          mds := mds.push s
        else if k == "COUNT" then
          pure ()    -- ignored on purpose
        else throw s!"parseMonteFile: unknown key {repr k}: {line}"
    | _ => throw s!"parseMonteFile: unrecognised line (not 'k = v'): {line}"
  let some s := seed | throw "Monte file missing Seed"
  return { seed := s, mds := mds }

end LeanCrypto.Data.CAVS
