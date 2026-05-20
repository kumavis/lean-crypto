import Lean.Data.Json
import LeanCrypto.Bytes
import LeanCrypto.Signature.Ed25519

open Lean (Json)
open LeanCrypto.Bytes
open LeanCrypto.Signature.Ed25519

/-! M10 — Project Wycheproof `ed25519_test.json` runner.

Each test case is exercised through `verify` (strict RFC 8032) and
`verifyZip215`.

* Strict mode: every case must match Wycheproof's expected `result`
  (valid/invalid). Any mismatch fails the runner.
* ZIP-215 mode: divergences from strict are expected on `invalid`
  cases flagged for non-canonical encodings or small-order public
  keys. We tolerate these (don't fail the runner) but report a count.
  Strict-bugfix cases like `SignatureMalleability` (S ≥ ℓ) must still
  be rejected by ZIP-215 — those failures DO fail the runner.

See `tests/wycheproof_decisions.md` for the full per-flag policy. -/

structure WpTest where
  tcId    : Nat
  comment : String
  flags   : List String
  msg     : ByteArray
  sig     : ByteArray
  result  : String

structure WpGroup where
  pk    : ByteArray
  tests : List WpTest

private def hexOrErr (label : String) (s : String) : Except String ByteArray :=
  match hexToBytes s with
  | some b => .ok b
  | none => .error s!"{label}: not valid hex: {s}"

private def parseTest (j : Json) : Except String WpTest := do
  let tcId    ← (← j.getObjVal? "tcId").getNat?
  let comment ← (← j.getObjVal? "comment").getStr?
  let result  ← (← j.getObjVal? "result").getStr?
  let msgHex  ← (← j.getObjVal? "msg").getStr?
  let sigHex  ← (← j.getObjVal? "sig").getStr?
  let msg     ← hexOrErr "msg" msgHex
  let sig     ← hexOrErr "sig" sigHex
  let flagsJ  ← (← j.getObjVal? "flags").getArr?
  let flags   ← flagsJ.toList.mapM (·.getStr?)
  return { tcId, comment, result, flags, msg, sig }

private def parseGroup (j : Json) : Except String WpGroup := do
  let pkHex ← (← (← j.getObjVal? "publicKey").getObjVal? "pk").getStr?
  let pk    ← hexOrErr "publicKey.pk" pkHex
  let testsJ ← (← j.getObjVal? "tests").getArr?
  let tests ← testsJ.toList.mapM parseTest
  return { pk, tests }

private def parseFile (text : String) : Except String (List WpGroup) := do
  let j ← Json.parse text
  let groupsJ ← (← j.getObjVal? "testGroups").getArr?
  groupsJ.toList.mapM parseGroup

/-- Flags whose `invalid` cases ZIP-215 may legitimately ACCEPT. These are
the encoding/representation differences between strict RFC and ZIP-215;
they don't represent security bugs in ZIP-215, they represent its
documented permissiveness.

Only `InvalidEncoding` is permissible — it covers non-canonical `R` / `pk`
encodings, which ZIP-215 reduces mod p instead of rejecting outright.
`InvalidKtv` (equation-failure attack vectors) and `InvalidSignature`
(`S = 0` / `S = ℓ` etc.) should reject under both modes per
`tests/wycheproof_decisions.md`; keeping them out of this list means a
future Wycheproof vector that wrongly verifies under ZIP-215 on those
flags fails CI instead of being silently demoted to `zip215Divergence`. -/
private def zip215PermissibleFlags : List String :=
  ["InvalidEncoding"]

private def overlap (a b : List String) : Bool :=
  a.any (fun x => b.contains x)

structure Stats where
  strictMatch       : Nat := 0
  strictMismatch    : Nat := 0
  zip215Match       : Nat := 0
  zip215Divergence  : Nat := 0   -- expected divergence from strict on permissible flags
  zip215Mismatch    : Nat := 0   -- unexpected: ZIP-215 disagrees in a non-permissible way

def runAll (groups : List WpGroup) : IO Stats := do
  let mut s : Stats := {}
  for g in groups do
    for t in g.tests do
      let expected : Bool := t.result == "valid"
      let gotStrict := verify g.pk t.sig t.msg
      let gotZip    := verifyZip215 g.pk t.sig t.msg
      -- Strict
      if gotStrict == expected then
        s := { s with strictMatch := s.strictMatch + 1 }
      else
        s := { s with strictMismatch := s.strictMismatch + 1 }
        IO.eprintln s!"  STRICT MISMATCH tcId={t.tcId} expected={t.result} got={gotStrict} flags={t.flags} :: {t.comment}"
      -- ZIP-215
      if gotZip == expected then
        s := { s with zip215Match := s.zip215Match + 1 }
      else if gotZip && !expected && overlap t.flags zip215PermissibleFlags then
        -- Documented divergence: ZIP-215 accepts a strict-invalid case
        -- whose only flaw is non-canonical encoding.
        s := { s with zip215Divergence := s.zip215Divergence + 1 }
      else
        s := { s with zip215Mismatch := s.zip215Mismatch + 1 }
        IO.eprintln s!"  ZIP215 UNEXPECTED tcId={t.tcId} expected={t.result} got={gotZip} flags={t.flags} :: {t.comment}"
  return s

def main : IO UInt32 := do
  let text ← IO.FS.readFile "tests/vectors/wycheproof/ed25519_test.json"
  let groups ← IO.ofExcept (parseFile text)
  let total : Nat := (groups.map (·.tests.length)).foldl (· + ·) 0
  IO.println s!"Wycheproof ed25519: {groups.length} groups, {total} tests"
  let stats ← runAll groups
  IO.println s!"  strict:   {stats.strictMatch} match, {stats.strictMismatch} mismatch"
  IO.println s!"  zip215:   {stats.zip215Match} match, {stats.zip215Divergence} documented-divergence, {stats.zip215Mismatch} unexpected-mismatch"
  if stats.strictMismatch == 0 ∧ stats.zip215Mismatch == 0 then
    IO.println s!"OK {stats.strictMatch + stats.zip215Match + stats.zip215Divergence} vectors"
    return 0
  else
    IO.eprintln s!"FAIL {stats.strictMismatch} strict + {stats.zip215Mismatch} zip215 unexpected"
    return 1
