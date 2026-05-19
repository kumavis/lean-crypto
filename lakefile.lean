import Lake
open Lake DSL

/-! `lean-crypto` — pure Lean 4 SHA-256/512 + Ed25519, no external deps.

This package has **zero** dependencies beyond the Lean toolchain itself.
Consumers (e.g. `lean-ocapn`) can depend on this directly without
pulling Mathlib or VCV-io into their build:

```
require «lean-crypto» from git
  "https://github.com/kumavis/lean-crypto" @ "main"
```

The optional VCV-io wrapper and the algebraic-foundations proof track
live in the **nested package** at `packages/lean-crypto-vcvio/`, which
*does* depend on Mathlib + VCV-io. See that directory's lakefile and
`docs/VCV_IO_PLAN.md` / `docs/PROOFS_ROADMAP.md`.
-/

package «lean-crypto» where
  -- no package-level options yet

@[default_target]
lean_lib LeanCrypto where
  buildType := BuildType.release
  moreLeancArgs := #["-O3"]

lean_exe Tests.HelloTest

lean_exe Tests.BytesTest

lean_exe Tests.Sha256Test

lean_exe Tests.Sha512Test

lean_exe Tests.Fp25519Test

lean_exe Tests.ScalarLTest

lean_exe Tests.Edwards25519Test

lean_exe Tests.Ed25519Test

lean_exe Tests.WycheproofTest

lean_exe Tests.DiffCli
