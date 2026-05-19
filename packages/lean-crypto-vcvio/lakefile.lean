import Lake
open Lake DSL

/-! `lean-crypto-vcvio` — VCV-io wrapper + algebraic-foundations proof
track for `lean-crypto`. Distinct Lake package from the core so
consumers needing only the pure-Lean primitives don't pull Mathlib.

Consumers (other Lean projects that want the wrapper + proofs):

```
require «lean-crypto-vcvio» from git
  "https://github.com/kumavis/lean-crypto" @ "main" with
  subDir := "packages/lean-crypto-vcvio"
```

When developing locally, this package requires the outer `lean-crypto`
package via a relative path — no git fetch needed in the monorepo
layout.
-/

require «lean-crypto» from ".." / ".."

require "leanprover-community" / "mathlib" @ git "v4.29.0"

require VCVio from git
  "https://github.com/dtumad/VCV-io" @ "v4.29.0"

package «lean-crypto-vcvio» where
  -- no package-level options yet

@[default_target]
lean_lib LeanCryptoVCVio where
  buildType := BuildType.release

lean_lib LeanCryptoProofs where
  buildType := BuildType.release

lean_exe Tests.VCVio.Smoke

lean_exe Tests.VCVio.Hash

lean_exe Tests.VCVio.Ed25519Det

lean_exe Tests.VCVio.Ed25519ROM

lean_exe Tests.VCVio.GameSmoke
