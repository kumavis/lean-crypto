import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.29.0"

require VCVio from git
  "https://github.com/dtumad/VCV-io" @ "v4.29.0"

package «lean-crypto» where
  -- no package-level options yet

@[default_target]
lean_lib LeanCrypto where
  buildType := BuildType.release
  moreLeancArgs := #["-O3"]

lean_lib LeanCryptoVCVio where
  buildType := BuildType.release

lean_lib LeanCryptoProofs where
  buildType := BuildType.release

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

lean_exe Tests.VCVio.Smoke

lean_exe Tests.VCVio.Hash

lean_exe Tests.VCVio.Ed25519Det

lean_exe Tests.VCVio.Ed25519ROM

lean_exe Tests.VCVio.GameSmoke
