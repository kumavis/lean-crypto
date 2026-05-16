import Lake
open Lake DSL

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
