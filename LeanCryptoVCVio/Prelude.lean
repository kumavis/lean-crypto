import VCVio.OracleComp.OracleSpec
import LeanCrypto

/-!
# VCV-io wrapper — prelude

Shared imports and namespace setup for the `LeanCryptoVCVio` library.
Brings `LeanCrypto` (our pure-functional implementation) into scope alongside
the minimum slice of VCV-io needed for the wrapper. The import surface widens
in later milestones:

* M13 (this file): just `VCVio.OracleComp.OracleSpec` — proves the
  dependency wiring resolves end-to-end.
* M14: pulls in `VCVio.OracleComp.OracleComp` once the deterministic
  adapters need `pure`/`bind` over `OracleComp`.
* M15/M16: adds `VCVio.CryptoFoundations.SignatureAlg` and
  `VCVio.OracleComp.QueryTracking.RandomOracle` for the `SignatureAlg`
  instance and the ROM-modeled SHA-512 variant.
-/

namespace LeanCryptoVCVio
end LeanCryptoVCVio
