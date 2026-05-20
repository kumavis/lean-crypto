import LeanCryptoVCVio

/-- M13 smoke test: the wrapper library compiles and links against VCV-io. -/
def main : IO UInt32 := do
  IO.println "OK 0 vectors"
  return 0
