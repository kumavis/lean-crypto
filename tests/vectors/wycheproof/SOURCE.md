# Wycheproof vendored vectors

## `ed25519_test.json`

* **Source:** [`github.com/C2SP/wycheproof`](https://github.com/C2SP/wycheproof) — `testvectors_v1/ed25519_test.json`
* **Vendored copy hash (SHA-256):** `70471c053c711731f2195ef4875b60ea7f5d6793939d99058ac12da810cb8e00` (122087 bytes)
* **Schema:** `eddsa_verify_schema_v1.json` (per the file's own `schema` field).
* **Count:** 150 tests across 77 groups (88 `valid`, 62 `invalid`).

The SHA-256 above pins the *exact* bytes of the vendored vector file —
two developers cloning this repo at the current commit get bit-for-bit
identical vectors. The upstream commit SHA that produced these bytes
isn't captured here (the file was originally fetched from
`testvectors_v1/ed25519_test.json` on the upstream `main` branch
without recording the snapshot SHA); to refresh, capture the new
upstream SHA as part of the procedure below so future refreshes have
a clean audit trail.

## Refresh procedure

```sh
# 1. Capture the upstream commit SHA we're vendoring against.
UPSTREAM_SHA=$(curl -sSL \
  https://api.github.com/repos/C2SP/wycheproof/commits/main \
  | jq -r .sha)
echo "Vendoring upstream SHA: $UPSTREAM_SHA"

# 2. Fetch the snapshot at that exact SHA (NOT main — main may have
#    moved between step 1 and step 2 in a concurrent push).
curl -sSL -o tests/vectors/wycheproof/ed25519_test.json \
  "https://raw.githubusercontent.com/C2SP/wycheproof/${UPSTREAM_SHA}/testvectors_v1/ed25519_test.json"

# 3. Record the new vendored-copy SHA-256 + upstream SHA in this file.
echo "New vendored SHA-256:"
sha256sum tests/vectors/wycheproof/ed25519_test.json
echo "Upstream commit: $UPSTREAM_SHA"

# 4. Run the test runner; investigate any new mismatches.
lake exe Tests.WycheproofTest
```

Any new mismatches after a refresh are either a real regression in our
verify (bug) or a deliberate Wycheproof change that warrants discussion
in `tests/wycheproof_decisions.md`.
