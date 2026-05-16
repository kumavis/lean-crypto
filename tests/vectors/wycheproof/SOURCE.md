# Wycheproof vendored vectors

## `ed25519_test.json`

* **Source:** [`github.com/C2SP/wycheproof`](https://github.com/C2SP/wycheproof) — `testvectors_v1/ed25519_test.json`
* **Pinned at:** branch `main` as of fetch time (no commit SHA captured at vendor time — refresh and re-pin if you need exact reproducibility).
* **Schema:** `eddsa_verify_schema_v1.json` (per the file's own `schema` field).
* **Count:** 150 tests across 77 groups (88 `valid`, 62 `invalid`).

Refresh procedure:

```sh
curl -sL -o tests/vectors/wycheproof/ed25519_test.json \
  https://raw.githubusercontent.com/C2SP/wycheproof/main/testvectors_v1/ed25519_test.json
```

Then run `lake exe Tests.WycheproofTest`. Any new mismatches are either
a real regression in our verify (bug) or a deliberate Wycheproof change
that warrants discussion in `tests/wycheproof_decisions.md`.
