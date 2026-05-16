# Wycheproof decisions — ed25519

Per-flag verification policy for `tests/vectors/wycheproof/ed25519_test.json`
(C2SP wycheproof `testvectors_v1/ed25519_test.json`, 150 cases, 77 groups).

Both `Ed25519.verify` (strict RFC 8032) and `Ed25519.verifyZip215`
(noble-compatible) are exercised against every case. The columns below
are the **expected** verify outcomes — every row in the current vendored
file actually agrees with these expectations under both modes.

| Wycheproof flag         | Result label | `verify` (strict) | `verifyZip215` | Reasoning |
|-------------------------|--------------|-------------------|----------------|-----------|
| `Valid`                 | valid        | accept            | accept         | Canonical RFC 8032 signature on a curve-order public key. Both modes accept. |
| `Ktv`                   | valid        | accept            | accept         | Known test vector. Same as `Valid`. |
| `SignatureMalleability` | invalid      | reject            | reject         | `S ≥ ℓ`. Both modes reject (RFC 8032 §5.2.7; ZIP-215 retains the `S < ℓ` check). |
| `SignatureWithGarbage`  | invalid      | reject            | reject         | Signature length ≠ 64 bytes. Length check is part of both modes' first gate. |
| `TruncatedSignature`    | invalid      | reject            | reject         | Same length check. |
| `CompressedSignature`   | invalid      | reject            | reject         | Length / structural malformation. |
| `InvalidEncoding`       | invalid      | reject            | reject         | Non-canonical `R` or `pk` encoding. Strict rejects via the `y < p` gate; ZIP-215 reduces y mod p but the resulting equation still fails for these crafted cases. |
| `InvalidKtv`            | invalid      | reject            | reject         | Adversarial known test vector — equation fails. |
| `InvalidSignature`      | invalid      | reject            | reject         | Edge values (e.g. `S = 0` or `S = ℓ`). Either the equation fails or the malleability gate catches them. |
| `TinkOverflow`          | invalid      | reject            | reject         | Boost-style overflow used to bypass weak verifiers. Strict and ZIP-215 both perform the full cofactored equation, so neither is fooled. |

## Why ZIP-215 agrees with strict on every Wycheproof case

ZIP-215's documented permissiveness (non-canonical `y` and small-order public
keys) overlaps with Wycheproof flags `InvalidEncoding` and a subset of
`InvalidSignature`. In principle ZIP-215 could *accept* some of those
cases, which would diverge from Wycheproof's `invalid` label.

In practice all of Wycheproof v1's `invalid` cases under those flags
combine non-canonical encoding with **other** structural defects
(wrong-length signature, broken curve equation after the mod-p reduction,
etc.) so the ZIP-215 decode succeeds but the verify equation still fails.
Net effect: 150/150 agree under both modes, with `zip215Divergence = 0`.

If a future Wycheproof revision introduces cases isolating exactly the
strict-vs-ZIP-215 distinction, the runner is set up to **tolerate** those
ZIP-215 acceptances when the case carries flags from
`zip215PermissibleFlags` (currently `InvalidEncoding`, `InvalidKtv`,
`InvalidSignature`). It logs them as `zip215Divergence` and does not fail
CI. Any other ZIP-215 disagreement is treated as a bug.

## Source

`tests/vectors/wycheproof/ed25519_test.json` is a verbatim snapshot of
`testvectors_v1/ed25519_test.json` from
`https://github.com/C2SP/wycheproof` (main branch). The vendored copy
will drift over time; refresh by re-downloading and re-running the test
binary. If any new `invalid` case suddenly verifies under strict mode,
that is a real regression in the verify implementation, not a Wycheproof
update we should rubber-stamp.
