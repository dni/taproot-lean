# taproot-lean

Machine-checked proofs, in [Lean 4](https://lean-lang.org) with [Mathlib](https://github.com/leanprover-community/mathlib4) and [VCVio](https://github.com/Verified-zkEVM/VCV-io), about the cryptography behind Bitcoin's Taproot upgrade:

- Schnorr signatures (BIP340)
- Taproot outputs (BIP341)
- MuSig2 multi-signatures (BIP327)
- Bech32m addresses (BIP350)
- Discreet Log Contracts (DLCs) built on top of them

The proofs work over a **concrete secp256k1 curve**, built from Mathlib's elliptic-curve group law, not over an assumed abstract group. The primes `p` and `n` are proven prime inside Lean.

Repository: <https://github.com/dni/taproot-lean>

## Highlight: BIP340 batch verification with 128-bit randomizers

[sipa/bips#219](https://github.com/sipa/bips/issues/219) and [sipa/bips#222](https://github.com/sipa/bips/pull/222) propose shrinking BIP340's batch-verification randomizers from 256 to 128 bits, which speeds up batch verification in libsecp256k1 by up to about 9%. The pen-and-paper argument there treats the randomizers as independent uniform values. In practice they are derived deterministically from the batch, and with incremental derivation (as in libsecp256k1's batch API) the attacker can pick later entries after seeing earlier randomizers. The PR discussion leaves open whether the argument still applies in that setting.

`Taproot/BIP340Batch.lean` answers this with machine-checked bounds in the random oracle model. Each holds for every choice of the challenge hash:

| Setting | Result | Theorem |
|---|---|---|
| Independent uniform `b`-bit randomizers | An invalid signature is caught except with probability `2^-b`. | `batchVerify_sound_bits` |
| Randomizers hashed from the whole batch (the BIP340 text) | An attacker making `q` hash queries, with batches of at most `ℓ` signatures, gets an invalid batch accepted with probability **at most `(q + ℓ)/2^b`**. | `batch_indexed_sound` |
| Incremental derivation (randomizer `i` hashes the first `i` entries) | The same bound, **`(q + ℓ)/2^b`**, although the attacker chooses later entries after seeing earlier randomizers. | `batch_incremental_sound` |
| Both derivations on secp256k1 with `b = 128` | **`(q + ℓ)/2^128`** | `secp256k1_batch_indexed_sound`, `secp256k1_batch_incremental_sound` |
| Lower bound | An explicit grinding attacker reaches **`1 - (1 - 2^-b)^q ≈ q/2^b`**, so the `q` term is tight. | `batch_indexed_grind` |

What this means for 128-bit randomizers: they are sound, and the only extra cost of deriving them deterministically is offline grinding at one hash per attempt. About `2^64` hash evaluations get an invalid batch accepted with probability about `2^-64`. Whether that margin is acceptable is a judgment for the BIP; the bounds make the trade-off exact.

Assumptions: the seed hash and the CSPRNG are idealized as a random oracle; every point satisfies `n·P = 0` (see [Limitations](#limitations)); the secp256k1 versions use the one `native_decide` computation `n·G = 0`.

## What is proven

Unless stated otherwise, every result holds for **all** choices of the tagged hash functions. Hashes are modelled as arbitrary functions, so no property of SHA-256 is assumed. Where a result needs a hash to be collision-free, that is an explicit hypothesis. Most results are *correctness* properties: when the parties follow the protocol, everything verifies. The *binding* and *extraction* results go further: they hold for arbitrary, possibly malicious, inputs. Unforgeability itself is not covered (see [Limitations](#limitations)).

### BIP340: Schnorr signatures — `Taproot/BIP340.lean`
| Theorem | Statement |
|---|---|
| `verify_sign` | Every signature produced by `Sign` with secret key `sk` is accepted by `Verify` under `sk`'s public key. |

`Taproot/BIP340Props.lean`:

| Theorem | Statement |
|---|---|
| `verify_unique` | **Non-malleability**: for a given public key, message and `r`, at most one `s` is valid. |
| `extract_secret` | **Special soundness**, the extractor behind Schnorr's security proof: any two valid signatures that share `r` but have different challenges reveal the secret key. |
| `sign_nonce_reuse` | So a signer whose nonce repeats across two messages leaks its key. |
| `batchVerify_of_valid` | BIP340 batch verification accepts every batch of valid signatures, for every choice of coefficients. |
| `batchVerify_sound` | If one signature is invalid, then once the other coefficients are fixed, at most one value of its coefficient lets the batch pass. A random coefficient catches it except with probability `1/n`. |
| `batchVerify_sound_bits` | The same with `b`-bit coefficients (`2^b ≤ n`): at most one `b`-bit value of the coefficient lets the batch pass, so 128-bit coefficients catch an invalid signature except with probability `2^-128`. |
| `batchVerify_sound_single` | A single invalid signature with a nonzero coefficient (e.g. BIP340's fixed `a₁ = 1`) is always caught. |

### BIP340 unforgeability (EUF-CMA) — `Taproot/BIP340Security.lean`

Built on [VCVio](https://github.com/Verified-zkEVM/VCV-io), a Lean framework for cryptographic security proofs with oracle computations, a probability semantics and a forking lemma.

BIP340 signing is the Fiat-Shamir transform of a Σ-protocol: commit to `r = x(k·G)` with an even-y nonce point, receive a challenge `e`, respond with `s = k + e·d`. Its verification check is exactly BIP340's `Verify` (`sigma_verify_eq_verify`).

| Theorem | Statement |
|---|---|
| `sigma_speciallySound` | Two accepting transcripts with the same `r` and different challenges reveal the secret key. |
| `sigma_hvzk` | **Perfect zero knowledge**: transcripts can be simulated without the secret key, with exactly the real distribution. |
| `sigma_simCommitPredictability` | A simulated `r` hits any fixed value with probability at most `1/|EvenNonce| = 2/(n-1)` (`two_mul_card_evenNonce`). |
| `normalize_uniform` | BIP340's normalization (`d = d'` or `n - d'`) of a uniform nonzero scalar is uniform over the scalars whose point has an even y. Keys and nonces are generated exactly this way in the model. |
| `euf_cma` | **BIP340 is unforgeable under chosen-message attacks in the random oracle model**, assuming it is hard to recover the secret key of a random public key: from a forger with success probability `ε` making `qS` signing and `qH` hash queries, VCVio's Pointcheval-Stern reduction recovers the key with probability at least `ε'·(ε'/(qH+1) - 1/n)`, where `ε' = ε - qS·(qS+qH)·2/(n-1)`. |
| `secp256k1_euf_cma` | The same bound for secp256k1. |

Modelling choices:
- The hash is a random oracle on `(message, r)`. BIP340 also hashes the public key into the challenge ("key prefixing"); that matters when an attacker targets many keys at once, not in this single-key experiment.
- Nonces are uniform nonzero scalars. Real BIP340 derives them from a hash, which a random oracle makes uniform.
- The hard problem is recovering the secret key of a random BIP340 public key (discrete log for a random even-y point).
- The bound is the textbook Pointcheval-Stern one. It loses roughly a factor of `qH`, so it doesn't give 128-bit security for secp256k1 by itself; tighter bounds need stronger idealizations (e.g. the algebraic group model).

### BIP340 batch verification with hash-derived coefficients — `Taproot/BIP340Batch.lean`

In practice the batch coefficients aren't independent random values. They are derived deterministically from the batch, and the attacker picks the batch. This file models them as a random oracle, in two ways:
- **Whole-batch derivation**, as in the BIP340 text (a seed hashing every input, expanded by a CSPRNG): the coefficient of signature `i ≥ 2` is a `b`-bit hash of `(batch, i)`.
- **Incremental derivation**, as in libsecp256k1's batch API: the coefficient of signature `i ≥ 2` is a `b`-bit hash of the first `i` entries, so the attacker can choose later entries after seeing earlier coefficients.

| Theorem | Statement |
|---|---|
| `batch_incremental_sound` | **Batch verification is sound in the random oracle model**: an attacker that makes at most `q` oracle queries and outputs batches of at most `ℓ` signatures gets a batch containing an invalid signature accepted with probability at most `(q + ℓ)/2^b` (`2^b ≤ n`). This holds for every choice of the challenge hash. |
| `batch_indexed_sound` | The same bound, `(q + ℓ)/2^b`, for whole-batch derivation. |
| `secp256k1_batch_indexed_sound`, `secp256k1_batch_incremental_sound` | Both bounds on secp256k1 with 128-bit coefficients: `(q + ℓ)/2^128`. |
| `batch_indexed_grind` | **The bound is tight up to the `ℓ` term**: from any valid signature, an explicit grinding attacker making `q` hash queries and outputting 2-signature batches gets an invalid batch accepted with probability at least `1 - (1 - 2^-b)^q` (about `q/2^b` while `q ≪ 2^b`), against the upper bound `(q + 2)/2^b`. |
| `prEvent_bad_le` | A generic random-oracle bad-event bound with a potential. It allows one fresh answer to complete several bad candidates, as long as earlier queries paid for them. |

The `q` term is inherent to deterministic coefficients, and `batch_indexed_grind` proves it: an attacker can grind batches offline, at one hash per try. With 128-bit coefficients, about `2^64` hash evaluations already give success probability about `2^-64`.

Proof idea (incremental): cut the winning batch after its last invalid signature. That prefix still passes, and its equation involves only coefficients of its own prefixes. The last of those to be answered must hit the single value that solves the equation. One fresh answer can complete many cached extensions of the queried prefix, but each cached prefix is completed only once, so the total stays at one bad value per query. Whole-batch derivation is simpler: one fresh answer completes at most one batch.

### BIP341: Taproot — `Taproot/BIP341.lean`
| Theorem | Statement |
|---|---|
| `outputKey_of_tweakSeckey` | Tweaking the secret key the BIP341 way gives exactly the secret key of the output key `Q = P + t·G`. |
| `keyPath_verify` | A signature made with the tweaked secret key verifies under the output key (key-path spending). |
| `computeRoot_of_mem` | Recomputing the Merkle root from any leaf and its path gives the script tree's root. |
| `verifyScriptPath_of_mem` | Every leaf of the committed script tree passes BIP341's control-block check (script-path spending). |
| `mem_of_computeRoot` | **Merkle binding**: with collision-free `TapLeaf`/`TapBranch` hashes, a leaf and path that recompute a tree's root are one of its leaves with its own path. |
| `mem_of_verifyScriptPath` | **Only committed scripts can be spent**: with collision-free hashes (including `TapTweak`), any leaf passing the control-block check is a leaf of the committed tree. |
| `verifyScriptPath_of_none` | A key-path-only output (no script tree) has no valid script-path spend. |

### BIP327: MuSig2 — `Taproot/MuSig2.lean`
| Theorem | Statement |
|---|---|
| `keyAgg_tweaks_invariant` | After `KeyAgg` and any sequence of tweaks: `Q = (gacc·Σ aᵢ·skᵢ + tacc)·G`. |
| `partialSigVerify_sign` | Honest partial signatures pass `PartialSigVerifyInternal`. |
| `verify_aggregate` | **If every partial signature passes partial verification, the aggregate is a valid BIP340 signature under the (tweaked) aggregate key**, regardless of who produced the partial signatures. Also covers MuSig2 adaptor signatures. |
| `verify_honest` | MuSig2 correctness for honest signers. |
| `outputKey_eq_applyTweak` | Applying the Taproot tweak as a MuSig2 x-only tweak gives exactly the BIP341 output key. |

### Discreet Log Contracts — `Taproot/DLC.lean`, `Taproot/DLCNumeric.lean`, `Taproot/MuSig2.lean`
| Theorem | Statement |
|---|---|
| `anticipate_of_verify` | A valid oracle attestation `(r, s)` of outcome `m` satisfies `s·G = R + e·P`, the point anticipated at setup. |
| `nonce_reuse_reveals_key` | An oracle that attests two outcomes with the same nonce reveals its secret key. |
| `anticipate_ne` | Different outcomes have different anticipation points, unless their challenge hashes collide. |
| `verify_adapt_wrong_outcome` | **Outcome binding**: the oracle's attestation of one outcome does not complete the adaptor signature of another outcome's CET. |
| `verify_adapt` | Any Schnorr adaptor pre-signature that passed pre-verification (even a malicious signer's) completes to a valid BIP340 signature once the secret is known. |
| `extract_of_verify` | Any valid completed signature reveals the adaptor secret, i.e. the oracle's attestation. |
| `settle` | DLC settlement through a Taproot **script path** (2-of-2 tapscript leaf). |
| `decomp_spec`, `decomp_unique` | **Numeric outcomes**: the digit-prefix decomposition of a payout interval `[lo, hi)` covers exactly the outcomes in the interval, each by exactly one prefix (one CET per outcome, never two). |
| `numeric_settle` | When the oracle attests each digit of an outcome in the interval, the sum of its digit attestations completes the adaptor signature of the one CET covering that outcome. |
| `settleKeyPath` | DLC settlement through the Taproot **key path**: the funding output's internal key is the MuSig2 aggregate of both parties, and completing their checked MuSig2 adaptor signature spends it. |

### BIP350: Bech32m — `Taproot/BIP350.lean`
| Theorem | Statement |
|---|---|
| `verify_createChecksum` | Checksums produced by the encoder always verify (Bech32 and Bech32m). |
| `not_both_valid` | No string is valid under both Bech32 and Bech32m. |
| `substitution_detected`, `verifyChecksum_substitution` | Changing any single data or checksum character is always detected. |
| `bech32_q_mutation` | **The Bech32 weakness that motivated BIP350**: in a valid Bech32 string ending in `p`, any number of `q`s can be inserted before the final `p`, or deleted, and the string stays valid. |
| `bech32_q_insertion_undetected_iff` | For Bech32, inserting 1–89 `q`s before the last character goes undetected **if and only if** that character is `p`. |
| `bech32m_q_insertion_detected`, `bech32m_q_deletion_detected` | **Bech32m fixes it**: inserting or deleting 1–89 `q`s before the last character (any character) always invalidates the checksum. |
| `two_substitutions_detected`, `verifyChecksum_two_substitutions` | Changing any two data or checksum characters (up to 88 positions apart, which covers every valid string) is always detected. |
| `burst_detected` | Any error confined to at most 6 consecutive characters is always detected. |

`Taproot/Summary.lean` restates the main results for the concrete `secp256k1` curve and prints the axioms each one depends on.

## secp256k1

`Taproot/Secp256k1.lean` defines the curve `y² = x³ + 7` over `𝔽_p` as a Mathlib `WeierstrassCurve` and uses Mathlib's proven group law on its points, associativity included. It then packages the curve as the interface the protocol proofs are written against (`Taproot/Curve.lean`):

- **`p` and `n` are prime.** Proven with Pratt certificates (a recursive chain of 24 primes) checked by the Lean kernel (`Taproot/Pratt.lean`, `Taproot/Primes.lean`). `scripts/gen_primes.gp` regenerates the certificates with [PARI/GP](https://pari.math.u-bordeaux.fr/).
- **`G` is on the curve.** Kernel computation.
- **`n·G = 0`.** Computed by double-and-add (`native_decide`, see below).
- **`lift_x` is correct.** Proven, using `p ≡ 3 (mod 4)` and the fact that no point has `y = 0` (`-7` is not a cube mod `p`).

The protocol proofs only use multiples of `G`, so they never need the number of points on the curve.

## Test vectors

The official test vectors run against the same definitions the theorems are about:

- **BIP340** (`Taproot/BIP340Vectors.lean`): a byte-level `PubKey`/`Sign`/`Verify` with SHA-256 tagged hashes (SHA-256 is implemented in Lean), built directly on the proven `BIP340.sign`/`verify`. All 19 vectors from `bip-0340/test-vectors.csv` pass: every verification result matches, and `Sign` reproduces every listed signature byte for byte. The run uses double-and-add implementations that are **proven equal** to the reference definitions.
- **BIP350** (`Taproot/BIP350Vectors.lean`): the string decoder, `convertbits` and segwit address rules, following the reference implementation. All Bech32m strings and segwit addresses from BIP350's test-vector section pass: valid ones decode correctly, re-encode to the same address and give the listed scriptPubKey, and invalid ones are rejected.

## Trust base

`lake build` prints `#print axioms` for the main results (end of `Taproot/Summary.lean`):

| Results | Axioms |
|---|---|
| BIP350 / Bech32m: all theorems and test vectors | Lean's standard axioms only (`propext`, `Classical.choice`, `Quot.sound`). Fully kernel-checked. |
| BIP340/341, MuSig2, DLC on secp256k1 | Standard axioms plus **one** `native_decide` computation: `n·G = 0` (`Secp256k1.n_smul_G`). |
| Generic results (batch verification, numeric DLC decomposition) | Standard axioms only. They hold for any curve satisfying the interface. |
| Batch verification in the random oracle model (`batch_indexed_sound`, `batch_incremental_sound`, `batch_indexed_grind`) | Standard axioms only; the secp256k1 versions add `n·G = 0`. |
| BIP340 EUF-CMA (`secp256k1_euf_cma`) | Standard axioms plus `n·G = 0`. VCVio's forking lemma and Fiat-Shamir reduction are fully proven (no `sorry`, no extra axioms). |
| BIP340 test vectors | Additionally use `native_decide` to run the vectors. |

`native_decide` trusts Lean's compiler in addition to its kernel. Every other computation, including all primality certificates, is checked by the kernel.

## Limitations

- **Unforgeability is proven only for BIP340 signatures**, as a reduction in the random oracle model (`euf_cma`). Its hardness assumption, discrete log on secp256k1, can't be proven, and the reduction's bound is the textbook Pointcheval-Stern one, which loses a factor of roughly `qH`. MuSig2, adaptor signatures and DLCs have no security reductions here. For example, nothing proves that a counterparty can't complete a DLC transaction for an outcome the oracle didn't attest by some means other than the attestation. What *is* proven about adversarial inputs: the robustness results (`verify_adapt`, `extract_of_verify`, `verify_aggregate`), the building blocks of security proofs (non-malleability, special soundness), batch-verification soundness against an adaptive attacker in the random oracle model, and the binding results under explicit collision-freeness hypotheses (script-tree binding, outcome binding).
- **Abstractions.** Hashes are arbitrary functions, transactions are reduced to the signed message, Bitcoin Script is not executed (the 2-of-2 leaf is modelled by what it checks), and byte encodings are left out except in the test-vector files. BIP340's range checks become types (`ZMod n`).
- **Group order.** Proving that secp256k1 has exactly `n` points (cofactor 1) needs point counting, which isn't done. So the MuSig2 results assume the public keys are multiples of `G`, and batch verification assumes `n·P = 0` for every point (`Curve.PrimeOrder`). Both hold for secp256k1.
- **MuSig2 details.** The aggregate nonce is assumed non-infinite (the honest case). BIP327's byte-level details (`GetSecondKey`, the key-sorting conventions, nonce generation) are part of the abstract hash functions.
- **Error detection.** For Bech32m, substitutions in up to 2 characters, bursts of up to 6 characters and the `q`-insertion/deletion pattern are proven. BIP173's full guarantee (any 4 substitutions) is not. Errors in the human-readable part are not covered.

## Building

Requirements: [elan](https://github.com/leanprover/elan), which installs the Lean toolchain pinned in `lean-toolchain`.

```sh
git clone https://github.com/dni/taproot-lean
cd taproot-lean
lake exe cache get   # download prebuilt Mathlib (several GB)
lake build
```

After the Mathlib cache is downloaded, the first build also compiles the needed parts of [VCVio](https://github.com/Verified-zkEVM/VCV-io) (about 3,000 files, which has no prebuilt cache), which can take an hour or more. Later builds take a few minutes. The build succeeding means every proof has been checked.

**Troubleshooting (Linux):** if the build fails with `undefined symbol` errors from Lean's bundled `clang`, your environment probably sets `LD_LIBRARY_PATH` to the system library directories, so the toolchain loads the system LLVM. Run `env -u LD_LIBRARY_PATH lake build`.

## Layout

```
Taproot/
  Curve.lean          the curve interface the protocols are proven against
  BIP340.lean         Schnorr signatures
  BIP340Props.lean    non-malleability, key extraction, batch verification
  BIP340Security.lean EUF-CMA unforgeability in the random oracle model (via VCVio)
  BIP340Batch.lean    batch verification soundness with hash-derived coefficients (ROM)
  BIP341.lean         Taproot: key tweaking, key path, script trees
  DLC.lean            oracle attestations, Schnorr adaptor signatures, outcome binding,
                      script-path settlement
  DLCNumeric.lean     numeric outcomes: digit-prefix CET decomposition and settlement
  MuSig2.lean         BIP327 MuSig2, MuSig2 adaptor signatures, key-path DLC settlement
  Secp256k1.lean      the concrete curve, built on Mathlib's elliptic curves
  Pratt.lean          kernel-checked Pratt primality certificates
  Primes.lean         primality of p and n (generated by scripts/gen_primes.gp)
  BIP340Vectors.lean  SHA-256, byte-level BIP340, official test vectors
  BIP350.lean         Bech32/Bech32m checksum and error-detection theorems
  BIP350Vectors.lean  Bech32m strings, segwit addresses, official test vectors
  Summary.lean        main results on secp256k1 and their axioms
```

## References

- [BIP340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki): Schnorr Signatures for secp256k1
- [BIP341](https://github.com/bitcoin/bips/blob/master/bip-0341.mediawiki): Taproot: SegWit version 1 spending rules
- [BIP327](https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki): MuSig2 for BIP340-compatible multi-signatures
- [BIP350](https://github.com/bitcoin/bips/blob/master/bip-0350.mediawiki): Bech32m format for v1+ witness addresses
- [sipa/bips#219](https://github.com/sipa/bips/issues/219), [sipa/bips#222](https://github.com/sipa/bips/pull/222): reducing BIP340 batch randomizers to 128 bits
- [DLC specifications](https://github.com/discreetlogcontracts/dlcspecs)
- Pointcheval, Stern: [Security Arguments for Digital Signatures and Blind Signatures](https://www.di.ens.fr/david.pointcheval/Documents/Papers/2000_joc.pdf) (J. Cryptology, 2000)
- [VCVio](https://github.com/Verified-zkEVM/VCV-io): formally verified cryptography proofs in Lean 4
