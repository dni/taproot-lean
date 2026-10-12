# taproot-lean

Machine-checked proofs, in [Lean 4](https://lean-lang.org) with [Mathlib](https://github.com/leanprover-community/mathlib4), about the cryptography behind Bitcoin's Taproot upgrade:

- Schnorr signatures (BIP340)
- Taproot outputs (BIP341)
- MuSig2 multi-signatures (BIP327)
- Bech32m addresses (BIP350)
- Discreet Log Contracts (DLCs) built on top of them

The proofs work over a **concrete secp256k1 curve**, built from Mathlib's elliptic-curve group law, not over an assumed abstract group. The primes `p` and `n` are proven prime inside Lean.

Repository: <https://github.com/dni/taproot-lean>

## What is proven

Unless stated otherwise, every result holds for **all** choices of the tagged hash functions. Hashes are modelled as arbitrary functions, so no property of SHA-256 is assumed. All results are *correctness* properties: when the parties follow the protocol, everything verifies. Security properties such as unforgeability are not covered (see [Limitations](#limitations)).

### BIP340: Schnorr signatures — `Taproot/BIP340.lean`
| Theorem | Statement |
|---|---|
| `verify_sign` | Every signature produced by `Sign` with secret key `sk` is accepted by `Verify` under `sk`'s public key. |

### BIP341: Taproot — `Taproot/BIP341.lean`
| Theorem | Statement |
|---|---|
| `outputKey_of_tweakSeckey` | Tweaking the secret key the BIP341 way gives exactly the secret key of the output key `Q = P + t·G`. |
| `keyPath_verify` | A signature made with the tweaked secret key verifies under the output key (key-path spending). |
| `computeRoot_of_mem` | Recomputing the Merkle root from any leaf and its path gives the script tree's root. |
| `verifyScriptPath_of_mem` | Every leaf of the committed script tree passes BIP341's control-block check (script-path spending). |

### BIP327: MuSig2 — `Taproot/MuSig2.lean`
| Theorem | Statement |
|---|---|
| `keyAgg_tweaks_invariant` | After `KeyAgg` and any sequence of tweaks: `Q = (gacc·Σ aᵢ·skᵢ + tacc)·G`. |
| `partialSigVerify_sign` | Honest partial signatures pass `PartialSigVerifyInternal`. |
| `verify_aggregate` | **If every partial signature passes partial verification, the aggregate is a valid BIP340 signature under the (tweaked) aggregate key**, regardless of who produced the partial signatures. Also covers MuSig2 adaptor signatures. |
| `verify_honest` | MuSig2 correctness for honest signers. |
| `outputKey_eq_applyTweak` | Applying the Taproot tweak as a MuSig2 x-only tweak gives exactly the BIP341 output key. |

### Discreet Log Contracts — `Taproot/DLC.lean`, `Taproot/MuSig2.lean`
| Theorem | Statement |
|---|---|
| `anticipate_of_verify` | A valid oracle attestation `(r, s)` of outcome `m` satisfies `s·G = R + e·P`, the point anticipated at setup. |
| `nonce_reuse_reveals_key` | An oracle that attests two outcomes with the same nonce reveals its secret key. |
| `verify_adapt` | Any Schnorr adaptor pre-signature that passed pre-verification (even a malicious signer's) completes to a valid BIP340 signature once the secret is known. |
| `extract_of_verify` | Any valid completed signature reveals the adaptor secret, i.e. the oracle's attestation. |
| `settle` | DLC settlement through a Taproot **script path** (2-of-2 tapscript leaf). |
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
| BIP340 test vectors | Additionally use `native_decide` to run the vectors. |

`native_decide` trusts Lean's compiler in addition to its kernel. Every other computation, including all primality certificates, is checked by the kernel.

## Limitations

- **Correctness, not security.** These are not unforgeability or security proofs: they rely on no hardness assumption and say nothing about adversaries who don't follow the protocol. For example, nothing here proves that a counterparty can't complete a DLC transaction for an outcome the oracle didn't attest. The exceptions are the robustness results: `verify_adapt`, `extract_of_verify` and `verify_aggregate` hold for *any* inputs that pass the respective checks.
- **Abstractions.** Hashes are arbitrary functions, transactions are reduced to the signed message, Bitcoin Script is not executed (the 2-of-2 leaf is modelled by what it checks), and byte encodings are left out except in the test-vector files. BIP340's range checks become types (`ZMod n`).
- **MuSig2 details.** MuSig2 public keys are assumed to be multiples of `G` (every secp256k1 point is, but that isn't proven here), and the aggregate nonce is assumed non-infinite (the honest case). BIP327's byte-level details (`GetSecondKey`, the key-sorting conventions, nonce generation) are part of the abstract hash functions.
- **Error detection.** For Bech32m, only single substitutions and the `q`-insertion/deletion pattern are proven. The BCH guarantee of detecting up to 4 substitutions is not.

## Building

Requirements: [elan](https://github.com/leanprover/elan), which installs the Lean toolchain pinned in `lean-toolchain`.

```sh
git clone https://github.com/dni/taproot-lean
cd taproot-lean
lake exe cache get   # download prebuilt Mathlib (several GB)
lake build
```

Building the project itself takes a few minutes after the Mathlib cache is downloaded. The build succeeding means every proof has been checked.

**Troubleshooting (Linux):** if the build fails with `undefined symbol` errors from Lean's bundled `clang`, your environment probably sets `LD_LIBRARY_PATH` to the system library directories, so the toolchain loads the system LLVM. Run `env -u LD_LIBRARY_PATH lake build`.

## Layout

```
Taproot/
  Curve.lean          the curve interface the protocols are proven against
  BIP340.lean         Schnorr signatures
  BIP341.lean         Taproot: key tweaking, key path, script trees
  DLC.lean            oracle attestations, Schnorr adaptor signatures, script-path settlement
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
- [DLC specifications](https://github.com/discreetlogcontracts/dlcspecs)
