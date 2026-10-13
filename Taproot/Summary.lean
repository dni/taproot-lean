import Taproot.MuSig2
import Taproot.BIP340Props
import Taproot.BIP340Security
import Taproot.DLCNumeric
import Taproot.BIP350
import Taproot.BIP340Vectors
import Taproot.BIP350Vectors

/-!
# The main results, on secp256k1

The protocol theorems, specialized to the concrete curve `secp256k1`.
Each holds for **every** choice of the tagged hash functions.
-/

namespace Taproot

open Secp256k1 BIP340 BIP341 DLC MuSig2

variable {M : Type*} (challenge : F → F → M → ZMod n) (nonce : ZMod n → F → M → ZMod n)

/-- BIP340: every Schnorr signature made with `sk` verifies under `sk`'s public key. -/
theorem secp256k1_schnorr_correct {sk : ZMod n} {m : M} {pk : F} {sig : F × ZMod n}
    (hpk : pubkey secp256k1 sk = some pk) (hsig : sign secp256k1 challenge nonce sk m = some sig) :
    verify secp256k1 challenge pk m sig = true :=
  verify_sign secp256k1 challenge nonce hpk hsig

/-- BIP341 key path: signing with the tweaked secret key verifies under the output key. -/
theorem secp256k1_taproot_keyPath {T : Type*} (tweak : F → Option T → ZMod n)
    {sk d : ZMod n} {root : Option T} {p q : F} {parity : Bool} {m : M} {sig : F × ZMod n}
    (hpk : pubkey secp256k1 sk = some p) (hd : tweakSeckey secp256k1 tweak sk root = some d)
    (hQ : outputKey secp256k1 tweak p root = some (q, parity))
    (hsig : sign secp256k1 challenge nonce d m = some sig) :
    verify secp256k1 challenge q m sig = true :=
  keyPath_verify secp256k1 tweak challenge nonce hpk hd hQ hsig

/-- BIP341 script path: every leaf of the committed script tree passes the
control-block check with its Merkle path. -/
theorem secp256k1_taproot_scriptPath {L T : Type*} [LinearOrder T] (leafHash : L → T)
    (branch : T → T → T) (tweak : F → Option T → ZMod n) (t : ScriptTree L)
    {p q : F} {parity : Bool} {l : L} {path : List T}
    (hQ : outputKey secp256k1 tweak p (some (t.root leafHash branch)) = some (q, parity))
    (hmem : (l, path) ∈ t.paths leafHash branch) :
    verifyScriptPath secp256k1 leafHash branch tweak q parity p l path = true :=
  verifyScriptPath_of_mem secp256k1 leafHash branch tweak t hQ hmem

/-- DLC: Schnorr adaptor soundness. Any pre-signature that passed pre-verification
completes to a valid BIP340 signature once `t` with `t·G = T` is known. -/
theorem secp256k1_adaptor_sound {pk : F} {T : Point} {m : M} {ps : PreSig n Point} {t : ZMod n}
    (hpre : preVerify secp256k1 challenge pk T m ps = true) (ht : secp256k1.mulG t = T) :
    verify secp256k1 challenge pk m (adapt secp256k1 ps t) = true :=
  verify_adapt secp256k1 challenge hpre ht

/-- DLC: any valid completion of a checked pre-signature reveals the discrete log of `T`. -/
theorem secp256k1_adaptor_extract {pk : F} {T : Point} {m : M} {ps : PreSig n Point}
    {sig : F × ZMod n} (hpre : preVerify secp256k1 challenge pk T m ps = true)
    (hsig : verify secp256k1 challenge pk m sig = true) (hr : sig.1 = secp256k1.x ps.R) :
    secp256k1.mulG (extract secp256k1 ps sig) = T :=
  extract_of_verify secp256k1 challenge hpre hsig hr

/-- DLC: an oracle that reuses its nonce for two outcomes reveals its secret key. -/
theorem secp256k1_oracle_nonce_reuse {sk k : ZMod n} {m₁ m₂ : M} {pk r₁ r₂ : F} {s₁ s₂ : ZMod n}
    (hpk : pubkey secp256k1 sk = some pk)
    (h₁ : attest secp256k1 challenge sk k m₁ = some (r₁, s₁))
    (h₂ : attest secp256k1 challenge sk k m₂ = some (r₂, s₂))
    (he : challenge r₁ pk m₁ ≠ challenge r₂ pk m₂) :
    pubkey secp256k1 ((s₁ - s₂) / (challenge r₁ pk m₁ - challenge r₂ pk m₂)) = some pk :=
  nonce_reuse_reveals_key secp256k1 challenge hpk h₁ h₂ he

/-- DLC settlement: with the oracle's attestation of outcome `o`, Bob completes
Alice's checked adaptor pre-signature and spends the Taproot funding output
through the 2-of-2 script leaf with that outcome's CET. -/
theorem secp256k1_dlc_settle {T : Type*} [LinearOrder T] (leafHash : Multisig2 F → T)
    (branch : T → T → T) (tweak : F → Option T → ZMod n) (tree : ScriptTree (Multisig2 F))
    {p q : F} {parity : Bool} {pkA pkB : F} {path : List T}
    {opk r : F} {o msg : M} {S : Point} {psA : PreSig n Point} {skB s : ZMod n}
    {sigB : F × ZMod n}
    (hQ : outputKey secp256k1 tweak p (some (tree.root leafHash branch)) = some (q, parity))
    (hleaf : (⟨pkA, pkB⟩, path) ∈ tree.paths leafHash branch)
    (hS : anticipate secp256k1 challenge opk r o = some S)
    (hpre : preVerify secp256k1 challenge pkA S msg psA = true)
    (hpkB : pubkey secp256k1 skB = some pkB)
    (hsigB : sign secp256k1 challenge nonce skB msg = some sigB)
    (hatt : verify secp256k1 challenge opk o (r, s) = true) :
    spendValid secp256k1 challenge leafHash branch tweak q parity p ⟨pkA, pkB⟩ path msg
      (adapt secp256k1 psA s) sigB = true :=
  settle secp256k1 challenge leafHash branch tweak nonce tree hQ hleaf hS hpre hpkB hsigB hatt

/-- MuSig2 (BIP327): if every partial signature passed partial verification,
the aggregate is a valid BIP340 signature under the (tweaked) aggregate key. -/
theorem secp256k1_musig2_sound (aggCoef : List Point → Point → ZMod n)
    (nonceCoef : Point → Point → F → M → ZMod n) (parts : List (Part n Point))
    (hP : ∀ x ∈ parts, x.2.1.P = secp256k1.mulG x.1) (tweaks : List (ZMod n × Bool))
    {ctx₀ ctx : KeyAggCtx n Point}
    (h₀ : keyAgg aggCoef ((parts.map (·.1)).map secp256k1.mulG) = some ctx₀)
    (h : applyTweaks secp256k1 ctx₀ tweaks = some ctx) (m : M)
    (hR : aggNonce (parts.map (·.2.1))
      (session secp256k1 nonceCoef challenge ctx (parts.map (·.2.1)) 0 m).b 0 ≠ 0)
    (hpart : ∀ x ∈ parts, partialSigVerify secp256k1 aggCoef ctx
      ((parts.map (·.1)).map secp256k1.mulG)
      (session secp256k1 nonceCoef challenge ctx (parts.map (·.2.1)) 0 m) x.2.1 x.2.2 = true) :
    let sig := partialSigAgg secp256k1 ctx
      (session secp256k1 nonceCoef challenge ctx (parts.map (·.2.1)) 0 m) (parts.map (·.2.2))
    verify secp256k1 challenge (secp256k1.x ctx.Q) m (secp256k1.x sig.R, sig.s) = true := by
  intro sig
  have := verify_aggregate secp256k1 aggCoef nonceCoef challenge parts hP tweaks h₀ h
    (map_zero _) m hR hpart
  rwa [adapt_zero] at this

/-- DLC through the Taproot key path: the funding output key is the
Taproot-tweaked MuSig2 aggregate of Alice and Bob, and after the oracle
attests, completing their checked MuSig2 adaptor signature spends it. -/
theorem secp256k1_dlc_settle_keyPath {T' : Type*} (aggCoef : List Point → Point → ZMod n)
    (nonceCoef : Point → Point → F → M → ZMod n) (tweak : F → Option T' → ZMod n)
    (root : Option T') (alice bob : Part n Point)
    (hA : alice.2.1.P = secp256k1.mulG alice.1) (hB : bob.2.1.P = secp256k1.mulG bob.1)
    {ctx₀ ctx : KeyAggCtx n Point}
    (h₀ : keyAgg aggCoef ([alice.1, bob.1].map secp256k1.mulG) = some ctx₀)
    (htw : applyTweak secp256k1 ctx₀ (tweak (secp256k1.x ctx₀.Q) root) true = some ctx)
    {opk r : F} {o msg : M} {S : Point} {s : ZMod n}
    (hS : anticipate secp256k1 challenge opk r o = some S)
    (hR : aggNonce [alice.2.1, bob.2.1]
      (session secp256k1 nonceCoef challenge ctx [alice.2.1, bob.2.1] S msg).b S ≠ 0)
    (hpartA : partialSigVerify secp256k1 aggCoef ctx ([alice.1, bob.1].map secp256k1.mulG)
      (session secp256k1 nonceCoef challenge ctx [alice.2.1, bob.2.1] S msg) alice.2.1 alice.2.2
        = true)
    (hpartB : partialSigVerify secp256k1 aggCoef ctx ([alice.1, bob.1].map secp256k1.mulG)
      (session secp256k1 nonceCoef challenge ctx [alice.2.1, bob.2.1] S msg) bob.2.1 bob.2.2
        = true)
    (hatt : verify secp256k1 challenge opk o (r, s) = true) :
    outputKey secp256k1 tweak (secp256k1.x ctx₀.Q) root =
      some (secp256k1.x ctx.Q, secp256k1.hasEvenY ctx.Q) ∧
    verify secp256k1 challenge (secp256k1.x ctx.Q) msg
      (adapt secp256k1 (partialSigAgg secp256k1 ctx
        (session secp256k1 nonceCoef challenge ctx [alice.2.1, bob.2.1] S msg)
        [alice.2.2, bob.2.2]) s) = true :=
  settleKeyPath secp256k1 aggCoef nonceCoef challenge tweak root alice bob hA hB h₀ htw hS hR
    hpartA hpartB hatt

/-- BIP340 non-malleability: a public key, message and `r` determine `s`. -/
theorem secp256k1_schnorr_unique {pk : F} {m : M} {r : F} {s s' : ZMod n}
    (h : verify secp256k1 challenge pk m (r, s) = true)
    (h' : verify secp256k1 challenge pk m (r, s') = true) : s = s' :=
  verify_unique secp256k1 challenge h h'

/-- BIP340 special soundness: two valid signatures sharing `r` on different
challenges reveal the secret key. -/
theorem secp256k1_schnorr_extract {sk : ZMod n} {pk : F} {m₁ m₂ : M} {r : F} {s₁ s₂ : ZMod n}
    (hpk : pubkey secp256k1 sk = some pk)
    (h₁ : verify secp256k1 challenge pk m₁ (r, s₁) = true)
    (h₂ : verify secp256k1 challenge pk m₂ (r, s₂) = true)
    (he : challenge r pk m₁ ≠ challenge r pk m₂) :
    (s₁ - s₂) / (challenge r pk m₁ - challenge r pk m₂) = secp256k1.evenScalar sk :=
  (extract_secret secp256k1 challenge hpk h₁ h₂ he).1

/-- BIP341 script-path binding: with collision-free hashes, only leaves of the
committed script tree pass the control-block check. -/
theorem secp256k1_taproot_scriptPath_binding {L T : Type*} [LinearOrder T] (leafHash : L → T)
    (branch : T → T → T) (tweak : F → Option T → ZMod n) (t : ScriptTree L) {p q : F}
    (htweak : Function.Injective (tweak p)) (hleaf : Function.Injective leafHash)
    (hbranch : ∀ a b c d, branch a b = branch c d → a = c ∧ b = d)
    (hsep : ∀ l a b, leafHash l ≠ branch a b) {parity : Bool} {l : L} {path : List T}
    (hQ : outputKey secp256k1 tweak p (some (t.root leafHash branch)) = some (q, parity))
    (hv : verifyScriptPath secp256k1 leafHash branch tweak q parity p l path = true) :
    (l, path) ∈ t.paths leafHash branch :=
  mem_of_verifyScriptPath secp256k1 tweak t htweak hleaf hbranch hsep hQ hv

/-- DLC outcome binding: the attestation of one outcome does not complete the
CET adaptor signature of another. -/
theorem secp256k1_dlc_wrong_outcome {osk : ZMod n} {opk r pk : F} {m m' msg : M} {S : Point}
    {ps : PreSig n Point} {s : ZMod n}
    (hopk : pubkey secp256k1 osk = some opk) (hS : anticipate secp256k1 challenge opk r m = some S)
    (hpre : preVerify secp256k1 challenge pk S msg ps = true)
    (hatt : verify secp256k1 challenge opk m' (r, s) = true)
    (hne : challenge r opk m ≠ challenge r opk m') :
    verify secp256k1 challenge pk msg (adapt secp256k1 ps s) = false :=
  verify_adapt_wrong_outcome secp256k1 challenge hopk hS hpre hatt hne

open OracleComp in
/-- **BIP340 on secp256k1 is EUF-CMA secure in the random oracle model**,
assuming key recovery for random public keys is hard: from any forger with
success probability `ε` making at most `qS` signing and `qH` hash queries, the
reduction recovers the secret key with probability at least
`ε' · (ε' / (qH + 1) - 1/n)`, where `ε' = ε - qS · (qS + qH) · 2/(n - 1)`. -/
theorem secp256k1_euf_cma (M' : Type) [DecidableEq M']
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamir.inROM (BIP340Security.sigma secp256k1) (BIP340Security.keyGen secp256k1) M'))
    (qS qH : ℕ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M') (Commit := F) (Chal := ZMod n)
      (S' := F × ZMod n) (oa := adv.main pk) qS qH) :
    let eps := SignatureAlg.unforgeableAdvantage
        (FiatShamir.runtime (Commit := F) (Chal := ZMod n) M') adv -
      (qS : ENNReal) * (qS + qH) * (2 / ((n - 1 : ℕ) : ENNReal))
    eps * (eps / (qH + 1 : ENNReal) - FiatShamir.challengeSpaceInv (ZMod n)) ≤
      Pr{let x ← (hardRelationExperiment (BIP340Security.keyGen secp256k1)
        (FiatShamir.cmaReduction (BIP340Security.sigma secp256k1)
          (BIP340Security.keyGen secp256k1) M' (BIP340Security.simTranscript secp256k1)
          adv qH))}[x = true] :=
  BIP340Security.euf_cma secp256k1 M' adv qS qH hQ

end Taproot

/-! ## What the proofs rely on -/

#print axioms Taproot.secp256k1_schnorr_correct
#print axioms Taproot.secp256k1_taproot_keyPath
#print axioms Taproot.secp256k1_taproot_scriptPath
#print axioms Taproot.secp256k1_dlc_settle
#print axioms Taproot.secp256k1_adaptor_extract
#print axioms Taproot.secp256k1_oracle_nonce_reuse
#print axioms Taproot.secp256k1_musig2_sound
#print axioms Taproot.secp256k1_dlc_settle_keyPath
#print axioms Taproot.secp256k1_euf_cma
#print axioms Taproot.secp256k1_schnorr_unique
#print axioms Taproot.secp256k1_schnorr_extract
#print axioms Taproot.secp256k1_taproot_scriptPath_binding
#print axioms Taproot.secp256k1_dlc_wrong_outcome
#print axioms Taproot.DLC.Numeric.numeric_settle
#print axioms Taproot.BIP340.batchVerify_sound
#print axioms Bech32.verify_createChecksum
#print axioms Bech32.verifyChecksum_substitution
#print axioms Bech32.bech32m_q_insertion_detected
#print axioms Bech32.bech32_q_insertion_undetected_iff
#print axioms Bech32.verifyChecksum_two_substitutions
#print axioms Bech32.burst_detected
#print axioms Bech32.validSegwit_ok
#print axioms Taproot.BIP340Vectors.vectors_verify
#print axioms Taproot.BIP340Vectors.vectors_sign
