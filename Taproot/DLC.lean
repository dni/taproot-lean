import Taproot.BIP341

/-!
# Discreet Log Contracts with Schnorr and Taproot

A DLC lets two parties lock funds in a Taproot output and settle according to
an oracle's attestation of an outcome, without the oracle learning about the
contract. This file proves the cryptographic steps it relies on, using BIP340
Schnorr signatures throughout:

* **Oracle**: the announcement is the oracle's key `P` and a pre-committed
  nonce point `R`. For each outcome `m` anyone can compute the
  *anticipation point* `S_m = R + e_m·P`. A valid attestation of `m` is a
  BIP340 signature `(r, s)` with `s·G = S_m` (`anticipate_of_verify`).
* **Adaptor signatures**: a pre-signature locked to a point `T` becomes a
  valid BIP340 signature once completed with `t` where `t·G = T`
  (`verify_adapt`, which holds for *any* pre-signature that passed
  pre-verification, so the receiver does not need to trust the signer),
  and any valid completion reveals `t` (`extract_of_verify`).
* **Oracle penalty**: attesting two outcomes with the same nonce reveals the
  oracle's secret key (`nonce_reuse_reveals_key`).
* **Settlement**: given a Taproot funding output committing to a 2-of-2
  tapscript leaf, an adaptor pre-signature for an outcome's contract execution
  transaction (CET), and the oracle's attestation of that outcome, the
  receiving party can produce a valid script-path spend (`settle`).

As in `BIP340`/`BIP341`, hashes are arbitrary functions and transactions are
abstracted to the message `M` being signed. These are correctness
properties; unforgeability (e.g. that nobody can complete a CET for an outcome
the oracle did not attest) rests on the discrete log assumption and is not
proven here.
-/

namespace Taproot.DLC

open Curve BIP340 BIP341

variable {n : ℕ} [Fact n.Prime] {E X M : Type*} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-! ## Oracle attestations -/

/-- The anticipation point `S_m = R + e·P` for outcome `m`, computed from the
oracle's announcement (public key `pk`, nonce x-coordinate `r`). -/
def anticipate (pk r : X) (m : M) : Option E :=
  match C.liftX pk, C.liftX r with
  | some P, some R => some (R + (challenge r pk m).val • P)
  | _, _ => none

/-- An oracle with secret key `sk` and pre-committed nonce `k` attests to
outcome `m` by BIP340-signing it with nonce `k`. -/
def attest (sk k : ZMod n) (m : M) : Option (X × ZMod n) :=
  sign C challenge (fun _ _ _ => k) sk m

/-- **Attestations unlock the anticipated point**: if `(r, s)` is a valid
BIP340 signature of `m` under `pk`, then `s·G` is exactly the point
anticipated for `m`. -/
theorem anticipate_of_verify {pk r : X} {m : M} {s : ZMod n}
    (h : verify C challenge pk m (r, s) = true) :
    anticipate C challenge pk r m = some (C.mulG s) := by
  unfold verify at h
  split at h
  · cases h
  · rename_i P hP
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hR0, hReven⟩, hRx⟩ := h
    have hR := C.liftX_x _ hR0 hReven
    rw [hRx] at hR
    simp [anticipate, hP, hR]

omit [DecidableEq E] [DecidableEq X] in
/-- The oracle's attestation uses its announced nonce: `r = x(k·G)`. -/
theorem attest_r {sk k : ZMod n} {m : M} {sig : X × ZMod n}
    (h : attest C challenge sk k m = some sig) : sig.1 = C.x (C.mulG k) := by
  unfold attest sign at h
  dsimp only at h
  split_ifs at h
  cases h
  rfl

omit [DecidableEq E] [DecidableEq X] in
/-- **Honest attestations unlock the anticipated point**: the scalar published
by an honest oracle is the discrete log of the anticipation point computed
from its announcement. -/
theorem anticipate_attest {sk k : ZMod n} {m : M} {pk : X} {sig : X × ZMod n}
    (hpk : pubkey C sk = some pk) (h : attest C challenge sk k m = some sig) :
    anticipate C challenge pk (C.x (C.mulG k)) m = some (C.mulG sig.2) := by
  classical
  have hv := verify_sign C challenge (fun _ _ _ => k) hpk h
  rw [← attest_r C challenge h]
  exact anticipate_of_verify C challenge hv

omit [DecidableEq E] [DecidableEq X] in
/-- **Oracle penalty**: if the oracle attests two outcomes with the same
nonce (and their challenges differ), anyone can compute a secret key for the
oracle's public key from the two signatures. -/
theorem nonce_reuse_reveals_key {sk k : ZMod n} {m₁ m₂ : M} {pk r₁ r₂ : X} {s₁ s₂ : ZMod n}
    (hpk : pubkey C sk = some pk)
    (h₁ : attest C challenge sk k m₁ = some (r₁, s₁))
    (h₂ : attest C challenge sk k m₂ = some (r₂, s₂))
    (he : challenge r₁ pk m₁ ≠ challenge r₂ pk m₂) :
    pubkey C ((s₁ - s₂) / (challenge r₁ pk m₁ - challenge r₂ pk m₂)) = some pk := by
  unfold pubkey at hpk
  unfold attest sign at h₁ h₂
  dsimp only at h₁ h₂
  split_ifs at hpk h₁ h₂ with hsk hk
  cases hpk
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
  -- s₁ - s₂ = (e₁ - e₂)·d, so the quotient is the (normalized) secret key `d`.
  have hd : ((C.evenScalar k + challenge (C.x (C.mulG k)) (C.x (C.mulG sk)) m₁ * C.evenScalar sk) -
      (C.evenScalar k + challenge (C.x (C.mulG k)) (C.x (C.mulG sk)) m₂ * C.evenScalar sk)) /
      (challenge (C.x (C.mulG k)) (C.x (C.mulG sk)) m₁ -
        challenge (C.x (C.mulG k)) (C.x (C.mulG sk)) m₂) = C.evenScalar sk := by
    rw [add_sub_add_left_eq_sub, ← sub_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr he)]
  rw [hd]
  simp [pubkey, C.evenScalar_ne_zero hsk, C.x_evenScalar]

/-! ## Schnorr adaptor signatures -/

/-- An adaptor pre-signature: the nonce point `R` (= `k·G + T`, the final
nonce up to sign) and the pre-signature scalar `s'`. -/
structure PreSig (n : ℕ) (E : Type*) where
  R : E
  s : ZMod n

/-- Create a pre-signature on `m` with secret key `sk`, locked to point `T`. -/
def presign (nonce : ZMod n → X → M → E → ZMod n) (sk : ZMod n) (T : E) (m : M) :
    Option (PreSig n E) :=
  if sk = 0 then none else
  let P := C.mulG sk
  let d := C.evenScalar sk
  let k := nonce d (C.x P) m T
  let R := C.mulG k + T
  if R = 0 then none else
  let e := challenge (C.x R) (C.x P) m
  some ⟨R, (if C.hasEvenY R then k else -k) + e * d⟩

/-- Check a pre-signature against the signer's public key and the lock point `T`:
`s'·G = ±(R - T) + e·P`, with the sign chosen so the final nonce has even y. -/
def preVerify (pk : X) (T : E) (m : M) (ps : PreSig n E) : Bool :=
  match C.liftX pk with
  | none => false
  | some P =>
    let e := challenge (C.x ps.R) pk m
    decide (ps.R ≠ 0) &&
    decide (C.mulG ps.s = (if C.hasEvenY ps.R then ps.R - T else -(ps.R - T)) + e.val • P)

/-- Complete a pre-signature with the secret `t` (where `t·G = T`). -/
def adapt (ps : PreSig n E) (t : ZMod n) : X × ZMod n :=
  (C.x ps.R, if C.hasEvenY ps.R then ps.s + t else ps.s - t)

/-- Recover the secret `t` from a pre-signature and its completed signature. -/
def extract (ps : PreSig n E) (sig : X × ZMod n) : ZMod n :=
  if C.hasEvenY ps.R then sig.2 - ps.s else ps.s - sig.2

omit [DecidableEq X] in
/-- Honestly created pre-signatures pass pre-verification. -/
theorem preVerify_presign (nonce : ZMod n → X → M → E → ZMod n) {sk : ZMod n} {T : E} {m : M}
    {pk : X} {ps : PreSig n E}
    (hpk : pubkey C sk = some pk) (hps : presign C challenge nonce sk T m = some ps) :
    preVerify C challenge pk T m ps = true := by
  unfold pubkey at hpk
  unfold presign at hps
  dsimp only at hps
  split_ifs at hpk hps with hsk hR heven <;>
  · cases hpk
    cases hps
    simp only [preVerify, C.liftX_x_mulG hsk, C.val_smul_mulG, add_sub_cancel_right]
    simp [hR, heven]

/-- **Adaptor soundness**: if a pre-signature passes pre-verification, then
completing it with `t` (where `t·G = T`) gives a valid BIP340 signature.
This holds for any pre-signature, not only honestly made ones. -/
theorem verify_adapt {pk : X} {T : E} {m : M} {ps : PreSig n E} {t : ZMod n}
    (hpre : preVerify C challenge pk T m ps = true) (ht : C.mulG t = T) :
    verify C challenge pk m (adapt C ps t) = true := by
  unfold preVerify at hpre
  split at hpre
  · cases hpre
  · rename_i P hP
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpre
    obtain ⟨hR0, hs⟩ := hpre
    simp only [verify, hP, adapt]
    split_ifs at hs ⊢ with heven
    · -- even nonce: (s' + t)·G - e·P = R
      have : C.mulG ps.s + C.mulG t - (challenge (C.x ps.R) pk m).val • P = ps.R := by
        rw [hs, ht]; abel
      simp [this, hR0, heven]
    · -- odd nonce: (s' - t)·G - e·P = -R, which has even y and the same x
      have : C.mulG ps.s - C.mulG t - (challenge (C.x ps.R) pk m).val • P = -ps.R := by
        rw [hs, ht]; abel
      simp [this, hR0, C.hasEvenY_neg _ hR0, heven, C.x_neg]

omit [DecidableEq E] [DecidableEq X] in
/-- Extraction undoes adaptation. -/
theorem extract_adapt (ps : PreSig n E) (t : ZMod n) : extract C ps (adapt C ps t) = t := by
  unfold extract adapt
  split_ifs <;> ring

/-- **Adaptor extraction**: from a pre-signature that passed pre-verification
and *any* valid signature with the same nonce, the extracted value is a
discrete log of `T`. (In a DLC: seeing the counterparty's completed CET
signature reveals the oracle's attestation.) -/
theorem extract_of_verify {pk : X} {T : E} {m : M} {ps : PreSig n E} {sig : X × ZMod n}
    (hpre : preVerify C challenge pk T m ps = true) (hsig : verify C challenge pk m sig = true)
    (hr : sig.1 = C.x ps.R) :
    C.mulG (extract C ps sig) = T := by
  obtain ⟨r, s⟩ := sig
  simp only at hr
  subst hr
  unfold preVerify at hpre
  unfold verify at hsig
  split at hpre
  · cases hpre
  · rename_i P hP
    rw [hP] at hsig
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpre hsig
    obtain ⟨hR0, hs'⟩ := hpre
    obtain ⟨⟨hN0, hNeven⟩, hNx⟩ := hsig
    -- The verified nonce point `N = s·G - e·P` is the even-y point with x = x(R).
    have hN := C.liftX_x _ hN0 hNeven
    unfold extract
    split_ifs at hs' ⊢ with heven
    · have hR := C.liftX_x _ hR0 heven
      rw [hNx, hR, Option.some.injEq] at hN
      rw [map_sub, hs', sub_eq_iff_eq_add.mp hN.symm]; abel
    · have hR := C.liftX_x _ (neg_ne_zero.mpr hR0)
        (by rw [C.hasEvenY_neg _ hR0]; simpa using heven)
      rw [C.x_neg, ← hNx, hN, Option.some.injEq] at hR
      rw [map_sub, hs', sub_eq_iff_eq_add.mp hR]; abel

/-! ## Settlement through a Taproot script path -/

/-- The DLC funding leaf: a 2-of-2 tapscript between Alice and Bob
(`<A> OP_CHECKSIGVERIFY <B> OP_CHECKSIG`). -/
structure Multisig2 (X : Type*) where
  a : X
  b : X

/-- The 2-of-2 leaf is satisfied when both signatures verify on the spending
transaction's signature message. -/
def Multisig2.satisfied (leaf : Multisig2 X) (msg : M) (sigA sigB : X × ZMod n) : Bool :=
  verify C challenge leaf.a msg sigA && verify C challenge leaf.b msg sigB

/-- A script-path spend of a Taproot output through a 2-of-2 leaf is valid when
the control block passes BIP341's commitment check and the leaf is satisfied. -/
def spendValid {T : Type*} [LinearOrder T] (leafHash : Multisig2 X → T) (branch : T → T → T)
    (tweak : X → Option T → ZMod n) (q : X) (parity : Bool) (p : X)
    (leaf : Multisig2 X) (path : List T) (msg : M) (sigA sigB : X × ZMod n) : Bool :=
  verifyScriptPath C leafHash branch tweak q parity p leaf path &&
    leaf.satisfied C challenge msg sigA sigB

/-- **DLC settlement**: suppose
* the funding output `q` commits to a script tree containing the 2-of-2 leaf
  for Alice's key `pkA` and Bob's key `pkB`,
* at setup Bob checked Alice's adaptor pre-signature `psA` on the CET for
  outcome `o`, locked to the anticipation point `S` of `o`,
* Bob can sign the CET himself,
* the oracle publishes a valid attestation `(r, s)` of `o`.

Then completing Alice's pre-signature with `s` gives Bob a valid Taproot
script-path spend of the funding output by the CET. -/
theorem settle {T : Type*} [LinearOrder T] (leafHash : Multisig2 X → T) (branch : T → T → T)
    (tweak : X → Option T → ZMod n) (nonce : ZMod n → X → M → ZMod n)
    (tree : ScriptTree (Multisig2 X)) {p q : X} {parity : Bool} {pkA pkB : X} {path : List T}
    {opk r : X} {o msg : M} {S : E} {psA : PreSig n E} {skB s : ZMod n} {sigB : X × ZMod n}
    -- funding output
    (hQ : outputKey C tweak p (some (tree.root leafHash branch)) = some (q, parity))
    (hleaf : (⟨pkA, pkB⟩, path) ∈ tree.paths leafHash branch)
    -- setup: anticipation point and Alice's checked pre-signature
    (hS : anticipate C challenge opk r o = some S)
    (hpre : preVerify C challenge pkA S msg psA = true)
    -- Bob's own signature
    (hpkB : pubkey C skB = some pkB) (hsigB : sign C challenge nonce skB msg = some sigB)
    -- the oracle's attestation
    (hatt : verify C challenge opk o (r, s) = true) :
    spendValid C challenge leafHash branch tweak q parity p ⟨pkA, pkB⟩ path msg
      (adapt C psA s) sigB = true := by
  have hS' : C.mulG s = S := by
    rw [anticipate_of_verify C challenge hatt] at hS
    exact Option.some.inj hS
  simp only [spendValid, Multisig2.satisfied, Bool.and_eq_true]
  exact ⟨verifyScriptPath_of_mem C leafHash branch tweak tree hQ hleaf,
    verify_adapt C challenge hpre hS', verify_sign C challenge nonce hpkB hsigB⟩

end Taproot.DLC
