import Taproot.BIP340

/-!
# BIP340: properties beyond correctness

* `verify_eq_true_iff`: what `Verify` accepts, as one equation between points.
* `verify_unique`: **non-malleability**: for a public key, message and `r`,
  at most one `s` is valid. Nobody can turn a valid signature into a different
  valid signature with the same nonce.
* `extract_secret`: **special soundness**, the extractor behind Schnorr's
  security proof. Two valid signatures with the same `r` on different
  challenges reveal the secret key. This holds for *any* signatures, not only
  honestly made ones: whoever can answer two challenges for one nonce knows
  the key.
* `sign_nonce_reuse`: hence a signer whose nonce repeats across two messages
  leaks its key.
* `batchVerify`: BIP340's batch verification. `batchVerify_of_verify`: a
  batch of valid signatures passes for every choice of the random
  coefficients. `batchVerify_sound`: if some signature is invalid, then for any
  fixed values of the other coefficients at most one value of its coefficient
  makes the batch pass, so a random coefficient catches it except with
  probability `1/n`. `batchVerify_sound_single` covers the coefficient fixed
  to `1`.

Batch verification needs every point to satisfy `n·P = 0`
(`Curve.PrimeOrder`, true for secp256k1 but not proven here).
-/

namespace Taproot.BIP340

open Curve

variable {n : ℕ} [Fact n.Prime] {E X M : Type*} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- `Verify` accepts `(r, s)` exactly when `lift_x(r)` is the point `s·G - e·P`. -/
theorem verify_eq_true_iff {pk : X} {m : M} {r : X} {s : ZMod n} :
    verify C challenge pk m (r, s) = true ↔
      ∃ P, C.liftX pk = some P ∧
        C.liftX r = some (C.mulG s - (challenge r pk m).val • P) := by
  unfold verify
  split
  · simp_all
  · rename_i P hP
    simp only [hP, Option.some.injEq, exists_eq_left', Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h0, he⟩, hx⟩
      have := C.liftX_x _ h0 he
      rwa [hx] at this
    · intro h
      obtain ⟨h0, he, hx⟩ := C.liftX_spec _ _ h
      exact ⟨⟨h0, he⟩, hx⟩

/-- **Non-malleability**: a public key, message and nonce `r` determine `s`. -/
theorem verify_unique {pk : X} {m : M} {r : X} {s s' : ZMod n}
    (h : verify C challenge pk m (r, s) = true) (h' : verify C challenge pk m (r, s') = true) :
    s = s' := by
  obtain ⟨P, hP, hR⟩ := (verify_eq_true_iff C challenge).mp h
  obtain ⟨P', hP', hR'⟩ := (verify_eq_true_iff C challenge).mp h'
  rw [hP, Option.some.injEq] at hP'
  subst hP'
  rw [hR, Option.some.injEq, sub_left_inj] at hR'
  exact C.mulG_injective hR'

/-- Two valid signatures with the same `r`: `e₁·P - e₂·P = (s₁ - s₂)·G`. -/
theorem verify_same_r {pk : X} {P : E} {m₁ m₂ : M} {r : X} {s₁ s₂ : ZMod n}
    (hP : C.liftX pk = some P)
    (h₁ : verify C challenge pk m₁ (r, s₁) = true) (h₂ : verify C challenge pk m₂ (r, s₂) = true) :
    (challenge r pk m₁).val • P - (challenge r pk m₂).val • P = C.mulG (s₁ - s₂) := by
  obtain ⟨P₁, hP₁, hR₁⟩ := (verify_eq_true_iff C challenge).mp h₁
  obtain ⟨P₂, hP₂, hR₂⟩ := (verify_eq_true_iff C challenge).mp h₂
  rw [hP, Option.some.injEq] at hP₁ hP₂
  subst hP₁ hP₂
  rw [hR₁, Option.some.injEq] at hR₂
  have := congrArg Neg.neg hR₂
  simp only [neg_sub] at this
  rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
  exact this

/-- **Special soundness (key extraction)**: from any two valid signatures
under the public key of `sk` that share `r` but have different challenges,
`(s₁ - s₂)/(e₁ - e₂)` is the (normalized) secret key, and in particular a
secret key for `pk`. -/
theorem extract_secret {sk : ZMod n} {pk : X} {m₁ m₂ : M} {r : X} {s₁ s₂ : ZMod n}
    (hpk : pubkey C sk = some pk)
    (h₁ : verify C challenge pk m₁ (r, s₁) = true) (h₂ : verify C challenge pk m₂ (r, s₂) = true)
    (he : challenge r pk m₁ ≠ challenge r pk m₂) :
    (s₁ - s₂) / (challenge r pk m₁ - challenge r pk m₂) = C.evenScalar sk ∧
      pubkey C ((s₁ - s₂) / (challenge r pk m₁ - challenge r pk m₂)) = some pk := by
  unfold pubkey at hpk
  split_ifs at hpk with hsk
  cases hpk
  have key := verify_same_r C challenge (C.liftX_x_mulG hsk) h₁ h₂
  rw [C.val_smul_mulG, C.val_smul_mulG, ← map_sub] at key
  have hd := C.mulG_injective key
  have hext : (s₁ - s₂) / (challenge r (C.x (C.mulG sk)) m₁ - challenge r (C.x (C.mulG sk)) m₂) =
      C.evenScalar sk := by
    rw [← hd, ← sub_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr he)]
  refine ⟨hext, ?_⟩
  rw [hext]
  simp [pubkey, C.evenScalar_ne_zero hsk, C.x_evenScalar]

omit [DecidableEq E] [DecidableEq X] in
/-- **Nonce reuse leaks the key**: if the signer's nonce function returns the
same nonce for two messages with different challenges, the two signatures
reveal the secret key. -/
theorem sign_nonce_reuse (nonce : ZMod n → X → M → ZMod n) {sk : ZMod n} {pk : X}
    {m₁ m₂ : M} {r₁ r₂ : X} {s₁ s₂ : ZMod n}
    (hpk : pubkey C sk = some pk)
    (h₁ : sign C challenge nonce sk m₁ = some (r₁, s₁))
    (h₂ : sign C challenge nonce sk m₂ = some (r₂, s₂))
    (hk : nonce (C.evenScalar sk) pk m₁ = nonce (C.evenScalar sk) pk m₂)
    (he : challenge r₁ pk m₁ ≠ challenge r₁ pk m₂) :
    pubkey C ((s₁ - s₂) / (challenge r₁ pk m₁ - challenge r₁ pk m₂)) = some pk := by
  classical
  have hr : r₁ = r₂ := by
    have hpk' := hpk
    unfold pubkey at hpk'
    unfold sign at h₁ h₂
    dsimp only at h₁ h₂
    split_ifs at hpk' h₁ h₂
    cases hpk'
    rw [hk] at h₁
    rw [← (Prod.mk.inj (Option.some.inj h₁)).1, ← (Prod.mk.inj (Option.some.inj h₂)).1]
  subst hr
  exact (extract_secret C challenge hpk (verify_sign C challenge nonce hpk h₁)
    (verify_sign C challenge nonce hpk h₂) he).2

/-! ## Batch verification -/

/-- One entry of a batch: public key, message and signature `(r, s)`. -/
structure Entry (n : ℕ) (X M : Type*) where
  pk : X
  m : M
  r : X
  s : ZMod n

namespace Entry

/-- `lift_x(pk)`, or `0` if it fails (the batch then fails anyway). -/
def P (e : Entry n X M) : E := (C.liftX e.pk).getD 0

/-- `lift_x(r)`, or `0` if it fails. -/
def R (e : Entry n X M) : E := (C.liftX e.r).getD 0

/-- The challenge `e = int(hash(r ‖ pk ‖ m)) mod n`. -/
def e (e : Entry n X M) : ZMod n := challenge e.r e.pk e.m

/-- Whether the entry verifies, as a single signature. -/
def valid (e : Entry n X M) : Bool := verify C challenge e.pk e.m (e.r, e.s)

/-- The amount by which the entry fails its equation: `s·G - R - e·P`. -/
def defect (ent : Entry n X M) : E := C.mulG ent.s - R C ent - (e challenge ent).val • P C ent

end Entry

open Entry

/-- BIP340 batch verification of `u` signatures with coefficients `a`
(BIP340 takes `a₁ = 1` and the others random): fail if some `lift_x` fails,
otherwise check
`(a₁s₁ + … + aᵤsᵤ)·G = a₁·R₁ + (a₁e₁)·P₁ + … + aᵤ·Rᵤ + (aᵤeᵤ)·Pᵤ`. -/
def batchVerify {u : ℕ} (ent : Fin u → Entry n X M) (a : Fin u → ZMod n) : Bool :=
  decide (∀ i, (C.liftX (ent i).pk).isSome ∧ (C.liftX (ent i).r).isSome) &&
  decide (C.mulG (∑ i, a i * (ent i).s) =
    ∑ i, ((a i).val • R C (ent i) + (a i * e challenge (ent i)).val • P C (ent i)))

/-- An entry verifies iff both lifts succeed and its defect is zero. -/
theorem valid_iff (ent : Entry n X M) :
    valid C challenge ent = true ↔
      (C.liftX ent.pk).isSome ∧ (C.liftX ent.r).isSome ∧ defect C challenge ent = 0 := by
  unfold valid defect R P e
  rw [verify_eq_true_iff]
  constructor
  · rintro ⟨P, hP, hR⟩
    simp [hP, hR]
  · rintro ⟨hP, hR, h0⟩
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hP
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp hR
    rw [hP, hR, Option.getD_some, Option.getD_some] at h0
    refine ⟨P, hP, ?_⟩
    rw [sub_sub, sub_eq_zero] at h0
    rw [hR, Option.some.injEq, h0, add_sub_cancel_right]

omit [DecidableEq X] in
/-- Under `PrimeOrder`, the batch equation says `Σ aᵢ·defectᵢ = 0`. -/
theorem batchVerify_iff (hord : PrimeOrder n E) {u : ℕ} (ent : Fin u → Entry n X M)
    (a : Fin u → ZMod n) :
    batchVerify C challenge ent a = true ↔
      (∀ i, (C.liftX (ent i).pk).isSome ∧ (C.liftX (ent i).r).isSome) ∧
        ∑ i, (a i).val • defect C challenge (ent i) = 0 := by
  unfold batchVerify
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  apply and_congr_right
  intro _
  have hterm (i : Fin u) : (a i).val • defect C challenge (ent i) =
      C.mulG (a i * (ent i).s) -
        ((a i).val • R C (ent i) + (a i * e challenge (ent i)).val • P C (ent i)) := by
    rw [defect, val_mul_smul (hord _), ← C.val_smul_mulG]
    simp only [smul_sub]
    abel
  simp only [hterm, Finset.sum_sub_distrib, map_sum, sub_eq_zero]

/-- **Batch verification is correct**: if every signature verifies, the batch
passes for every choice of coefficients. -/
theorem batchVerify_of_valid (hord : PrimeOrder n E) {u : ℕ} (ent : Fin u → Entry n X M)
    (hv : ∀ i, valid C challenge (ent i) = true) (a : Fin u → ZMod n) :
    batchVerify C challenge ent a = true := by
  rw [batchVerify_iff C challenge hord]
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := (valid_iff C challenge _).mp (hv i)
    exact ⟨h1, h2⟩
  · apply Finset.sum_eq_zero
    intro i _
    rw [((valid_iff C challenge _).mp (hv i)).2.2, nsmul_zero]

/-- **Batch verification is sound**: if signature `j` is invalid, then once
the other coefficients are fixed, at most one value of `aⱼ` lets the batch
pass. With `aⱼ` uniformly random, an invalid batch is accepted with
probability at most `1/n`. -/
theorem batchVerify_sound (hord : PrimeOrder n E) {u : ℕ} (ent : Fin u → Entry n X M)
    {j : Fin u} (hj : valid C challenge (ent j) = false) {a a' : Fin u → ZMod n}
    (hoff : ∀ i, i ≠ j → a i = a' i)
    (h : batchVerify C challenge ent a = true) (h' : batchVerify C challenge ent a' = true) :
    a j = a' j := by
  rw [batchVerify_iff C challenge hord] at h h'
  obtain ⟨hlift, hsum⟩ := h
  obtain ⟨-, hsum'⟩ := h'
  by_contra hne
  have hdiff : (a j - a' j).val • defect C challenge (ent j) = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsum hsum'
    have hrest : ∑ i ∈ Finset.univ.erase j, (a i).val • defect C challenge (ent i) =
        ∑ i ∈ Finset.univ.erase j, (a' i).val • defect C challenge (ent i) :=
      Finset.sum_congr rfl fun i hi => by rw [hoff i (Finset.ne_of_mem_erase hi)]
    rw [hrest] at hsum
    rw [val_sub_smul (hord _)]
    exact sub_eq_zero.mpr (add_right_cancel (hsum.trans hsum'.symm))
  have h0 := eq_zero_of_val_smul (hord _) (sub_ne_zero.mpr hne) hdiff
  have := (valid_iff C challenge (ent j)).mpr ⟨(hlift j).1, (hlift j).2, h0⟩
  rw [hj] at this
  cases this

/-- **A single invalid signature is always caught** when its coefficient is
nonzero (e.g. BIP340's fixed `a₁ = 1`). -/
theorem batchVerify_sound_single (hord : PrimeOrder n E) {u : ℕ} (ent : Fin u → Entry n X M)
    {j : Fin u} (hj : valid C challenge (ent j) = false)
    (hothers : ∀ i, i ≠ j → valid C challenge (ent i) = true) {a : Fin u → ZMod n}
    (ha : a j ≠ 0) : batchVerify C challenge ent a = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  have h0 : ∀ i, i ≠ j → defect C challenge (ent i) = 0 := fun i hi =>
    ((valid_iff C challenge _).mp (hothers i hi)).2.2
  rw [batchVerify_iff C challenge hord] at h
  obtain ⟨hlift, hsum⟩ := h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    Finset.sum_eq_zero (fun i hi => by rw [h0 i (Finset.ne_of_mem_erase hi), nsmul_zero]),
    add_zero] at hsum
  have := (valid_iff C challenge (ent j)).mpr
    ⟨(hlift j).1, (hlift j).2, eq_zero_of_val_smul (hord _) ha hsum⟩
  rw [hj] at this
  cases this

end Taproot.BIP340
