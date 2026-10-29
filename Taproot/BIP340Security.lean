import Taproot.BIP340Props
import VCVio.CryptoFoundations.FiatShamir.Sigma.Security
import VCVio.ProgramLogic.Tactics.Relational
import VCVio.EvalDist.Monad.Branch

/-!
# BIP340 unforgeability (EUF-CMA) in the random oracle model

BIP340 signing is the Fiat-Shamir transform of a Σ-protocol (an interactive
proof of knowledge of the secret key):

* **commit**: pick a nonce `k` whose point `R = k·G` has an even y, send `r = x(R)`;
* **challenge**: a random `e`;
* **respond**: `s = k + e·d`;
* **verify**: `lift_x(r) = s·G - e·P`, exactly BIP340's verification equation
  (`sigma_verify_eq_verify`).

We prove the three properties VCVio's Fiat-Shamir security theorem needs:

* `sigma_speciallySound`: two accepting transcripts with the same `r` and
  different challenges give the secret key;
* `sigma_hvzk`: transcripts can be simulated without the secret key, with
  exactly the right distribution (perfect honest-verifier zero knowledge);
* `sigma_simCommitPredictability`: a simulated `r` hits any fixed value with
  probability at most `1/|EvenNonce|`, where `EvenNonce` is the set of
  nonzero nonces with an even-y point (`(n - 1)/2` of them).

From these, VCVio's `FiatShamir.euf_cma_bound` (the Pointcheval-Stern
reduction, via its forking lemma) gives `euf_cma`: **any forger against
BIP340 in the random oracle model yields an algorithm that recovers the
secret key of a random public key**, with

`ε' · (ε' / (qH + 1) - 1/n) ≤ Pr[key recovery]`,
`ε' = ε - qS · (qS + qH) · 2/(n - 1)`,

where `ε` is the forger's success probability and `qS`, `qH` bound its
signing and hash queries.

Modelling choices:
* The hash is a random oracle on `(message, r)`. BIP340 also hashes the public
  key into the challenge ("key prefixing"); that matters for security with
  many keys, not for this single-key experiment, where the key is fixed.
* Honest secret keys and nonces are uniform nonzero scalars, normalized as in
  BIP340 (`d = d'` or `n - d'`); real BIP340 derives the nonce from a hash,
  which a random oracle makes uniform. `normalize_uniform` shows the
  normalized value is uniform over the even-y scalars.
* The hard problem is recovering the secret key of a uniformly random
  (even-y) public key: discrete log restricted to even-y points.
-/

open OracleSpec OracleComp
open scoped ENNReal

namespace Taproot.BIP340Security

open Curve

variable {n : ℕ} [Fact n.Prime] {E X : Type} [AddCommGroup E] (C : Curve n E X)

instance : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩

/-- Public keys: the multiples of `G`. -/
abbrev Stmt := Set.range C.mulG

/-- Nonzero scalars whose point has an even y: BIP340's normalized nonces and secret keys. -/
abbrev EvenNonce := {t : ZMod n // C.mulG t ≠ 0 ∧ C.hasEvenY (C.mulG t) = true}

/-- Responses `s` that the simulator can use with challenge `e` under key `P`:
those for which `s·G - e·P` is a nonzero even-y point. -/
abbrev Good (P : E) (e : ZMod n) :=
  {s : ZMod n // C.mulG s - e.val • P ≠ 0 ∧ C.hasEvenY (C.mulG s - e.val • P) = true}

theorem evenScalar_one_mem : C.mulG (C.evenScalar 1) ≠ 0 ∧
    C.hasEvenY (C.mulG (C.evenScalar 1)) = true :=
  ⟨C.mulG_ne_zero (C.evenScalar_ne_zero one_ne_zero), C.hasEvenY_evenScalar one_ne_zero⟩

instance : Nonempty (EvenNonce C) := ⟨⟨C.evenScalar 1, evenScalar_one_mem C⟩⟩

variable [DecidableEq E]

noncomputable instance : SampleableType (EvenNonce C) := SampleableType.subtype _ _

/-- Shifting by `e·k` maps even nonces to good responses for the key `P = k·G`. -/
def shiftEquiv (k e : ZMod n) {P : E} (hk : C.mulG k = P) : EvenNonce C ≃ Good C P e where
  toFun t := ⟨t.1 + e * k, by subst hk; simpa [C.val_smul_mulG, map_add] using t.2⟩
  invFun s := ⟨s.1 - e * k, by subst hk; simpa [C.val_smul_mulG, map_sub] using s.2⟩
  left_inv t := Subtype.ext (add_sub_cancel_right _ _)
  right_inv s := Subtype.ext (sub_add_cancel _ _)

instance (P : Stmt C) (e : ZMod n) : Nonempty (Good C P e) := by
  obtain ⟨k, hk⟩ := P.2
  exact ⟨shiftEquiv C k e hk ⟨C.evenScalar 1, evenScalar_one_mem C⟩⟩

noncomputable instance (P : Stmt C) (e : ZMod n) : SampleableType (Good C P e) :=
  SampleableType.subtype _ _

/-- Exactly half of the `n - 1` nonzero scalars have an even-y point
(negation swaps the two halves). -/
theorem two_mul_card_evenNonce : 2 * Fintype.card (EvenNonce C) = n - 1 := by
  classical
  have hneg (t : ZMod n) (h : C.mulG t ≠ 0) :
      C.hasEvenY (C.mulG (-t)) = !C.hasEvenY (C.mulG t) := by
    rw [map_neg, C.hasEvenY_neg _ h]
  have hodd : Fintype.card (EvenNonce C) = Fintype.card
      {t : ZMod n // C.mulG t ≠ 0 ∧ C.hasEvenY (C.mulG t) = false} :=
    Fintype.card_congr
      { toFun := fun t => ⟨-t.1, by rw [map_neg]; exact neg_ne_zero.mpr t.2.1,
          by rw [hneg _ t.2.1, t.2.2]; rfl⟩
        invFun := fun t => ⟨-t.1, by rw [map_neg]; exact neg_ne_zero.mpr t.2.1,
          by rw [hneg _ t.2.1, t.2.2]; rfl⟩
        left_inv := fun t => Subtype.ext (neg_neg _)
        right_inv := fun t => Subtype.ext (neg_neg _) }
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun t : ZMod n => C.mulG t ≠ 0)
    (p := fun t => C.hasEvenY (C.mulG t) = true)
  simp only [Finset.filter_filter, Bool.not_eq_true] at hsum
  have hev : Fintype.card (EvenNonce C) = (Finset.univ.filter fun t : ZMod n =>
      C.mulG t ≠ 0 ∧ C.hasEvenY (C.mulG t) = true).card := Fintype.card_subtype _
  have hodd' : Fintype.card {t : ZMod n // C.mulG t ≠ 0 ∧ C.hasEvenY (C.mulG t) = false} =
      (Finset.univ.filter fun t : ZMod n =>
        C.mulG t ≠ 0 ∧ C.hasEvenY (C.mulG t) = false).card := Fintype.card_subtype _
  have h0 : (Finset.univ.filter fun t : ZMod n => C.mulG t ≠ 0).card = n - 1 := by
    simp only [ne_eq, C.mulG_eq_zero]
    rw [Finset.filter_ne' Finset.univ (0 : ZMod n), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  omega

/-! ### BIP340's normalization produces uniform even nonces -/

/-- Nonzero scalars: BIP340 secret keys and nonces before normalization. -/
abbrev NonzeroScalar (n : ℕ) := {k : ZMod n // k ≠ 0}

instance : Nonempty (NonzeroScalar n) := ⟨⟨1, one_ne_zero⟩⟩

noncomputable instance : SampleableType (NonzeroScalar n) := SampleableType.subtype _ _

/-- BIP340's normalization `d = d' if has_even_y(d'·G) else n - d'`. -/
def normalize (k : NonzeroScalar n) : EvenNonce C :=
  ⟨C.evenScalar k.1, C.mulG_ne_zero (C.evenScalar_ne_zero k.2), C.hasEvenY_evenScalar k.2⟩

theorem card_nonzeroScalar : Fintype.card (NonzeroScalar n) = n - 1 := by
  classical
  rw [Fintype.card_subtype, Finset.filter_ne' Finset.univ (0 : ZMod n),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

omit [DecidableEq E] in
/-- Each even nonce `t` comes from exactly two scalars, `t` and `-t`. -/
theorem card_normalize_preimage (t : EvenNonce C) :
    (Finset.univ.filter fun k : NonzeroScalar n => normalize C k = t).card = 2 := by
  classical
  have ht0 : t.1 ≠ 0 := fun h => t.2.1 (by rw [h, map_zero])
  have hne : t.1 ≠ -t.1 := by
    intro h
    have := C.hasEvenY_neg _ t.2.1
    rw [← map_neg, ← h, t.2.2] at this
    cases this
  have hiff (k : NonzeroScalar n) : normalize C k = t ↔ k.1 = t.1 ∨ k.1 = -t.1 := by
    simp only [normalize, Subtype.ext_iff, Curve.evenScalar]
    constructor
    · split_ifs
      · exact Or.inl
      · intro h; right; rw [← h, neg_neg]
    · rintro (h | h) <;> rw [h]
      · simp [t.2.2]
      · rw [map_neg, C.hasEvenY_neg _ t.2.1, t.2.2]; simp
  have hfilter : (Finset.univ.filter fun k : NonzeroScalar n => normalize C k = t) =
      {⟨t.1, ht0⟩, ⟨-t.1, neg_ne_zero.mpr ht0⟩} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff, Finset.mem_insert,
      Finset.mem_singleton, Subtype.ext_iff]
  rw [hfilter, Finset.card_pair (fun h => hne (congrArg Subtype.val h))]

theorem two_div_two_mul (c : ℝ≥0∞) : 2 / (2 * c) = c⁻¹ := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
    mul_comm 2⁻¹, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

/-- The β parameter: `1/|EvenNonce| = 2/(n - 1)`. -/
theorem inv_card_evenNonce :
    (Fintype.card (EvenNonce C) : ℝ≥0∞)⁻¹ = 2 / ((n - 1 : ℕ) : ℝ≥0∞) := by
  rw [← two_mul_card_evenNonce C, Nat.cast_mul, Nat.cast_ofNat,
    two_div_two_mul]

/-- **BIP340's normalization of a uniform nonzero scalar is a uniform even
nonce.** So the honest keys and nonces below, made exactly as BIP340 does
(from uniform nonzero `d'` and `k'`), are uniform over `EvenNonce`. -/
theorem normalize_uniform :
    (normalize C <$> ($ᵗ (NonzeroScalar n) : ProbComp _)) =ᵈ ($ᵗ (EvenNonce C) : ProbComp _) := by
  classical
  rw [evalDistEq_iff_forall_prEvent_eq_output]
  intro t
  rw [prEvent_map, SampleableType.prEvent_uniformSample, card_normalize_preimage,
    SampleableType.prEvent_uniformSample_eq_singleton, card_nonzeroScalar, inv_card_evenNonce]
  rfl

noncomputable instance : Fintype (Stmt C) := Fintype.ofFinite _

instance : Nonempty (Stmt C) := ⟨⟨C.mulG 0, 0, rfl⟩⟩

noncomputable instance : SampleableType (Stmt C) := SampleableType.ofFintype _

variable [DecidableEq X]

/-- The simulator: pick the challenge `e` and a response `s` first, then solve
the verification equation for the nonce point `R = s·G - e·P`. -/
noncomputable def simTranscript (P : Stmt C) : ProbComp ((X × X) × ZMod n × ZMod n) := do
  let e ← $ᵗ (ZMod n)
  let s ← $ᵗ (Good C P e)
  return ((C.x (C.mulG s.1 - e.val • P.1), C.x P.1), e, s.1)

/-- The BIP340 Σ-protocol: statement `P`, witness `d` with `d·G = P`. The
prover picks a uniform nonzero nonce `k'`, commits to `(r, p)` with
`r = x(k'·G)` and `p = x(P)` the public key, and answers the challenge `e`
with `s = k + e·d`, where `k` is `k'` normalized so that `k·G` has an even y
(as in BIP340 `Sign`). Putting `p` into the commitment makes the Fiat-Shamir
hash input `(m, (r, p))`: exactly BIP340's challenge inputs `r ‖ p ‖ m`. -/
noncomputable def sigma :
    SigmaProtocol (Stmt C) (ZMod n) (X × X) (ZMod n) (ZMod n) (ZMod n)
      (fun P w => decide (C.mulG w = P.1)) where
  commit P _ := do
    let k ← $ᵗ (NonzeroScalar n)
    return ((C.x (C.mulG k.1), C.x P.1), C.evenScalar k.1)
  respond _ w k e := pure (k + e * w)
  verify P c e s :=
    decide (c.2 = C.x P.1) && decide (C.liftX c.1 = some (C.mulG s - e.val • P.1))
  sim P := Prod.fst <$> simTranscript C P
  extract e₁ s₁ e₂ s₂ := pure ((s₁ - s₂) / (e₁ - e₂))

/-- BIP340 key generation: a uniform nonzero secret key `d'`, normalized to `d`
so that the public key `P = d·G` has an even y. -/
noncomputable def keyGen :
    GenerableRelation (Stmt C) (ZMod n) (fun P w => decide (C.mulG w = P.1)) where
  gen := do
    let k ← $ᵗ (NonzeroScalar n)
    return (⟨C.mulG (C.evenScalar k.1), C.evenScalar k.1, rfl⟩, C.evenScalar k.1)
  gen_sound P w h := by
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    obtain ⟨k, -, rfl, rfl⟩ := h
    simp

/-- The Σ-protocol's check is BIP340's `Verify` with challenge `e`, for even-y
keys, when the commitment carries the right public key `x(P)`. So a signature
`((r, x(P)), s)` of this scheme is valid iff the BIP340 signature `(r, s)` is,
with challenge `e = H(m, (r, x(P)))`: the two signature formats differ only
by the (checked) public key. -/
theorem sigma_verify_eq_verify {M : Type} {P : E} (hP0 : P ≠ 0)
    (hPe : C.hasEvenY P = true) (hP : P ∈ Set.range C.mulG) (r : X) (e s : ZMod n) (m : M) :
    (sigma C).verify ⟨P, hP⟩ (r, C.x P) e s =
      BIP340.verify C (fun _ _ _ => e) (C.x P) m (r, s) := by
  have hlift := C.liftX_x P hP0 hPe
  rw [Bool.eq_iff_iff, BIP340.verify_eq_true_iff]
  simp only [sigma, decide_eq_true_eq, hlift, Option.some.injEq, exists_eq_left',
    Bool.and_eq_true, true_and]

/-- A commitment carrying any other public key is rejected. -/
theorem sigma_verify_wrong_key {P : Stmt C} {r p : X} (hp : p ≠ C.x P.1) (e s : ZMod n) :
    (sigma C).verify P (r, p) e s = false := by
  simp [sigma, hp]

/-- **Special soundness**: two accepting transcripts with the same commitment
and different challenges reveal a secret key. -/
theorem sigma_speciallySound : (sigma C).SpeciallySound := by
  rintro ⟨P, k, rfl⟩ ⟨r, p⟩ e₁ e₂ s₁ s₂ hne h₁ h₂ w hw
  simp only [sigma, support_pure, Set.mem_singleton_iff, decide_eq_true_eq,
    Bool.and_eq_true] at h₁ h₂ hw ⊢
  subst hw
  replace h₁ := h₁.2
  replace h₂ := h₂.2
  rw [h₁, Option.some.injEq, C.val_smul_mulG, C.val_smul_mulG, ← map_sub, ← map_sub] at h₂
  have h := C.mulG_injective h₂
  have hk : (s₁ - s₂) / (e₁ - e₂) = k := by
    rw [div_eq_iff (sub_ne_zero.mpr hne)]
    linear_combination h
  rw [hk]

/-- **Perfect honest-verifier zero knowledge**: the simulator's transcripts
have exactly the distribution of real ones. Real transcripts are
`(x(t·G), e, t + e·d)` for a uniform even nonce `t`; shifting `t` by `e·d` is a
bijection onto the simulator's good responses. -/
theorem sigma_hvzk : (sigma C).PerfectHVZK (simTranscript C) := by
  rintro ⟨P, hP⟩ w hw
  have hw' : C.mulG w = P := of_decide_eq_true hw
  let g (e : ZMod n) (s : Good C P e) : (X × X) × ZMod n × ZMod n :=
    ((C.x (C.mulG s.1 - e.val • P), C.x P), e, s.1)
  -- First, the normalized nonce is a uniform even nonce.
  have hnorm : (sigma C).realTranscript ⟨P, hP⟩ w =ᵈ (do
      let t ← $ᵗ (EvenNonce C)
      let e ← $ᵗ (ZMod n)
      pure (((C.x (C.mulG t.1), C.x P), e, t.1 + e * w) : (X × X) × ZMod n × ZMod n)) := by
    have h : (sigma C).realTranscript ⟨P, hP⟩ w =
        (normalize C <$> ($ᵗ (NonzeroScalar n) : ProbComp _)) >>=
        fun t => (do
          let e ← $ᵗ (ZMod n)
          pure (((C.x (C.mulG t.1), C.x P), e, t.1 + e * w) :
            (X × X) × ZMod n × ZMod n)) := by
      simp [ChallengeVerifyProtocol.realTranscript, sigma, normalize, C.x_evenScalar]
    rw [h]
    exact EvalDistEq.bind_left (normalize_uniform C) _
  have hswap : (sigma C).realTranscript ⟨P, hP⟩ w =ᵈ (do
      let e ← $ᵗ (ZMod n)
      let t ← $ᵗ (EvenNonce C)
      pure (g e (shiftEquiv C w e hw' t))) := by
    refine hnorm.trans ?_
    let : MeasurableSpace ((X × X) × ZMod n × ZMod n) := ⊤
    refine EvalDistEq.of_evalDist_eq ?_
    rw [OracleComp.evalDist_bind_bind_swap]
    subst hw'
    simp [g, shiftEquiv, C.val_smul_mulG, map_add]
  refine hswap.trans (EvalDistEq.bind_right _ fun e => ?_)
  simp only [bind_pure_comp]
  rw [← Functor.map_map]
  let : SampleableType (Good C P e) :=
    inferInstanceAs (SampleableType (Good C (↑(⟨P, hP⟩ : Stmt C)) e))
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (shiftEquiv C w e hw').bijective).map (g e)

/-- **Commitment unpredictability**: a simulated commitment equals any given
value with probability at most `1/|EvenNonce|`. -/
theorem sigma_simCommitPredictability :
    (sigma C).simCommitPredictability (simTranscript C)
      ((Fintype.card (EvenNonce C) : ℝ≥0∞)⁻¹) := by
  classical
  intro P c₀
  obtain ⟨k, hk⟩ := P.2
  refine prEvent_bind_le_of_forall_le ($ᵗ (ZMod n)) _
    (fun t : (X × X) × ZMod n × ZMod n => t.1 = c₀) fun e => ?_
  simp only [prEvent_norm]
  rw [SampleableType.prEvent_uniformSample, Fintype.card_congr (shiftEquiv C k e hk).symm]
  -- At most one good response gives the commitment `c₀`.
  have hle : (Finset.univ.filter fun s : Good C P e =>
      (C.x (C.mulG s.1 - e.val • P.1), C.x P.1) = c₀).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have := C.eq_of_x_eq a.2.1 b.2.1 (congrArg Prod.fst (ha.trans hb.symm))
      (a.2.2.trans b.2.2.symm)
    exact Subtype.ext (C.mulG_injective (sub_left_injective this))
  calc ((Finset.univ.filter _).card : ℝ≥0∞) / (Fintype.card (EvenNonce C) : ℝ≥0∞)
      ≤ 1 / (Fintype.card (EvenNonce C) : ℝ≥0∞) := by
        gcongr; exact_mod_cast hle
    _ = _ := one_div _

/-- **BIP340 is unforgeable under chosen-message attacks (EUF-CMA)** in the
random oracle model, assuming it is hard to recover the secret key of a
random public key. Concretely, from any forger making at most `qS` signing
and `qH` hash queries and succeeding with probability `ε`, the reduction
`FiatShamir.cmaReduction` recovers the secret key with probability at least
`ε' · (ε' / (qH + 1) - 1/n)`, where `ε' = ε - qS·(qS + qH)·2/(n - 1)`. -/
theorem euf_cma (M : Type) [DecidableEq M]
    (adv : SignatureAlg.UnforgeableAdversary (FiatShamir.inROM (sigma C) (keyGen C) M))
    (qS qH : ℕ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (Commit := X × X) (Chal := ZMod n)
      (S' := (X × X) × ZMod n) (oa := adv.main pk) qS qH) :
    let eps := SignatureAlg.unforgeableAdvantage
        (FiatShamir.runtime (Commit := X × X) (Chal := ZMod n) M) adv -
      (qS : ℝ≥0∞) * (qS + qH) * (2 / ((n - 1 : ℕ) : ℝ≥0∞))
    eps * (eps / (qH + 1 : ℝ≥0∞) - FiatShamir.challengeSpaceInv (ZMod n)) ≤
      Pr{let x ← (hardRelationExperiment (keyGen C)
        (FiatShamir.cmaReduction (sigma C) (keyGen C) M (simTranscript C) adv qH))}[x = true] := by
  have h := FiatShamir.euf_cma_bound (sigma C) (keyGen C) M (sigma_speciallySound C)
    (simTranscript C) (ζ_zk := 0)
    ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp (sigma_hvzk C))
    (β := (Fintype.card (EvenNonce C) : ℝ≥0∞)⁻¹) (sigma_simCommitPredictability C)
    adv qS qH hQ
  simp only [mul_zero, zero_add, inv_card_evenNonce] at h ⊢
  exact h

/-! ## From key recovery to discrete log -/

/-- The discrete-log experiment: given `k·G` for a uniform nonzero `k`, find `k`. -/
noncomputable def dlogExperiment (B : Stmt C → ProbComp (ZMod n)) : ProbComp Bool := do
  let k ← $ᵗ (NonzeroScalar n)
  let x ← B ⟨C.mulG k.1, k.1, rfl⟩
  return decide (x = k.1)

/-- `-P`, which is again a multiple of `G`. -/
def negStmt (P : Stmt C) : Stmt C :=
  ⟨-P.1, by obtain ⟨k, hk⟩ := P.2; exact ⟨-k, by rw [map_neg, hk]⟩⟩

/-- Solve discrete log with a key-recovery algorithm `A`: if `Y` has an odd y,
recover the key of `-Y` and negate it. -/
noncomputable def dlogOfKeyRecovery (A : Stmt C → ProbComp (ZMod n)) (Y : Stmt C) :
    ProbComp (ZMod n) :=
  if C.hasEvenY Y.1 then A Y else (fun d => -d) <$> A (negStmt C Y)

/-- **Key recovery is exactly as hard as discrete log**: `dlogOfKeyRecovery A`
solves discrete log with exactly the probability that `A` recovers the key of
a BIP340 public key. -/
theorem hardRelationExperiment_eq_dlog (A : Stmt C → ProbComp (ZMod n)) :
    hardRelationExperiment (keyGen C) A = dlogExperiment C (dlogOfKeyRecovery C A) := by
  simp only [hardRelationExperiment, keyGen, dlogExperiment, bind_assoc, pure_bind]
  congr 1
  funext k
  unfold dlogOfKeyRecovery
  by_cases h : C.hasEvenY (C.mulG k.1) = true
  · have hk : C.evenScalar k.1 = k.1 := by simp [Curve.evenScalar, h]
    have hs : (⟨C.mulG (C.evenScalar k.1), C.evenScalar k.1, rfl⟩ : Stmt C) =
        ⟨C.mulG k.1, k.1, rfl⟩ := Subtype.ext (by rw [hk])
    simp only [h, if_true, hs]
    congr 1
    funext w
    simp [hk, C.mulG_injective.eq_iff]
  · have hk : C.evenScalar k.1 = -k.1 := by simp [Curve.evenScalar, h]
    have hs : (⟨C.mulG (C.evenScalar k.1), C.evenScalar k.1, rfl⟩ : Stmt C) =
        negStmt C ⟨C.mulG k.1, k.1, rfl⟩ := Subtype.ext (by simp [negStmt, hk])
    simp only [h, Bool.false_eq_true, if_false, hs, bind_map_left]
    congr 1
    funext w
    simp only [hk, C.mulG_injective.eq_iff, neg_eq_iff_eq_neg]

/-- **BIP340 is EUF-CMA secure under the discrete-log assumption**, in the
random oracle model: the Pointcheval-Stern bound of `euf_cma`, with the
key-recovery algorithm turned into a discrete-log solver. -/
theorem euf_cma_dlog (M : Type) [DecidableEq M]
    (adv : SignatureAlg.UnforgeableAdversary (FiatShamir.inROM (sigma C) (keyGen C) M))
    (qS qH : ℕ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (Commit := X × X) (Chal := ZMod n)
      (S' := (X × X) × ZMod n) (oa := adv.main pk) qS qH) :
    let eps := SignatureAlg.unforgeableAdvantage
        (FiatShamir.runtime (Commit := X × X) (Chal := ZMod n) M) adv -
      (qS : ℝ≥0∞) * (qS + qH) * (2 / ((n - 1 : ℕ) : ℝ≥0∞))
    eps * (eps / (qH + 1 : ℝ≥0∞) - FiatShamir.challengeSpaceInv (ZMod n)) ≤
      Pr{let x ← (dlogExperiment C (dlogOfKeyRecovery C
        (FiatShamir.cmaReduction (sigma C) (keyGen C) M (simTranscript C) adv qH)))}[x = true] := by
  rw [← hardRelationExperiment_eq_dlog]
  exact euf_cma C M adv qS qH hQ

end Taproot.BIP340Security
