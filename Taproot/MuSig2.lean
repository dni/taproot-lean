import Taproot.DLC

/-!
# BIP327: MuSig2, and DLCs funded through the Taproot key path

MuSig2 lets several signers produce one BIP340 signature for an aggregate
key. We model BIP327's `KeyAgg`, `ApplyTweak` (with its `gacc`/`tacc`
bookkeeping), `GetSessionValues`, `Sign`, `PartialSigVerifyInternal` and
`PartialSigAgg`, generalized with an *adaptor point* `T` added to the
aggregate nonce (`T = 0` is exactly BIP327). We prove:

* `keyAgg_tweaks_invariant`: after key aggregation and any tweaks,
  `Q = (gacc·Σ aᵢ·skᵢ + tacc)·G` (BIP327's tweaking invariant).
* `partialSigVerify_sign`: honest partial signatures pass partial verification.
* `verify_aggregate`: **if every partial signature passes
  `PartialSigVerifyInternal`, the aggregate is a valid BIP340 signature
  under the (tweaked) aggregate key**, whoever produced them.
  With an adaptor point it is an adaptor pre-signature that completes to a
  valid signature.
* `outputKey_eq_applyTweak`: tweaking the aggregate key with the Taproot tweak
  gives exactly the BIP341 output key, so MuSig2 signs Taproot key-path spends.
* `settleKeyPath`: a DLC whose funding output's internal key is the MuSig2
  aggregate of Alice and Bob settles through the **key path** once the oracle
  attests, and the broadcast signature reveals the attestation.

As before, hashes are arbitrary functions and byte encodings are left out.
Public keys of signers are assumed to be multiples of `G` (on secp256k1 every
point is); public nonces can be arbitrary points.
-/

namespace Taproot.MuSig2

open Curve BIP340 BIP341 DLC

variable {n : ℕ} [Fact n.Prime] {E X M : Type*} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  (C : Curve n E X)

/-! ## Key aggregation and tweaking -/

/-- BIP327 KeyAgg context `(Q, gacc, tacc)`. -/
structure KeyAggCtx (n : ℕ) (E : Type*) where
  Q : E
  gacc : ZMod n
  tacc : ZMod n

variable (aggCoef : List E → E → ZMod n)

/-- `KeyAgg(pk₁..ᵤ)`: `Q = Σ aᵢ·Pᵢ` with `aᵢ = KeyAggCoeff(pk₁..ᵤ, Pᵢ)`. -/
def keyAgg (pks : List E) : Option (KeyAggCtx n E) :=
  let Q := (pks.map fun P => (aggCoef pks P).val • P).sum
  if Q = 0 then none else some ⟨Q, 1, 0⟩

/-- `ApplyTweak(ctx, t, is_xonly_t)`. -/
def applyTweak (ctx : KeyAggCtx n E) (t : ZMod n) (xonly : Bool) : Option (KeyAggCtx n E) :=
  let neg := xonly && !C.hasEvenY ctx.Q
  let g : ZMod n := if neg then -1 else 1
  let Q' := (if neg then -ctx.Q else ctx.Q) + C.mulG t
  if Q' = 0 then none else some ⟨Q', g * ctx.gacc, t + g * ctx.tacc⟩

/-- Apply a list of tweaks in order. -/
def applyTweaks (ctx : KeyAggCtx n E) : List (ZMod n × Bool) → Option (KeyAggCtx n E)
  | [] => some ctx
  | (t, xonly) :: ts => (applyTweak C ctx t xonly).bind (applyTweaks · ts)

/-- `g = 1` if `Q` has even y, else `-1`. -/
def gOf (ctx : KeyAggCtx n E) : ZMod n := if C.hasEvenY ctx.Q then 1 else -1

/-- The aggregate secret `Σ aᵢ·skᵢ` for signers with keys `skᵢ`. -/
def aggSecret (sks : List (ZMod n)) : ZMod n :=
  (sks.map fun sk => aggCoef (sks.map C.mulG) (C.mulG sk) * sk).sum

omit [DecidableEq X] in
/-- **BIP327's tweak invariant**: after `KeyAgg` and any tweaks,
`Q = (gacc · Σ aᵢ·skᵢ + tacc)·G`, and `Q ≠ 0`. -/
theorem keyAgg_tweaks_invariant (sks : List (ZMod n)) (tweaks : List (ZMod n × Bool))
    {ctx₀ ctx : KeyAggCtx n E} (h₀ : keyAgg aggCoef (sks.map C.mulG) = some ctx₀)
    (h : applyTweaks C ctx₀ tweaks = some ctx) :
    ctx.Q = C.mulG (ctx.gacc * aggSecret C aggCoef sks + ctx.tacc) ∧ ctx.Q ≠ 0 := by
  have base : ctx₀.Q = C.mulG (ctx₀.gacc * aggSecret C aggCoef sks + ctx₀.tacc) ∧ ctx₀.Q ≠ 0 := by
    unfold keyAgg at h₀
    dsimp only at h₀
    split_ifs at h₀ with hQ
    cases h₀
    refine ⟨?_, hQ⟩
    simp only [one_mul, add_zero, aggSecret, map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro sk _
    simp [C.val_smul_mulG]
  clear h₀
  induction tweaks generalizing ctx₀ with
  | nil => cases h; exact base
  | cons tw ts ih =>
    obtain ⟨t, xonly⟩ := tw
    simp only [applyTweaks, Option.bind_eq_some_iff] at h
    obtain ⟨ctx₁, h₁, h⟩ := h
    refine ih h ?_
    obtain ⟨hb, hb0⟩ := base
    unfold applyTweak at h₁
    dsimp only at h₁
    split_ifs at h₁ <;> cases h₁ <;> refine ⟨?_, by assumption⟩
    · rw [hb, ← map_neg, ← map_add]; ring_nf
    · rw [hb, ← map_add]; ring_nf

/-! ## Signing sessions -/

/-- A signer's public data: public key and the two public nonces. -/
structure PubSigner (E : Type*) where
  P : E
  R₁ : E
  R₂ : E

/-- A signer's secret data: secret key and the two secret nonces. -/
structure SecSigner (n : ℕ) where
  sk : ZMod n
  k₁ : ZMod n
  k₂ : ZMod n

/-- The public data of an honest signer. -/
def SecSigner.pub (s : SecSigner n) : PubSigner E := ⟨C.mulG s.sk, C.mulG s.k₁, C.mulG s.k₂⟩

/-- Session values `(b, R, e)` (`GetSessionValues`), with the aggregate nonce
shifted by an adaptor point `T` (`T = 0` for plain MuSig2). -/
structure Session (n : ℕ) (E : Type*) where
  b : ZMod n
  R : E
  e : ZMod n

variable (nonceCoef : E → E → X → M → ZMod n) (challenge : X → X → M → ZMod n)

/-- `R' = R₁ + b·R₂ + T` before the infinity check. -/
def aggNonce (signers : List (PubSigner E)) (b : ZMod n) (T : E) : E :=
  (signers.map (·.R₁)).sum + b.val • (signers.map (·.R₂)).sum + T

/-- `GetSessionValues`: `b = H_non(aggnonce, x(Q), m)`, `R = R₁ + b·R₂ (+ T)`
(or `G` if that is infinity), `e = H_sig(x(R), x(Q), m)`. -/
def session (ctx : KeyAggCtx n E) (signers : List (PubSigner E)) (T : E) (m : M) :
    Session n E :=
  let b := nonceCoef (signers.map (·.R₁)).sum (signers.map (·.R₂)).sum (C.x ctx.Q) m
  let R' := aggNonce signers b T
  let R := if R' = 0 then C.G else R'
  ⟨b, R, challenge (C.x R) (C.x ctx.Q) m⟩

/-- `Sign`: `s = k₁ + b·k₂ + e·a·d` with nonces negated if `R` has odd y and
`d = g·gacc·sk`. -/
def partialSign (ctx : KeyAggCtx n E) (pks : List E) (sess : Session n E) (sec : SecSigner n) :
    ZMod n :=
  let k := sec.k₁ + sess.b * sec.k₂
  (if C.hasEvenY sess.R then k else -k) +
    sess.e * aggCoef pks (C.mulG sec.sk) * (gOf C ctx * ctx.gacc * sec.sk)

/-- `PartialSigVerifyInternal`: `s·G = Re + e·a·g'·P`, where `Re = ±(R₁ + b·R₂)`
for this signer's nonces and `g' = g·gacc`. -/
def partialSigVerify (ctx : KeyAggCtx n E) (pks : List E) (sess : Session n E)
    (pub : PubSigner E) (s : ZMod n) : Bool :=
  let Re := pub.R₁ + sess.b.val • pub.R₂
  decide (C.mulG s = (if C.hasEvenY sess.R then Re else -Re) +
    (sess.e * aggCoef pks pub.P * (gOf C ctx * ctx.gacc)).val • pub.P)

/-- `PartialSigAgg`: `s = Σ sᵢ + e·g·tacc`, packaged with the final nonce as a
(pre-)signature; with `T = 0` its `adapt … 0` is the BIP340 signature. -/
def partialSigAgg (ctx : KeyAggCtx n E) (sess : Session n E) (ss : List (ZMod n)) : PreSig n E :=
  ⟨sess.R, ss.sum + sess.e * gOf C ctx * ctx.tacc⟩

omit [DecidableEq X] in
/-- Honest partial signatures pass partial verification. -/
theorem partialSigVerify_sign (ctx : KeyAggCtx n E) (pks : List E) (sess : Session n E)
    (sec : SecSigner n) :
    partialSigVerify C aggCoef ctx pks sess (sec.pub C) (partialSign C aggCoef ctx pks sess sec)
      = true := by
  simp only [partialSigVerify, partialSign, SecSigner.pub, decide_eq_true_eq, C.val_smul_mulG,
    ← map_add, ← map_neg]
  split_ifs <;> rw [← map_add] <;> congr 1 <;> ring

omit [DecidableEq E] [DecidableEq X] in
/-- With `T = 0` and `t = 0`, completing the aggregate is just reading it off. -/
theorem adapt_zero (ps : PreSig n E) : adapt C ps 0 = (C.x ps.R, ps.s) := by
  unfold adapt; split_ifs <;> simp

omit [DecidableEq E] [DecidableEq X] in
/-- The secret aggregate scalar of the final key: `Q = q·G` with
`q = gacc·Σ aᵢ·skᵢ + tacc`; `liftX(x(Q)) = (g·q)·G`. -/
theorem evenScalar_eq_gOf {ctx : KeyAggCtx n E} {q : ZMod n} (hQ : ctx.Q = C.mulG q) :
    C.evenScalar q = gOf C ctx * q := by
  unfold evenScalar gOf; rw [← hQ]; split_ifs <;> ring

/-- One signer in a session, as seen by the aggregator: a witness `sk` for the
public key (`P = sk·G`, not needed by the algorithms), its public data, and
its partial signature. -/
abbrev Part (n : ℕ) (E : Type*) := ZMod n × PubSigner E × ZMod n

omit [DecidableEq E] in
theorem list_sum_map_neg {α : Type*} (l : List α) (f : α → E) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons y ys ih => simp [ih, add_comm]

omit [DecidableEq X] in
/-- The aggregate passes adaptor pre-verification under `x(Q)` whenever every
partial signature passed `PartialSigVerifyInternal`. -/
theorem preVerify_aggregate (parts : List (Part n E)) (hP : ∀ x ∈ parts, x.2.1.P = C.mulG x.1)
    (tweaks : List (ZMod n × Bool)) {ctx₀ ctx : KeyAggCtx n E}
    (h₀ : keyAgg aggCoef ((parts.map (·.1)).map C.mulG) = some ctx₀)
    (h : applyTweaks C ctx₀ tweaks = some ctx) (T : E) (m : M)
    (hR : aggNonce (parts.map (·.2.1))
      (session C nonceCoef challenge ctx (parts.map (·.2.1)) T m).b T ≠ 0)
    (hpart : ∀ x ∈ parts, partialSigVerify C aggCoef ctx ((parts.map (·.1)).map C.mulG)
      (session C nonceCoef challenge ctx (parts.map (·.2.1)) T m) x.2.1 x.2.2 = true) :
    preVerify C challenge (C.x ctx.Q) T m
      (partialSigAgg C ctx (session C nonceCoef challenge ctx (parts.map (·.2.1)) T m)
        (parts.map (·.2.2))) = true := by
  set sks := parts.map (·.1)
  obtain ⟨hQ, hQ0⟩ := keyAgg_tweaks_invariant C aggCoef sks tweaks h₀ h
  set q := ctx.gacc * aggSecret C aggCoef sks + ctx.tacc with hq
  have hq0 : q ≠ 0 := fun h0 => hQ0 (by rw [hQ, h0, map_zero])
  set sess := session C nonceCoef challenge ctx (parts.map (·.2.1)) T m with hsess
  have hRdef : sess.R = aggNonce (parts.map (·.2.1)) sess.b T := by
    simp only [hsess, session]
    split_ifs with h
    · exact absurd h hR
    · rfl
  set g' := gOf C ctx * ctx.gacc
  set pks := sks.map C.mulG
  -- Each partial verification equation, with `Pᵢ = skᵢ·G`.
  have hpart' : ∀ x ∈ parts, C.mulG x.2.2 =
      (if C.hasEvenY sess.R then x.2.1.R₁ + sess.b.val • x.2.1.R₂
        else -(x.2.1.R₁ + sess.b.val • x.2.1.R₂)) +
      C.mulG (sess.e * g' * (aggCoef pks (C.mulG x.1) * x.1)) := by
    intro x hx
    have := hpart x hx
    simp only [partialSigVerify, decide_eq_true_eq, hP x hx, C.val_smul_mulG] at this
    rw [this]; congr 2; ring
  -- Summing them: Σ sᵢ·G = ±(R - T) + (e·g'·Σ aᵢ·skᵢ)·G.
  have hsum : C.mulG (parts.map (·.2.2)).sum =
      (if C.hasEvenY sess.R then sess.R - T else -(sess.R - T)) +
        C.mulG (sess.e * g' * aggSecret C aggCoef sks) := by
    rw [map_list_sum, List.map_map]
    have e1 : List.map (⇑C.mulG ∘ fun x => x.2.2) parts = parts.map (fun x =>
        (if C.hasEvenY sess.R then x.2.1.R₁ + sess.b.val • x.2.1.R₂
          else -(x.2.1.R₁ + sess.b.val • x.2.1.R₂)) +
        C.mulG (sess.e * g' * (aggCoef pks (C.mulG x.1) * x.1))) :=
      List.map_congr_left (fun x hx => hpart' x hx)
    have e2 : (parts.map fun x => C.mulG (sess.e * g' * (aggCoef pks (C.mulG x.1) * x.1))).sum =
        C.mulG (sess.e * g' * aggSecret C aggCoef sks) := by
      rw [aggSecret, List.map_map, ← List.sum_map_mul_left, map_list_sum, List.map_map]
      rfl
    rw [e1, List.sum_map_add, e2, hRdef, aggNonce, add_sub_cancel_right]
    congr 1
    split_ifs <;> simp [List.sum_map_add, list_sum_map_neg, List.smul_sum, List.map_map,
      Function.comp_def,
      add_comm]
  have hl : C.liftX (C.x ctx.Q) = some (C.mulG (C.evenScalar q)) := by
    rw [hQ]; exact C.liftX_x_mulG hq0
  have he : challenge (C.x sess.R) (C.x ctx.Q) m = sess.e := rfl
  simp only [preVerify, partialSigAgg, hl, he, C.val_smul_mulG, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨decide_eq_true (by rw [hRdef]; exact hR), ?_⟩
  rw [map_add, hsum, evenScalar_eq_gOf C hQ, add_assoc, ← map_add]
  congr 2
  rw [hq]; ring

/-- **MuSig2 aggregation soundness**: if every partial signature passed
`PartialSigVerifyInternal`, then
* (adaptor) completing the aggregate with `t`, where `t·G = T`, gives a
  valid BIP340 signature under the aggregate key `x(Q)`; and
* (plain MuSig2, `T = 0`) the aggregate `(x(R), Σ sᵢ + e·g·tacc)` itself is
  a valid BIP340 signature under `x(Q)`. -/
theorem verify_aggregate (parts : List (Part n E)) (hP : ∀ x ∈ parts, x.2.1.P = C.mulG x.1)
    (tweaks : List (ZMod n × Bool)) {ctx₀ ctx : KeyAggCtx n E}
    (h₀ : keyAgg aggCoef ((parts.map (·.1)).map C.mulG) = some ctx₀)
    (h : applyTweaks C ctx₀ tweaks = some ctx) {T : E} {t : ZMod n} (ht : C.mulG t = T) (m : M)
    (hR : aggNonce (parts.map (·.2.1))
      (session C nonceCoef challenge ctx (parts.map (·.2.1)) T m).b T ≠ 0)
    (hpart : ∀ x ∈ parts, partialSigVerify C aggCoef ctx ((parts.map (·.1)).map C.mulG)
      (session C nonceCoef challenge ctx (parts.map (·.2.1)) T m) x.2.1 x.2.2 = true) :
    verify C challenge (C.x ctx.Q) m
      (adapt C (partialSigAgg C ctx (session C nonceCoef challenge ctx (parts.map (·.2.1)) T m)
        (parts.map (·.2.2))) t) = true :=
  verify_adapt C challenge
    (preVerify_aggregate C aggCoef nonceCoef challenge parts hP tweaks h₀ h T m hR hpart) ht

/-- **MuSig2 correctness for honest signers** (BIP327 with `T = 0`): when all
signers follow `Sign`, the aggregated signature verifies under the aggregate key. -/
theorem verify_honest (secs : List (SecSigner n)) (tweaks : List (ZMod n × Bool))
    {ctx₀ ctx : KeyAggCtx n E}
    (h₀ : keyAgg aggCoef (secs.map (fun s => C.mulG s.sk)) = some ctx₀)
    (h : applyTweaks C ctx₀ tweaks = some ctx) (m : M)
    (hR : aggNonce (secs.map (SecSigner.pub C))
      (session C nonceCoef challenge ctx (secs.map (SecSigner.pub C)) 0 m).b 0 ≠ 0) :
    let sess := session C nonceCoef challenge ctx (secs.map (SecSigner.pub C)) 0 m
    let psigs := secs.map (partialSign C aggCoef ctx (secs.map (fun s => C.mulG s.sk)) sess)
    let sig := partialSigAgg C ctx sess psigs
    verify C challenge (C.x ctx.Q) m (C.x sig.R, sig.s) = true := by
  intro sess psigs sig
  let parts : List (Part n E) := secs.map fun s =>
    (s.sk, s.pub C, partialSign C aggCoef ctx (secs.map (fun s => C.mulG s.sk)) sess s)
  have hfst : parts.map (·.1) = secs.map (·.sk) := by simp [parts]
  have hsnd : parts.map (·.2.1) = secs.map (SecSigner.pub C) := by simp [parts]
  have hthd : parts.map (·.2.2) = psigs := by simp [parts, psigs]
  have hpks : (parts.map (·.1)).map C.mulG = secs.map (fun s => C.mulG s.sk) := by
    simp [parts, List.map_map, Function.comp_def]
  have := verify_aggregate C aggCoef nonceCoef challenge parts
    (by intro x hx; simp only [parts, List.mem_map] at hx; obtain ⟨s, _, rfl⟩ := hx; rfl)
    tweaks (hpks ▸ h₀) h (map_zero C.mulG) m (by rw [hsnd]; exact hR)
    (by
      intro x hx
      simp only [parts, List.mem_map] at hx
      obtain ⟨s, _, rfl⟩ := hx
      rw [hsnd, hpks]
      exact partialSigVerify_sign C aggCoef ctx _ _ s)
  rw [hsnd, hthd, adapt_zero] at this
  exact this

/-! ## Taproot key-path funding -/

omit [DecidableEq X] in
/-- **The Taproot tweak is a MuSig2 x-only tweak**: tweaking the aggregate key
context with `t = hash_TapTweak(x(Q) ‖ root)` gives exactly the BIP341 output
key (and its parity). -/
theorem outputKey_eq_applyTweak {T' : Type*} (tweak : X → Option T' → ZMod n)
    {ctx ctx' : KeyAggCtx n E} {q : ZMod n} (hQ : ctx.Q = C.mulG q) (hq : q ≠ 0)
    (root : Option T')
    (h : applyTweak C ctx (tweak (C.x ctx.Q) root) true = some ctx') :
    outputKey C tweak (C.x ctx.Q) root = some (C.x ctx'.Q, C.hasEvenY ctx'.Q) := by
  unfold applyTweak at h
  dsimp only at h
  generalize hQ' : (if (true && !C.hasEvenY ctx.Q) = true then -ctx.Q else ctx.Q) +
    C.mulG (tweak (C.x ctx.Q) root) = Q' at h
  by_cases h0 : Q' = 0
  · simp [h0] at h
  simp only [h0, ↓reduceIte, Option.some.injEq] at h
  subst h
  have hlift : C.liftX (C.x ctx.Q) =
      some (if (true && !C.hasEvenY ctx.Q) = true then -ctx.Q else ctx.Q) := by
    rw [hQ, C.liftX_x_mulG hq]
    congr 1
    unfold evenScalar
    cases C.hasEvenY (C.mulG q) <;> simp [map_neg]
  simp only [outputKey, hlift, ← mulG_eq_val_smul, hQ', h0, ↓reduceIte]

/-- **DLC settlement through the Taproot key path with MuSig2.**
Alice and Bob (keys `sk_A`, `sk_B`) fund an output whose internal key is
their MuSig2 aggregate `Q₀` and whose output key is the BIP341 tweak `q`
(the script tree `root` can hold refund scripts). For the CET of outcome `o`
they run a MuSig2 adaptor session locked to the oracle's anticipation point
`S` and check each other's partial signatures. When the oracle attests `o`
with `(r, s)`, completing the aggregate with `s` is a valid BIP340
signature under `q`, i.e. a valid key-path spend of the funding output. -/
theorem settleKeyPath {T' : Type*} (tweak : X → Option T' → ZMod n) (root : Option T')
    (alice bob : Part n E) (hA : alice.2.1.P = C.mulG alice.1) (hB : bob.2.1.P = C.mulG bob.1)
    {ctx₀ ctx : KeyAggCtx n E}
    (h₀ : keyAgg aggCoef ([alice.1, bob.1].map C.mulG) = some ctx₀)
    (htw : applyTweak C ctx₀ (tweak (C.x ctx₀.Q) root) true = some ctx)
    {opk r : X} {o msg : M} {S : E} {s : ZMod n}
    (hS : anticipate C challenge opk r o = some S)
    (hR : aggNonce [alice.2.1, bob.2.1]
      (session C nonceCoef challenge ctx [alice.2.1, bob.2.1] S msg).b S ≠ 0)
    (hpartA : partialSigVerify C aggCoef ctx ([alice.1, bob.1].map C.mulG)
      (session C nonceCoef challenge ctx [alice.2.1, bob.2.1] S msg) alice.2.1 alice.2.2 = true)
    (hpartB : partialSigVerify C aggCoef ctx ([alice.1, bob.1].map C.mulG)
      (session C nonceCoef challenge ctx [alice.2.1, bob.2.1] S msg) bob.2.1 bob.2.2 = true)
    (hatt : verify C challenge opk o (r, s) = true) :
    -- the funding output key is the tweaked aggregate key …
    outputKey C tweak (C.x ctx₀.Q) root = some (C.x ctx.Q, C.hasEvenY ctx.Q) ∧
    -- … and the completed CET signature is valid for it.
    verify C challenge (C.x ctx.Q) msg
      (adapt C (partialSigAgg C ctx (session C nonceCoef challenge ctx [alice.2.1, bob.2.1] S msg)
        [alice.2.2, bob.2.2]) s) = true := by
  have hS' : C.mulG s = S := by
    rw [anticipate_of_verify C challenge hatt] at hS
    exact Option.some.inj hS
  obtain ⟨hQ₀, hQ₀0⟩ := keyAgg_tweaks_invariant C aggCoef [alice.1, bob.1] [] h₀ rfl
  refine ⟨outputKey_eq_applyTweak C tweak hQ₀ (fun h0 => hQ₀0 (by rw [hQ₀, h0, map_zero])) root
    htw, ?_⟩
  have := verify_aggregate C aggCoef nonceCoef challenge [alice, bob]
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> assumption)
    [(tweak (C.x ctx₀.Q) root, true)] h₀ (by simp [applyTweaks, htw]) hS' msg hR
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> assumption)
  simpa using this

end Taproot.MuSig2
