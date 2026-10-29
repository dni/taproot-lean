import Taproot.BIP340Props
import Taproot.Secp256k1
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.EvalDist.Measure
import VCVio.EvalDist.ProbabilityBounds

/-!
# BIP340 batch verification with hash-derived coefficients

BIP340 batch verification checks `Σ aᵢ·(sᵢ·G - Rᵢ - eᵢ·Pᵢ) = 0` with `a₁ = 1`
and random coefficients `a₂, …, aᵤ`. `batchVerify_sound_bits` shows that one
uniformly random `b`-bit coefficient catches an invalid batch except with
probability `2^-b`. In practice the coefficients are not independent random
values: they are derived deterministically from the batch, and the attacker
chooses the batch. Here they come from a random oracle.

We model two derivations, both as a random oracle with `b`-bit answers:

* **whole-batch derivation**, as in the BIP340 text: coefficient `aᵢ` (for
  `i ≥ 2`) is the hash of the whole batch together with `i`;
* **incremental derivation**, as in libsecp256k1's batch verification API:
  `aᵢ` is the hash of the first `i` entries of the batch, so it is known as
  soon as those entries are, and the attacker may choose the later entries
  after seeing it.

`batchGame`: the attacker, with access to the random oracle, outputs a batch;
the verifier derives the coefficients from the same oracle.
`batch_indexed_sound` and `batch_incremental_sound`: if the attacker makes at
most `q` oracle queries and outputs batches of at most `ℓ` entries, then the
batch passes while containing an invalid signature with probability at most
`(q + ℓ)/2^b`. This holds for every choice of the challenge hash. The
`secp256k1_…` versions take `b = 128`.

For whole-batch derivation one fresh answer can complete at most one batch,
which gives the bound directly. The incremental case needs more care.

For incremental derivation, the proof charges each win to a random oracle answer. Let `j` be the last
invalid entry of the winning batch. Then the prefix `t` of the first `j`
entries already passes, and its equation `Σ aᵢ·defectᵢ = 0` involves only
coefficients of prefixes of `t`. Whichever of those (with a nonzero defect) is
answered last must hit the one value that solves the equation. One fresh
answer can complete many prefixes `t` at once (all cached extensions of the
queried prefix), so a single query can have several bad values. Each such `t`
was already cached, though, and is completed only once. `prEvent_bad_le` makes
this accounting precise with a potential: the number of cached prefixes that
are not complete yet.
-/

open OracleSpec OracleComp
open scoped ENNReal OracleSpec.PrimitiveQuery

namespace Taproot.BIP340Batch

/-! ## A bad-event bound for random oracles -/

section BadEvent

variable {ι Y : Type} [DecidableEq ι] [Fintype Y] [UniformAnswerMeasure (ι →ₒ Y)]

/-- **Bad-event bound with a potential**: run `oa` against a lazily sampled
random oracle. Suppose that whenever the cache `c` is good and `t` is fresh,
the fresh answer makes the cache bad with probability at most `k/|Y|`, and the
potential `Φ` afterwards is at most `Ψ`, where `k + Ψ ≤ 1 + Φ c`. Then a
computation making at most `q` queries ends with a bad cache with probability
at most `(q + Φ c₀)/|Y|`.

With `Φ = 0` and `k = 1` this is the usual "each fresh answer is bad with
probability `1/|Y|`". The potential lets one query be charged for several bad
values (`k > 1`) when earlier queries prepaid for them. -/
theorem prEvent_bad_le {α : Type} (Bad : (ι →ₒ Y).QueryCache → Prop)
    (Φ : (ι →ₒ Y).QueryCache → ℝ≥0∞)
    (hstep : ∀ c t, ¬ Bad c → c t = none → ∃ k Ψ : ℝ≥0∞,
      Pr{let u ← (liftM ((ι →ₒ Y).query t) : OracleComp (ι →ₒ Y) Y)}[Bad (c.cacheQuery t u)] ≤
        k * (Fintype.card Y : ℝ≥0∞)⁻¹ ∧
      (∀ u, Φ (c.cacheQuery t u) ≤ Ψ) ∧ k + Ψ ≤ 1 + Φ c)
    (oa : OracleComp (ι →ₒ Y) α) (q : ℕ) (hq : IsTotalQueryBound oa q)
    (c₀ : (ι →ₒ Y).QueryCache) (h₀ : ¬ Bad c₀) :
    Pr{let z ← (simulateQ (ι →ₒ Y).cachingOracle oa).run c₀}[Bad z.2] ≤
      (q + Φ c₀) * (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing q c₀ with
  | pure x =>
    rw [simulateQ_pure]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_) bot_le
    change z ∈ support (pure (x, c₀) : OracleComp _ _) at hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h₀ h
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hq
    obtain ⟨hpos, hrest⟩ := hq
    rw [simulateQ_bind, cachingOracle.simulateQ_query, StateT.run_bind]
    cases hc : c₀ t with
    | some v =>
      rw [cachingOracle.run_some hc, pure_bind]
      refine (ih v (q - 1) (hrest v) c₀ h₀).trans ?_
      gcongr
      exact_mod_cast Nat.sub_le q 1
    | none =>
      obtain ⟨k, Ψ, hbad, hΨ, hkΨ⟩ := hstep c₀ t h₀ hc
      rw [cachingOracle.run_none hc, bind_map_left]
      refine (prEvent_bind_le_prEvent_add_of_support _ _
        (fun u => Bad (c₀.cacheQuery t u)) _
        (ε := ((q - 1 : ℕ) + Ψ) * (Fintype.card Y : ℝ≥0∞)⁻¹) fun u _ hu => ?_).trans ?_
      · refine (ih u (q - 1) (hrest u) _ hu).trans ?_
        gcongr
        exact hΨ u
      · refine (add_le_add hbad le_rfl).trans ?_
        rw [← add_mul]
        gcongr ?_ * _
        calc k + ((q - 1 : ℕ) + Ψ) = (q - 1 : ℕ) + (k + Ψ) := by ring
          _ ≤ (q - 1 : ℕ) + (1 + Φ c₀) := by gcongr
          _ = q + Φ c₀ := by
            rw [← add_assoc]
            congr 1
            exact_mod_cast Nat.sub_add_cancel hpos

end BadEvent

/-! ## Batches -/

open Curve BIP340 BIP340.Entry

deriving instance DecidableEq for Taproot.BIP340.Entry

section Batch

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- Coefficients only matter at invalid signatures: changing the others keeps a
passing batch passing. -/
theorem batchVerify_congr (hord : PrimeOrder n E) {u : ℕ} (ent : Fin u → Entry n X M)
    {a a' : Fin u → ZMod n} (h : ∀ i, valid C challenge (ent i) = false → a i = a' i)
    (hv : batchVerify C challenge ent a = true) : batchVerify C challenge ent a' = true := by
  rw [batchVerify_iff C challenge hord] at hv ⊢
  refine ⟨hv.1, ?_⟩
  rw [← hv.2]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hi : valid C challenge (ent i)
  · rw [h i hi]
  · rw [((valid_iff C challenge _).mp hi).2.2, nsmul_zero, nsmul_zero]

/-- If every signature after position `j` is valid, a passing batch still
passes when cut after position `j`. -/
theorem batchVerify_take (hord : PrimeOrder n E) (L : List (Entry n X M)) {j : ℕ}
    (hj : j < L.length) (hafter : ∀ i : Fin L.length, j < i → valid C challenge (L.get i) = true)
    (a : ℕ → ZMod n) (hv : batchVerify C challenge L.get (fun i => a i) = true) :
    batchVerify C challenge (L.take (j + 1)).get (fun i => a i) = true := by
  have hlen : (L.take (j + 1)).length = j + 1 := by simp; omega
  rw [batchVerify_iff C challenge hord] at hv ⊢
  obtain ⟨hlift, hsum⟩ := hv
  refine ⟨fun i => ?_, ?_⟩
  · have hi : (i : ℕ) < L.length := by have := i.2; omega
    simpa [List.getElem_take] using hlift ⟨i, hi⟩
  · let f : ℕ → E := fun i =>
      if h : i < L.length then (a i).val • defect C challenge L[i] else 0
    have hL : ∀ i : Fin L.length, (a i).val • defect C challenge (L.get i) = f i :=
      fun i => by simp [f, i.2]
    have hT : ∀ i : Fin (L.take (j + 1)).length,
        (a i).val • defect C challenge ((L.take (j + 1)).get i) = f i := fun i => by
      have hi : (i : ℕ) < L.length := by have := i.2; omega
      simp [f, hi, List.getElem_take]
    rw [Finset.sum_congr rfl fun i _ => hL i, Fin.sum_univ_eq_sum_range f] at hsum
    rw [Finset.sum_congr rfl fun i _ => hT i, Fin.sum_univ_eq_sum_range f, hlen, ← hsum]
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i hi hi' => ?_
    simp only [Finset.mem_range] at hi hi'
    have hv := ((valid_iff C challenge _).mp (hafter ⟨i, hi⟩ (by change j < i; omega))).2.2
    simp only [List.get_eq_getElem] at hv
    simp [f, hi, hv]

/-- Batch verification of `L` with coefficients `as`. -/
def verifyList (L : List (Entry n X M)) (as : List (ZMod n)) : Bool :=
  batchVerify C challenge L.get (fun i => as.getD i 0)

/-- The attacker wins if its batch passes although it contains an invalid signature. -/
def Wins (z : List (Entry n X M) × List (ZMod n)) : Prop :=
  verifyList C challenge z.1 z.2 = true ∧
    ∃ i : Fin z.1.length, valid C challenge (z.1.get i) = false

end Batch

/-! ## Deriving the coefficients from a random oracle -/

section Derivation

variable {n : ℕ} {X M : Type} {K : Type} [DecidableEq K] (b : ℕ)
  (key : List (Entry n X M) → ℕ → K)

/-- A random oracle with `b`-bit answers on inputs of type `K`. -/
abbrev KeySpec (K : Type) (b : ℕ) := K →ₒ Fin (2 ^ b)

/-- The verifier's coefficient for position `i` (from `0`) of batch `L`: `1`
for the first signature (BIP340's `a₁ = 1`), otherwise the hash of `key L i`. -/
def coeffQuery (L : List (Entry n X M)) (i : ℕ) : OracleComp (KeySpec K b) (ZMod n) :=
  if i = 0 then pure 1
  else (fun h : Fin (2 ^ b) => ((h : ℕ) : ZMod n)) <$>
    (liftM ((KeySpec K b).query (key L i)) : OracleComp (KeySpec K b) (Fin (2 ^ b)))

/-- The batch verification game: the attacker `adv` outputs a batch, then the
verifier derives its coefficients from the same random oracle. -/
def batchGame (adv : OracleComp (KeySpec K b) (List (Entry n X M))) :
    OracleComp (KeySpec K b) (List (Entry n X M) × List (ZMod n)) := do
  let L ← adv
  let as ← (List.range L.length).mapM (coeffQuery b key L)
  return (L, as)

theorem coeffQuery_spec (L : List (Entry n X M)) (i : ℕ) (c : (KeySpec K b).QueryCache)
    (z : ZMod n × (KeySpec K b).QueryCache)
    (hz : z ∈ support ((simulateQ (KeySpec K b).cachingOracle (coeffQuery b key L i)).run c)) :
    (i = 0 → z.1 = 1) ∧
      (i ≠ 0 → ∃ h : Fin (2 ^ b), z.2 (key L i) = some h ∧ z.1 = ((h : ℕ) : ZMod n)) := by
  unfold coeffQuery at hz
  split_ifs at hz with hi
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨fun _ => rfl, fun h => absurd hi h⟩
  · rw [simulateQ_map, cachingOracle.simulateQ_query, StateT.run_map, support_map] at hz
    obtain ⟨⟨h, c'⟩, hmem, rfl⟩ := hz
    exact ⟨fun h0 => absurd h0 hi, fun _ => ⟨h, cachingOracle_query_caches _ _ _ _ hmem, rfl⟩⟩

theorem coeffs_spec (L : List (Entry n X M)) (is : List ℕ) (c : (KeySpec K b).QueryCache)
    (z : List (ZMod n) × (KeySpec K b).QueryCache)
    (hz : z ∈ support
      ((simulateQ (KeySpec K b).cachingOracle (is.mapM (coeffQuery b key L))).run c)) :
    ∀ k (hk : k < is.length), (is[k] = 0 → z.1.getD k 0 = 1) ∧
      (is[k] ≠ 0 → ∃ h : Fin (2 ^ b),
        z.2 (key L is[k]) = some h ∧ z.1.getD k 0 = ((h : ℕ) : ZMod n)) := by
  induction is generalizing c z with
  | nil => intro k hk; simp at hk
  | cons i is ih =>
    rw [List.mapM_cons, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨a, c₁⟩, h₁, hz⟩ := hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨as, c₂⟩, h₂, hz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    intro k hk
    cases k with
    | zero =>
      obtain ⟨hz0, hnz⟩ := coeffQuery_spec b key L i c _ h₁
      refine ⟨fun h => by simpa using hz0 h, fun h => ?_⟩
      obtain ⟨v, hv, ha⟩ := hnz (by simpa using h)
      have hle := simulateQ_cachingOracle_cache_le _ c₁ _ h₂
      exact ⟨v, by simpa using hle hv, by simpa using ha⟩
    | succ k =>
      simpa using ih c₁ (as, c₂) h₂ k (by simpa using hk)

/-- **What the verifier leaves in the cache**: coefficient `0` is `1`, and every
other coefficient `k` is the cached hash of `key L k`. -/
theorem game_spec (adv : OracleComp (KeySpec K b) (List (Entry n X M)))
    (L : List (Entry n X M)) (as : List (ZMod n)) (c : (KeySpec K b).QueryCache)
    (hz : ((L, as), c) ∈
      support ((simulateQ (KeySpec K b).cachingOracle (batchGame b key adv)).run ∅)) :
    (∀ k < L.length, k = 0 → as.getD k 0 = 1) ∧
      (∀ k < L.length, k ≠ 0 → ∃ h : Fin (2 ^ b),
        c (key L k) = some h ∧ as.getD k 0 = ((h : ℕ) : ZMod n)) := by
  unfold batchGame at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨L', c₁⟩, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨as', c₂⟩, h₂, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hz
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hz
  have hco := coeffs_spec b key L (List.range L.length) c₁ (as, c) h₂
  refine ⟨fun k hk h0 => by simpa using (hco k (by simpa using hk)).1 (by simpa using h0),
    fun k hk h0 => ?_⟩
  obtain ⟨h, hc, ha⟩ := (hco k (by simpa using hk)).2 (by simpa using h0)
  rw [List.getElem_range] at hc
  exact ⟨h, hc, by simpa using ha⟩

omit [DecidableEq K] in
theorem coeffQuery_bound (L : List (Entry n X M)) (i : ℕ) :
    IsTotalQueryBound (coeffQuery b key L i) 1 := by
  unfold coeffQuery
  split_ifs
  · trivial
  · rw [map_eq_bind_pure_comp, isTotalQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun _ => trivial⟩

omit [DecidableEq K] in
theorem coeffs_bound (L : List (Entry n X M)) (is : List ℕ) :
    IsTotalQueryBound (is.mapM (coeffQuery b key L)) is.length := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    rw [List.mapM_cons]
    refine (isTotalQueryBound_bind (coeffQuery_bound b key L i) fun _ =>
      isTotalQueryBound_bind (n₂ := 0) ih fun _ => ?_).mono (by simp; omega)
    trivial

omit [DecidableEq K] in
theorem batchGame_bound (adv : OracleComp (KeySpec K b) (List (Entry n X M)))
    {q ℓ : ℕ} (hq : IsTotalQueryBound adv q) (hℓ : ∀ L ∈ support adv, L.length ≤ ℓ) :
    IsTotalQueryBound (batchGame b key adv) (q + ℓ) := by
  unfold batchGame
  refine isTotalQueryBound_bind_of_mem_support hq fun L hL => ?_
  refine (isTotalQueryBound_bind (n₂ := 0) (coeffs_bound b key L _) fun _ => ?_).mono
    (by simpa using hℓ L hL)
  trivial

end Derivation

/-! ## Incremental derivation -/

section Incremental

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n) (b : ℕ)

/-- Incremental derivation hashes the first `i + 1` entries. -/
def prefixKey (L : List (Entry n X M)) (i : ℕ) : List (Entry n X M) := L.take (i + 1)

/-- The random oracle of incremental derivation: a batch prefix ↦ a `b`-bit value. -/
abbrev PrefixSpec (n : ℕ) (X M : Type) (b : ℕ) := KeySpec (List (Entry n X M)) b

/-! ### Bookkeeping on the random oracle's cache -/

/-- The prefixes stored in cache `c`. -/
def cached (c : (PrefixSpec n X M b).QueryCache) (x : List (Entry n X M)) : Prop := c x ≠ none

/-- Batch `t` has length at least two and its last signature is invalid. -/
def Rel (t : List (Entry n X M)) : Prop :=
  ∃ h : 1 < t.length, valid C challenge (t.get ⟨t.length - 1, by omega⟩) = false

/-- Every prefix of `t` that determines the coefficient of an invalid
signature (other than the first) lies in `S`. -/
def Covers (S : List (Entry n X M) → Prop) (t : List (Entry n X M)) : Prop :=
  ∀ i : Fin t.length, (i : ℕ) ≠ 0 → valid C challenge (t.get i) = false → S (t.take (i + 1))

/-- The coefficients of batch `t` as recorded in cache `c`. -/
def cacheCoeff (c : (PrefixSpec n X M b).QueryCache) (t : List (Entry n X M))
    (i : Fin t.length) : ZMod n :=
  if (i : ℕ) = 0 then 1 else ((c (t.take (i + 1))).map fun h => ((h : ℕ) : ZMod n)).getD 0

/-- The bad event: some batch with an invalid last signature has all its
relevant coefficients in the cache, and passes with them. -/
def Bad (c : (PrefixSpec n X M b).QueryCache) : Prop :=
  ∃ t, Rel C challenge t ∧ Covers C challenge (cached b c) t ∧
    batchVerify C challenge t.get (cacheCoeff b c t) = true

/-- Batches in `S` that are not covered by `S` yet. -/
def IncOf (S : List (Entry n X M) → Prop) : Set (List (Entry n X M)) :=
  {t | Rel C challenge t ∧ S t ∧ ¬ Covers C challenge S t}

/-- The potential: how many cached batches still wait for a coefficient. -/
noncomputable def Φ (c : (PrefixSpec n X M b).QueryCache) : ℝ≥0∞ :=
  ((IncOf C challenge (cached b c)).encard : ℝ≥0∞)

omit [DecidableEq M] in
theorem covers_mono {S S' : List (Entry n X M) → Prop} (h : ∀ x, S x → S' x)
    {t : List (Entry n X M)} (ht : Covers C challenge S t) : Covers C challenge S' t :=
  fun i hi hv => h _ (ht i hi hv)

omit [Fact n.Prime] in
theorem cached_cacheQuery (c : (PrefixSpec n X M b).QueryCache) (p : List (Entry n X M))
    (u : Fin (2 ^ b)) : cached b (c.cacheQuery p u) = fun x => cached b c x ∨ x = p := by
  funext x
  by_cases hx : x = p
  · subst hx
    simp [cached]
  · simp [cached, hx]

omit [DecidableEq M] in
theorem bad_empty : ¬ Bad C challenge b ∅ := by
  rintro ⟨t, ⟨h1, hlast⟩, hcov, -⟩
  exact hcov ⟨t.length - 1, by omega⟩ (by change t.length - 1 ≠ 0; omega) hlast
    (by rw [Nat.sub_add_cancel (by omega), List.take_of_length_le le_rfl]; rfl)

omit [DecidableEq M] in
theorem Φ_empty : Φ C challenge b ∅ = 0 := by
  have : IncOf C challenge (cached b (∅ : (PrefixSpec n X M b).QueryCache)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun t ht => ht.2.1 rfl
  simp [Φ, this]

/-- **One fresh answer**: if the cache is good and the prefix `p` is fresh,
the answer for `p` makes the cache bad with probability at most `k/2^b`, where
`k` is the number of batches the answer completes, and the potential drops by
`k - 1`. -/
theorem bad_step [UniformAnswerMeasure (PrefixSpec n X M b)] (hord : PrimeOrder n E)
    (hb : 2 ^ b ≤ n)
    (c : (PrefixSpec n X M b).QueryCache) (p : List (Entry n X M))
    (hbad : ¬ Bad C challenge b c) (hp : c p = none) :
    ∃ k Ψ : ℝ≥0∞,
      Pr{let u ← (liftM ((PrefixSpec n X M b).query p) :
          OracleComp (PrefixSpec n X M b) (Fin (2 ^ b)))}[
        Bad C challenge b (c.cacheQuery p u)] ≤ k * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ ∧
      (∀ u, Φ C challenge b (c.cacheQuery p u) ≤ Ψ) ∧ k + Ψ ≤ 1 + Φ C challenge b c := by
  classical
  let S : List (Entry n X M) → Prop := fun x => cached b c x ∨ x = p
  have hS : ∀ u, cached b (c.cacheQuery p u) = S := cached_cacheQuery b c p
  -- the batches that the answer for `p` completes
  let NC : Set (List (Entry n X M)) :=
    {t | Rel C challenge t ∧ Covers C challenge S t ∧ ¬ Covers C challenge (cached b c) t}
  refine ⟨(NC.encard : ℝ≥0∞), ((IncOf C challenge S).encard : ℝ≥0∞), ?_, ?_, ?_⟩
  · by_cases hfin : NC.Finite
    swap
    · rw [Set.Infinite.encard_eq hfin, ENat.toENNReal_top, ENNReal.top_mul]
      · exact le_top
      · exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    rw [hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    refine (prEvent_mono_of_support _ _
      (fun u => ∃ t ∈ hfin.toFinset,
        batchVerify C challenge t.get (cacheCoeff b (c.cacheQuery p u) t) = true)
      fun u _ hu => ?_).trans (prEvent_exists_finset_le_card_mul _ _ _ fun t ht => ?_)
    · obtain ⟨t, hrel, hcov, hbv⟩ := hu
      rw [hS u] at hcov
      refine ⟨t, hfin.mem_toFinset.mpr ⟨hrel, hcov, fun hcov' => hbad ⟨t, hrel, hcov', ?_⟩⟩, hbv⟩
      refine batchVerify_congr C challenge hord t.get (fun i hi => ?_) hbv
      unfold cacheCoeff
      split_ifs with hi0
      · rfl
      · have hne : t.take (i + 1) ≠ p := fun h => hcov' i hi0 hi (h ▸ hp)
        rw [QueryCache.cacheQuery_of_ne _ _ hne]
    · obtain ⟨hrel, hcov, hncov⟩ := hfin.mem_toFinset.mp ht
      obtain ⟨i₀, hi₀, hinv, hnone⟩ : ∃ i₀ : Fin t.length, (i₀ : ℕ) ≠ 0 ∧
          valid C challenge (t.get i₀) = false ∧ ¬ cached b c (t.take (i₀ + 1)) := by
        by_contra! h
        exact hncov fun i hi hv => h i hi hv
      have hp₀ : t.take (i₀ + 1) = p := (hcov i₀ hi₀ hinv).resolve_left hnone
      rw [prEvent_liftM_query_eq_card_div]
      have hcard : (Finset.univ.filter fun u : Fin (2 ^ b) =>
          batchVerify C challenge t.get (cacheCoeff b (c.cacheQuery p u) t) = true).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun u hu u' hu' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
        have h := batchVerify_sound C challenge hord t.get hinv (fun i hi => by
          unfold cacheCoeff
          split_ifs with hi0
          · rfl
          · have hne : t.take (i + 1) ≠ p := by
              rw [← hp₀]
              intro h
              apply hi
              have := congrArg List.length h
              simp only [List.length_take] at this
              have := i.2
              have := i₀.2
              ext
              omega
            rw [QueryCache.cacheQuery_of_ne _ _ hne, QueryCache.cacheQuery_of_ne _ _ hne]) hu hu'
        subst hp₀
        simp only [cacheCoeff, hi₀, ↓reduceIte, QueryCache.cacheQuery_self] at h
        have h' : ((u : ℕ) : ZMod n) = ((u' : ℕ) : ZMod n) := by simpa using h
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (u.2.trans_le hb),
          Nat.mod_eq_of_lt (u'.2.trans_le hb)] at h'
        exact Fin.ext h'
      calc ((Finset.univ.filter fun u : Fin (2 ^ b) =>
            batchVerify C challenge t.get (cacheCoeff b (c.cacheQuery p u) t) = true).card :
              ℝ≥0∞) / (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)
          ≤ 1 / (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞) := by gcongr; exact_mod_cast hcard
        _ = _ := one_div _
  · intro u
    rw [Φ, hS u]
  · have hdisj : Disjoint NC (IncOf C challenge S) :=
      Set.disjoint_left.mpr fun t h1 h2 => h2.2.2 h1.2.1
    have hsub : NC ∪ IncOf C challenge S ⊆ IncOf C challenge (cached b c) ∪ {p} := by
      rintro t (⟨hrel, hcov, hncov⟩ | ⟨hrel, hSt, hncov⟩)
      · by_cases htp : t = p
        · exact Or.inr htp
        · refine Or.inl ⟨hrel, ?_, hncov⟩
          obtain ⟨h1, hlast⟩ := hrel
          have := hcov ⟨t.length - 1, by omega⟩ (by change t.length - 1 ≠ 0; omega) hlast
          rw [show t.length - 1 + 1 = t.length by omega, List.take_of_length_le le_rfl] at this
          exact this.resolve_right htp
      · by_cases htp : t = p
        · exact Or.inr htp
        · exact Or.inl ⟨hrel, hSt.resolve_right htp,
            fun hcov => hncov (covers_mono C challenge (fun x hx => Or.inl hx) hcov)⟩
    calc (NC.encard : ℝ≥0∞) + ((IncOf C challenge S).encard : ℝ≥0∞)
        = ((NC ∪ IncOf C challenge S).encard : ℝ≥0∞) := by
          rw [Set.encard_union_eq hdisj, ENat.toENNReal_add]
      _ ≤ ((IncOf C challenge (cached b c) ∪ {p}).encard : ℝ≥0∞) :=
          ENat.toENNReal_le.mpr (Set.encard_le_encard hsub)
      _ ≤ ((IncOf C challenge (cached b c)).encard + ({p} : Set _).encard : ℕ∞) :=
          ENat.toENNReal_le.mpr (Set.encard_union_le _ _)
      _ = 1 + Φ C challenge b c := by
          rw [ENat.toENNReal_add, Set.encard_singleton, ENat.toENNReal_one, add_comm, Φ]

/-- **A win leaves a bad cache**: if the batch passes although it contains an
invalid signature, cut it after its last invalid signature; that prefix has a
cached coefficient for each invalid signature and passes with them. -/
theorem wins_bad (hord : PrimeOrder n E)
    (adv : OracleComp (PrefixSpec n X M b) (List (Entry n X M)))
    (z : (List (Entry n X M) × List (ZMod n)) × (PrefixSpec n X M b).QueryCache)
    (hz : z ∈ support
      ((simulateQ (PrefixSpec n X M b).cachingOracle (batchGame b prefixKey adv)).run ∅))
    (hw : Wins C challenge z.1) : Bad C challenge b z.2 := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  obtain ⟨⟨L, as⟩, c₂⟩ := z
  change Bad C challenge b c₂
  obtain ⟨h1, h2'⟩ := game_spec b prefixKey adv L as c₂ hz
  have h2 : ∀ k < L.length, k ≠ 0 → ∃ h : Fin (2 ^ b),
      c₂ (L.take (k + 1)) = some h ∧ as.getD k 0 = ((h : ℕ) : ZMod n) := h2'
  obtain ⟨hv, i, hi⟩ := hw
  simp only at hv i hi
  -- the last invalid signature
  classical
  let F := Finset.univ.filter fun j : Fin L.length => valid C challenge (L.get j) = false
  have hF : F.Nonempty := ⟨i, by simpa [F] using hi⟩
  set j := F.max' hF with hjdef
  have hj : valid C challenge (L.get j) = false := by
    have := F.max'_mem hF
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  have hafter : ∀ i : Fin L.length, j < i → valid C challenge (L.get i) = true := by
    intro i hji
    by_contra hvi
    have : i ∈ F := by simpa [F] using hvi
    exact absurd (F.le_max' i this) (not_le.mpr hji)
  have hj0 : (j : ℕ) ≠ 0 := by
    intro hj0
    have hsingle := batchVerify_sound_single C challenge hord L.get hj
      (fun i hi => hafter i (by
        rw [Fin.lt_def, hj0]
        exact Nat.pos_of_ne_zero fun h => hi (Fin.ext (h.trans hj0.symm))))
      (a := fun i => as.getD i 0) (by rw [h1 j j.2 hj0]; exact one_ne_zero)
    unfold verifyList at hv
    rw [hv] at hsingle
    cases hsingle
  have hlen : (L.take (j + 1)).length = j + 1 := by simp
  refine ⟨L.take (j + 1), ⟨by omega, ?_⟩, fun i hi0 hinv => ?_, ?_⟩
  · simpa [List.getElem_take, hlen] using hj
  · have hi : (i : ℕ) < L.length := by have := i.2; omega
    obtain ⟨h, hc, -⟩ := h2 i hi hi0
    rw [List.take_take, min_eq_left (by have := i.2; omega)]
    simp [cached, hc]
  · have := batchVerify_take C challenge hord L j.2 hafter (fun k => as.getD k 0) hv
    refine batchVerify_congr C challenge hord _ (fun i _ => ?_) this
    have hi : (i : ℕ) < L.length := by have := i.2; omega
    unfold cacheCoeff
    split_ifs with hi0
    · exact h1 i hi hi0
    · obtain ⟨h, hc, ha⟩ := h2 i hi hi0
      rw [List.take_take, min_eq_left (by have := i.2; omega), hc]
      simpa using ha

/-- **BIP340 batch verification is sound with incrementally hash-derived
coefficients**, in the random oracle model: the coefficient of signature `i`
(for `i ≥ 2`) is a `b`-bit hash of the first `i` entries, with `2^b ≤ n`. An
attacker that makes at most `q` oracle queries and outputs batches of at most
`ℓ` signatures gets a batch containing an invalid signature accepted with
probability at most `(q + ℓ)/2^b`. This holds for every challenge hash. -/
theorem batch_incremental_sound [UniformAnswerMeasure (PrefixSpec n X M b)]
    (hord : PrimeOrder n E) (hb : 2 ^ b ≤ n)
    (adv : OracleComp (PrefixSpec n X M b) (List (Entry n X M))) (q ℓ : ℕ)
    (hq : IsTotalQueryBound adv q) (hℓ : ∀ L ∈ support adv, L.length ≤ ℓ) :
    Pr{let z ← (simulateQ (PrefixSpec n X M b).cachingOracle
      (batchGame b prefixKey adv)).run ∅}[Wins C challenge z.1] ≤
        ((q + ℓ : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ) := by
  have hmain := prEvent_bad_le (Bad C challenge b) (Φ C challenge b)
    (fun c t h₁ h₂ => bad_step C challenge b hord hb c t h₁ h₂) (batchGame b prefixKey adv)
    (q + ℓ)
    (batchGame_bound b prefixKey adv hq hℓ) ∅ (bad_empty C challenge b)
  rw [Φ_empty, add_zero, Fintype.card_fin] at hmain
  rw [div_eq_mul_inv]
  exact (prEvent_mono_of_support _ _ _ fun z hz hw =>
    wins_bad C challenge b hord adv z hz hw).trans hmain

end Incremental

/-! ## Derivation from the whole batch

BIP340 itself derives the coefficients from a seed that hashes the whole
batch, expanded with a CSPRNG. We idealize this as a random oracle on
`(batch, index)`. Each coefficient now depends on every entry, so one fresh
answer completes at most one batch and no potential is needed. -/

section Indexed

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n) (b : ℕ)

/-- Coefficient `i` hashes the whole batch together with `i`. -/
def indexKey (L : List (Entry n X M)) (i : ℕ) : List (Entry n X M) × ℕ := (L, i)

/-- The random oracle of whole-batch derivation: `(batch, index)` ↦ a `b`-bit value. -/
abbrev IndexSpec (n : ℕ) (X M : Type) (b : ℕ) := KeySpec (List (Entry n X M) × ℕ) b

namespace Indexed

/-- The coefficients of batch `L` as recorded in cache `c`. -/
def cacheCoeff (c : (IndexSpec n X M b).QueryCache) (L : List (Entry n X M))
    (i : Fin L.length) : ZMod n :=
  if (i : ℕ) = 0 then 1 else ((c (L, i)).map fun h => ((h : ℕ) : ZMod n)).getD 0

/-- The bad event: some batch with an invalid signature has the coefficients
of all its invalid signatures in the cache, and passes with them. -/
def Bad (c : (IndexSpec n X M b).QueryCache) : Prop :=
  ∃ L : List (Entry n X M), (∃ j : Fin L.length, valid C challenge (L.get j) = false) ∧
    (∀ i : Fin L.length, (i : ℕ) ≠ 0 → valid C challenge (L.get i) = false →
      c (L, i) ≠ none) ∧
    batchVerify C challenge L.get (cacheCoeff b c L) = true

omit [DecidableEq M] in
theorem bad_empty (hord : PrimeOrder n E) : ¬ Bad C challenge b ∅ := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  rintro ⟨L, ⟨j, hj⟩, hcov, hbv⟩
  -- every invalid signature sits at position `0`
  have h0 : ∀ i : Fin L.length, valid C challenge (L.get i) = false → (i : ℕ) = 0 :=
    fun i hi => by_contra fun h => hcov i h hi rfl
  have hsingle := batchVerify_sound_single C challenge hord L.get hj
    (fun i hi => by
      by_contra hv
      exact hi (Fin.ext ((h0 i (by simpa using hv)).trans (h0 j hj).symm)))
    (a := cacheCoeff b ∅ L) (by simp [cacheCoeff, h0 j hj])
  rw [hbv] at hsingle
  cases hsingle

/-- **One fresh answer**: the answer for `(L, k)` can only complete batch `L`,
and at most one value of it makes `L` pass. -/
theorem bad_step [UniformAnswerMeasure (IndexSpec n X M b)] (hord : PrimeOrder n E)
    (hb : 2 ^ b ≤ n) (c : (IndexSpec n X M b).QueryCache) (p : List (Entry n X M) × ℕ)
    (hbad : ¬ Bad C challenge b c) (hp : c p = none) :
    ∃ k Ψ : ℝ≥0∞,
      Pr{let u ← (liftM ((IndexSpec n X M b).query p) :
          OracleComp (IndexSpec n X M b) (Fin (2 ^ b)))}[
        Bad C challenge b (c.cacheQuery p u)] ≤ k * (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)⁻¹ ∧
      (∀ u, (fun _ => (0 : ℝ≥0∞)) (c.cacheQuery p u) ≤ Ψ) ∧
        k + Ψ ≤ 1 + (fun _ => (0 : ℝ≥0∞)) c := by
  classical
  refine ⟨1, 0, ?_, fun _ => le_rfl, by simp⟩
  obtain ⟨L₀, k₀⟩ := p
  -- a bad answer makes `L₀` pass, and position `k₀` holds an invalid signature
  have hcand : ∀ u, Bad C challenge b (c.cacheQuery (L₀, k₀) u) →
      ∃ hk : k₀ < L₀.length, k₀ ≠ 0 ∧ valid C challenge (L₀.get ⟨k₀, hk⟩) = false ∧
        batchVerify C challenge L₀.get (cacheCoeff b (c.cacheQuery (L₀, k₀) u) L₀) = true := by
    rintro u ⟨L, hinv, hcov, hbv⟩
    by_cases hcovc : ∀ i : Fin L.length, (i : ℕ) ≠ 0 → valid C challenge (L.get i) = false →
        c (L, i) ≠ none
    · refine absurd ⟨L, hinv, hcovc, batchVerify_congr C challenge hord L.get (fun i hi => ?_)
        hbv⟩ hbad
      unfold cacheCoeff
      split_ifs with hi0
      · rfl
      · have hne : ((L, (i : ℕ)) : List (Entry n X M) × ℕ) ≠ (L₀, k₀) :=
          fun h => hcovc i hi0 hi (h ▸ hp)
        rw [QueryCache.cacheQuery_of_ne _ _ hne]
    · push Not at hcovc
      obtain ⟨i₀, hi₀, hv₀, hnone⟩ := hcovc
      have heq : ((L, (i₀ : ℕ)) : List (Entry n X M) × ℕ) = (L₀, k₀) := by
        by_contra hne
        exact hcov i₀ hi₀ hv₀ (by rwa [QueryCache.cacheQuery_of_ne _ _ hne])
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨i₀.2, hi₀, hv₀, hbv⟩
  by_cases hk : ∃ hk : k₀ < L₀.length, k₀ ≠ 0 ∧ valid C challenge (L₀.get ⟨k₀, hk⟩) = false
  swap
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => ?_) bot_le
    obtain ⟨hk', hk0, hv, -⟩ := hcand u hu
    exact hk ⟨hk', hk0, hv⟩
  obtain ⟨hk, hk0, hv⟩ := hk
  refine (prEvent_mono_of_support _ _
    (fun u => batchVerify C challenge L₀.get (cacheCoeff b (c.cacheQuery (L₀, k₀) u) L₀) = true)
    fun u _ hu => (hcand u hu).2.2.2).trans ?_
  rw [prEvent_liftM_query_eq_card_div, one_mul]
  have hcard : (Finset.univ.filter fun u : Fin (2 ^ b) =>
      batchVerify C challenge L₀.get (cacheCoeff b (c.cacheQuery (L₀, k₀) u) L₀) = true).card ≤ 1 :=
      by
    refine Finset.card_le_one.mpr fun u hu u' hu' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
    have h := batchVerify_sound C challenge hord L₀.get (j := ⟨k₀, hk⟩) hv (fun i hi => by
      unfold cacheCoeff
      split_ifs with hi0
      · rfl
      · have hne : ((L₀, (i : ℕ)) : List (Entry n X M) × ℕ) ≠ (L₀, k₀) :=
          fun h => hi (Fin.ext (Prod.mk.inj h).2)
        rw [QueryCache.cacheQuery_of_ne _ _ hne, QueryCache.cacheQuery_of_ne _ _ hne]) hu hu'
    simp only [cacheCoeff, hk0, ↓reduceIte, QueryCache.cacheQuery_self] at h
    have h' : ((u : ℕ) : ZMod n) = ((u' : ℕ) : ZMod n) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (u.2.trans_le hb),
      Nat.mod_eq_of_lt (u'.2.trans_le hb)] at h'
    exact Fin.ext h'
  calc ((Finset.univ.filter fun u : Fin (2 ^ b) =>
        batchVerify C challenge L₀.get (cacheCoeff b (c.cacheQuery (L₀, k₀) u) L₀) = true).card :
          ℝ≥0∞) / (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞)
      ≤ 1 / (Fintype.card (Fin (2 ^ b)) : ℝ≥0∞) := by gcongr; exact_mod_cast hcard
    _ = _ := one_div _

/-- **A win leaves a bad cache**: the verifier cached the coefficient of every
signature of the winning batch. -/
theorem wins_bad (hord : PrimeOrder n E)
    (adv : OracleComp (IndexSpec n X M b) (List (Entry n X M)))
    (z : (List (Entry n X M) × List (ZMod n)) × (IndexSpec n X M b).QueryCache)
    (hz : z ∈ support
      ((simulateQ (IndexSpec n X M b).cachingOracle (batchGame b indexKey adv)).run ∅))
    (hw : Wins C challenge z.1) : Bad C challenge b z.2 := by
  obtain ⟨⟨L, as⟩, c⟩ := z
  change Bad C challenge b c
  obtain ⟨h1, h2'⟩ := game_spec b indexKey adv L as c hz
  have h2 : ∀ k < L.length, k ≠ 0 → ∃ h : Fin (2 ^ b),
      c (L, k) = some h ∧ as.getD k 0 = ((h : ℕ) : ZMod n) := h2'
  obtain ⟨hv, i, hi⟩ := hw
  refine ⟨L, ⟨i, hi⟩, fun i hi0 _ => ?_, ?_⟩
  · obtain ⟨h, hc, -⟩ := h2 i i.2 hi0
    simp [hc]
  · refine batchVerify_congr C challenge hord _ (fun i _ => ?_) hv
    unfold cacheCoeff
    split_ifs with hi0
    · exact h1 i i.2 hi0
    · obtain ⟨h, hc, ha⟩ := h2 i i.2 hi0
      rw [hc]
      simpa using ha

end Indexed

/-- **BIP340 batch verification is sound with coefficients derived from the
whole batch**, in the random oracle model: the coefficient of signature `i`
(for `i ≥ 2`) is a `b`-bit hash of the batch and `i`, with `2^b ≤ n`. An
attacker that makes at most `q` oracle queries and outputs batches of at most
`ℓ` signatures gets a batch containing an invalid signature accepted with
probability at most `(q + ℓ)/2^b`. This holds for every challenge hash. -/
theorem batch_indexed_sound [UniformAnswerMeasure (IndexSpec n X M b)]
    (hord : PrimeOrder n E) (hb : 2 ^ b ≤ n)
    (adv : OracleComp (IndexSpec n X M b) (List (Entry n X M))) (q ℓ : ℕ)
    (hq : IsTotalQueryBound adv q) (hℓ : ∀ L ∈ support adv, L.length ≤ ℓ) :
    Pr{let z ← (simulateQ (IndexSpec n X M b).cachingOracle
      (batchGame b indexKey adv)).run ∅}[Wins C challenge z.1] ≤
        ((q + ℓ : ℕ) : ℝ≥0∞) / (2 ^ b : ℕ) := by
  have hmain := prEvent_bad_le (Indexed.Bad C challenge b) (fun _ => 0)
    (fun c t h₁ h₂ => Indexed.bad_step C challenge b hord hb c t h₁ h₂)
    (batchGame b indexKey adv) (q + ℓ) (batchGame_bound b indexKey adv hq hℓ) ∅
    (Indexed.bad_empty C challenge b hord)
  rw [add_zero, Fintype.card_fin] at hmain
  rw [div_eq_mul_inv]
  exact (prEvent_mono_of_support _ _ _ fun z hz hw =>
    Indexed.wins_bad C challenge b hord adv z hz hw).trans hmain

end Indexed

/-! ## On secp256k1 with 128-bit coefficients -/

section Secp256k1

open Secp256k1

theorem two_pow_128_le_n : 2 ^ 128 ≤ n := by decide

/-- `batch_incremental_sound` on secp256k1 with 128-bit coefficients: an
invalid batch is accepted with probability at most `(q + ℓ)/2^128`. -/
theorem secp256k1_batch_incremental_sound {M : Type} [DecidableEq M]
    (challenge : F → F → M → ZMod n) [UniformAnswerMeasure (PrefixSpec n F M 128)]
    (hord : PrimeOrder n Point) (adv : OracleComp (PrefixSpec n F M 128) (List (Entry n F M)))
    (q ℓ : ℕ) (hq : IsTotalQueryBound adv q) (hℓ : ∀ L ∈ support adv, L.length ≤ ℓ) :
    Pr{let z ← (simulateQ (PrefixSpec n F M 128).cachingOracle
      (batchGame 128 prefixKey adv)).run ∅}[Wins secp256k1 challenge z.1] ≤
        ((q + ℓ : ℕ) : ℝ≥0∞) / (2 ^ 128 : ℕ) :=
  batch_incremental_sound secp256k1 challenge 128 hord two_pow_128_le_n adv q ℓ hq hℓ

/-- `batch_indexed_sound` on secp256k1 with 128-bit coefficients: an invalid
batch is accepted with probability at most `(q + ℓ)/2^128`. -/
theorem secp256k1_batch_indexed_sound {M : Type} [DecidableEq M]
    (challenge : F → F → M → ZMod n) [UniformAnswerMeasure (IndexSpec n F M 128)]
    (hord : PrimeOrder n Point) (adv : OracleComp (IndexSpec n F M 128) (List (Entry n F M)))
    (q ℓ : ℕ) (hq : IsTotalQueryBound adv q) (hℓ : ∀ L ∈ support adv, L.length ≤ ℓ) :
    Pr{let z ← (simulateQ (IndexSpec n F M 128).cachingOracle
      (batchGame 128 indexKey adv)).run ∅}[Wins secp256k1 challenge z.1] ≤
        ((q + ℓ : ℕ) : ℝ≥0∞) / (2 ^ 128 : ℕ) :=
  batch_indexed_sound secp256k1 challenge 128 hord two_pow_128_le_n adv q ℓ hq hℓ

end Secp256k1

end Taproot.BIP340Batch
