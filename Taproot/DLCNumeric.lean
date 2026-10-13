import Taproot.DLC

/-!
# DLCs on numeric outcomes

For numeric outcomes (prices, scores, …) the DLC specification has the oracle
attest each base-`b` digit of the outcome separately, with one pre-committed
nonce per digit. Instead of one CET per outcome, the parties make one CET per
*digit prefix*: a CET for prefix `v` (of length `k`) is locked to the sum of
the anticipation points of those `k` digits, and covers every outcome whose
first `k` digits are `v`. An interval of outcomes with the same payout is
split into few prefixes ("CET compression").

We prove:
* `decomp_spec`, `decomp_unique`: the prefix decomposition of an interval
  `[lo, hi)` covers **exactly** the outcomes in the interval, each by
  **exactly one** prefix (so every outcome has one CET, never two).
* `mulG_attestation_sum`: the oracle's digit attestations for outcome `x`
  sum to the discrete log of the CET point of every prefix of `x`.
* `numeric_settle`: hence for every outcome in the interval, the attestation
  completes the adaptor signature of the one CET covering it.
-/

namespace Taproot.DLC.Numeric

open Curve BIP340

section Decomposition

variable (b nd : ℕ)

/-- Digit `i` (most significant first) of `x` written with `k` base-`b` digits. -/
def digit (k x i : ℕ) : ℕ := x / b ^ (k - 1 - i) % b

/-- The prefix `blk = (v, k)` (value `v`, `k` digits) covers the `nd`-digit
outcome `x` when the first `k` digits of `x` are `v`. -/
def covers (blk : ℕ × ℕ) (x : ℕ) : Prop := x / b ^ (nd - blk.2) = blk.1

/-- If the prefix `(v, k)` covers `x`, its digits are the first `k` digits of `x`. -/
theorem digit_of_covers {v k x i : ℕ} (hk : k ≤ nd) (hi : i < k) (h : covers b nd (v, k) x) :
    digit b k v i = digit b nd x i := by
  unfold covers at h
  dsimp only at h
  unfold digit
  rw [← h, Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  omega

/-- The largest aligned block `[lo, lo + bʲ)` (with `j ≤ nd`) that fits in `[lo, hi)`. -/
def bestExp (lo hi : ℕ) : ℕ :=
  Nat.findGreatest (fun j => b ^ j ∣ lo ∧ lo + b ^ j ≤ hi ∧ 0 < b ^ j) nd

theorem bestExp_spec {lo hi : ℕ} (h : lo < hi) :
    b ^ bestExp b nd lo hi ∣ lo ∧ lo + b ^ bestExp b nd lo hi ≤ hi ∧
      0 < b ^ bestExp b nd lo hi :=
  Nat.findGreatest_spec (P := fun j => b ^ j ∣ lo ∧ lo + b ^ j ≤ hi ∧ 0 < b ^ j)
    (Nat.zero_le nd) ⟨by simp, by simp; omega, by simp⟩

theorem bestExp_le (lo hi : ℕ) : bestExp b nd lo hi ≤ nd := Nat.findGreatest_le nd

/-- Split `[lo, hi)` into prefixes, greedily taking the largest aligned block. -/
def decomp (lo hi : ℕ) : List (ℕ × ℕ) :=
  if lo < hi then
    (lo / b ^ bestExp b nd lo hi, nd - bestExp b nd lo hi) ::
      decomp (lo + b ^ bestExp b nd lo hi) hi
  else []
termination_by hi - lo
decreasing_by have := (bestExp_spec b nd ‹lo < hi›).2.2; omega

theorem div_eq_iff' {x q k : ℕ} (hk : 0 < k) : x / k = q ↔ q * k ≤ x ∧ x < (q + 1) * k := by
  rw [← Nat.le_div_iff_mul_le hk, ← Nat.div_lt_iff_lt_mul hk]
  omega

/-- The first block covers exactly `[lo, lo + bʲ)`. -/
theorem covers_head {lo hi x : ℕ} (h : lo < hi) :
    covers b nd (lo / b ^ bestExp b nd lo hi, nd - bestExp b nd lo hi) x ↔
      lo ≤ x ∧ x < lo + b ^ bestExp b nd lo hi := by
  have hdvd := (bestExp_spec b nd h).1
  have hle := bestExp_le b nd lo hi
  unfold covers
  rw [show nd - (nd - bestExp b nd lo hi) = bestExp b nd lo hi by omega,
    div_eq_iff' (bestExp_spec b nd h).2.2, add_mul, one_mul, Nat.div_mul_cancel hdvd]

/-- **Exact cover**: an outcome is covered by some prefix of the decomposition
iff it lies in `[lo, hi)`. -/
theorem decomp_spec (lo hi x : ℕ) :
    (∃ blk ∈ decomp b nd lo hi, covers b nd blk x) ↔ lo ≤ x ∧ x < hi := by
  induction hd : hi - lo using Nat.strong_induction_on generalizing lo with
  | _ d ih =>
    rw [decomp]
    split_ifs with h
    · obtain ⟨-, hfit, hpos⟩ := bestExp_spec b nd h
      rw [List.exists_mem_cons_iff, covers_head b nd h, ih _ (by omega) _ rfl]
      omega
    · simp only [List.not_mem_nil, false_and, exists_false, false_iff]
      omega

/-- **No overlaps**: an outcome is covered by at most one prefix of the decomposition. -/
theorem decomp_unique {lo hi x : ℕ} {blk₁ blk₂ : ℕ × ℕ}
    (h₁ : blk₁ ∈ decomp b nd lo hi) (h₂ : blk₂ ∈ decomp b nd lo hi)
    (hc₁ : covers b nd blk₁ x) (hc₂ : covers b nd blk₂ x) : blk₁ = blk₂ := by
  induction hd : hi - lo using Nat.strong_induction_on generalizing lo with
  | _ d ih =>
    rw [decomp] at h₁ h₂
    split_ifs at h₁ h₂ with h
    · obtain ⟨-, hfit, hpos⟩ := bestExp_spec b nd h
      -- Blocks after the first only cover outcomes `≥ lo + bʲ`.
      have hrest {blk : ℕ × ℕ} (hm : blk ∈ decomp b nd (lo + b ^ bestExp b nd lo hi) hi)
          (hc : covers b nd blk x) : lo + b ^ bestExp b nd lo hi ≤ x :=
        ((decomp_spec b nd _ hi x).mp ⟨blk, hm, hc⟩).1
      rcases List.mem_cons.mp h₁ with rfl | h₁ <;> rcases List.mem_cons.mp h₂ with rfl | h₂
      · rfl
      · have := ((covers_head b nd h).mp hc₁).2; have := hrest h₂ hc₂; omega
      · have := ((covers_head b nd h).mp hc₂).2; have := hrest h₁ hc₁; omega
      · exact ih (hi - (lo + b ^ bestExp b nd lo hi)) (by omega) h₁ h₂ rfl
    · simp at h₁

/-- Every prefix has at most `nd` digits. -/
theorem decomp_len_le {lo hi : ℕ} {blk : ℕ × ℕ} (h : blk ∈ decomp b nd lo hi) : blk.2 ≤ nd := by
  induction hd : hi - lo using Nat.strong_induction_on generalizing lo with
  | _ d ih =>
    rw [decomp] at h
    split_ifs at h with hlt
    · rcases List.mem_cons.mp h with rfl | h
      · exact Nat.sub_le _ _
      · obtain ⟨-, hfit, hpos⟩ := bestExp_spec b nd hlt
        exact ih (hi - (lo + b ^ bestExp b nd lo hi)) (by omega) h rfl
    · simp at h

end Decomposition

/-! ## Attestations unlock the CET of the outcome's prefix -/

variable {n : ℕ} [Fact n.Prime] {E X M : Type*} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  (C : Curve n E X) (challenge : X → X → M → ZMod n) (b nd : ℕ)

/-- The CET adaptor point for prefix `(v, k)`: the sum of the anticipation
points `Rᵢ + eᵢ·P` of its `k` digits, where digit `i` is attested with nonce
`rᵢ` (`Rᵢ = lift_x(rᵢ)`) and digit value `d` is signed as message `msg d`. -/
def cetPoint (P : E) (R : ℕ → E) (pk : X) (r : ℕ → X) (msg : ℕ → M) (blk : ℕ × ℕ) : E :=
  ∑ i ∈ Finset.range blk.2, (R i + (challenge (r i) pk (msg (digit b blk.2 blk.1 i))).val • P)

/-- **Digit attestations unlock prefix CETs**: if the oracle validly attests
every digit of outcome `x`, then for every prefix covering `x`, the sum of
the first `k` attestation scalars is the discrete log of the prefix's CET
point. -/
theorem mulG_attestation_sum {pk : X} {P : E} {r : ℕ → X} {R : ℕ → E} {msg : ℕ → M}
    (hP : C.liftX pk = some P) (hR : ∀ i, C.liftX (r i) = some (R i))
    {x : ℕ} {s : ℕ → ZMod n}
    (hatt : ∀ i < nd, verify C challenge pk (msg (digit b nd x i)) (r i, s i) = true)
    {blk : ℕ × ℕ} (hk : blk.2 ≤ nd) (hcov : covers b nd blk x) :
    C.mulG (∑ i ∈ Finset.range blk.2, s i) = cetPoint challenge b P R pk r msg blk := by
  obtain ⟨v, k⟩ := blk
  rw [map_sum, cetPoint]
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_range.mp hi
  have h := anticipate_of_verify C challenge (hatt i (by simp at hk; omega))
  simp only [anticipate, hP, hR i, Option.some.injEq] at h
  rw [← h, digit_of_covers b nd hk hi hcov]

/-- **Numeric DLC settlement**: for every outcome `x` in `[lo, hi)`, exactly
one prefix of the decomposition covers `x`, and completing any pre-signature
that passed pre-verification against that prefix's CET point with the sum of
the oracle's digit attestations gives a valid BIP340 signature. -/
theorem numeric_settle {pk : X} {P : E} {r : ℕ → X} {R : ℕ → E} {msg : ℕ → M}
    (hP : C.liftX pk = some P) (hR : ∀ i, C.liftX (r i) = some (R i))
    {lo hi x : ℕ} (hx : lo ≤ x ∧ x < hi) {s : ℕ → ZMod n}
    (hatt : ∀ i < nd, verify C challenge pk (msg (digit b nd x i)) (r i, s i) = true) :
    ∃ blk ∈ decomp b nd lo hi, covers b nd blk x ∧
      (∀ blk' ∈ decomp b nd lo hi, covers b nd blk' x → blk' = blk) ∧
      ∀ (pk' : X) (msg' : M) (ps : PreSig n E),
        preVerify C challenge pk' (cetPoint challenge b P R pk r msg blk) msg' ps = true →
        verify C challenge pk' msg' (adapt C ps (∑ i ∈ Finset.range blk.2, s i)) = true := by
  obtain ⟨blk, hmem, hcov⟩ := (decomp_spec b nd lo hi x).mpr hx
  refine ⟨blk, hmem, hcov, fun blk' hm hc => decomp_unique b nd hm hmem hc hcov, ?_⟩
  intro pk' msg' ps hpre
  exact verify_adapt C challenge hpre
    (mulG_attestation_sum C challenge b nd hP hR hatt (decomp_len_le b nd hmem) hcov)

end Taproot.DLC.Numeric
