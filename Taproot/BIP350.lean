import Mathlib

/-!
# BIP350: Bech32m

Bech32 (BIP173) and Bech32m (BIP350) addresses end in a 6-character checksum
computed by `polymod`, a BCH code over 5-bit symbols. The two variants differ
only in the constant the checksum is compared against: `1` for Bech32,
`0x2bc830a3` for Bech32m. Segwit v0 addresses use Bech32, v1+ (Taproot) use
Bech32m.

We implement the BIP's reference algorithms and prove:

* `verify_createChecksum`: checksums made by the encoder always verify.
* `not_both_valid`: no string is valid under both encodings.
* `substitution_detected`: changing any one data/checksum symbol is detected.
* `bech32_q_mutation`: the Bech32 weakness that motivated BIP350. If a valid
  Bech32 string ends in `p`, inserting or deleting any number of `q`s just
  before that `p` keeps it valid.
* `bech32m_q_mutation_detected`: Bech32m detects that mutation, for every final
  character and every number (1 to 89) of inserted or deleted `q`s; and
  `bech32_q_mutation_detected_iff`: Bech32 detects it exactly when the final
  character is not `p`.

`Taproot.BIP350Vectors` checks the BIP's official test vectors against this
implementation.
-/

namespace Bech32

/-! ## The checksum -/

/-- The two checksum variants. -/
inductive Encoding
  | bech32
  | bech32m
deriving DecidableEq, Repr

/-- The constant the checksum must equal. -/
def Encoding.const : Encoding → BitVec 32
  | .bech32 => 1
  | .bech32m => 0x2bc830a3

/-- The generator terms selected by the top 5 bits `b` of the checksum state. -/
def gen (b : BitVec 32) : BitVec 32 :=
  (if b.getLsbD 0 then 0x3b6a57b2 else 0) ^^^ (if b.getLsbD 1 then 0x26508e6d else 0) ^^^
  (if b.getLsbD 2 then 0x1ea119fa else 0) ^^^ (if b.getLsbD 3 then 0x3d4233dd else 0) ^^^
  (if b.getLsbD 4 then 0x2a1462b3 else 0)

/-- The input-independent part of one `polymod` step (multiplication by `x`
modulo the generator polynomial). -/
def shift (c : BitVec 32) : BitVec 32 :=
  ((c &&& 0x1ffffff) <<< 5) ^^^ gen (c >>> 25)

/-- One step of `bech32_polymod`:
`b = chk >> 25; chk = (chk & 0x1ffffff) << 5 ^ v; chk ^= GEN[i] for each set bit i of b`. -/
def step (c : BitVec 32) (v : ℕ) : BitVec 32 :=
  shift c ^^^ BitVec.ofNat 32 v

/-- `polymod` started from state `c`. -/
def polymodFrom (c : BitVec 32) (vs : List ℕ) : BitVec 32 :=
  vs.foldl step c

/-- `bech32_polymod`. -/
def polymod (vs : List ℕ) : BitVec 32 :=
  polymodFrom 1 vs

/-- `bech32_hrp_expand`: high bits of each character, a 0, then the low bits. -/
def hrpExpand (hrp : List Char) : List ℕ :=
  hrp.map (fun c => c.toNat >>> 5) ++ [0] ++ hrp.map (fun c => c.toNat &&& 31)

/-- `bech32_verify_checksum`, for a given encoding. -/
def verifyChecksum (enc : Encoding) (hrp : List Char) (data : List ℕ) : Bool :=
  polymod (hrpExpand hrp ++ data) == enc.const

/-- The six 5-bit chunks of a 30-bit value, most significant first. -/
def chunks (p : BitVec 32) : List ℕ :=
  [25, 20, 15, 10, 5, 0].map fun k => ((p >>> k) &&& 31).toNat

/-- `bech32_create_checksum`. -/
def createChecksum (enc : Encoding) (hrp : List Char) (data : List ℕ) : List ℕ :=
  chunks (polymod (hrpExpand hrp ++ data ++ [0, 0, 0, 0, 0, 0]) ^^^ enc.const)

/-! ## Bit-level facts about one step

Everything below is proven from `BitVec`/`Nat` lemmas and small kernel
computations; no SAT solver or native code is involved. -/

instance : Std.Associative (α := BitVec 32) (· ^^^ ·) := ⟨BitVec.xor_assoc⟩
instance : Std.Commutative (α := BitVec 32) (· ^^^ ·) := ⟨BitVec.xor_comm⟩

theorem xor0 (a : BitVec 32) : a ^^^ 0 = a := BitVec.xor_zero
theorem zeroXor (a : BitVec 32) : 0 ^^^ a = a := BitVec.zero_xor
theorem xorSelf (a : BitVec 32) : a ^^^ a = 0 := BitVec.xor_self
theorem toNat_zero32 : (0 : BitVec 32).toNat = 0 := rfl
theorem xor_cancel (a b : BitVec 32) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, xorSelf, zeroXor]
theorem xor_cancel_right (a b : BitVec 32) : a ^^^ b ^^^ b = a := by
  rw [BitVec.xor_assoc, xorSelf, xor0]
theorem xor_eq_iff (a v c : BitVec 32) : a ^^^ v = c ↔ a = c ^^^ v := by
  constructor
  · intro h; rw [← h, xor_cancel_right]
  · intro h; rw [h, xor_cancel_right]
theorem xor_xor_cancel (a b v : BitVec 32) : a ^^^ v ^^^ (b ^^^ v) = a ^^^ b := by
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc v, BitVec.xor_comm v b, BitVec.xor_assoc, xorSelf, xor0]
theorem xor_xor_cancel_left (a v w : BitVec 32) : a ^^^ v ^^^ (a ^^^ w) = v ^^^ w := by
  rw [BitVec.xor_comm a v, BitVec.xor_assoc, xor_cancel]

theorem ite_xor_bool (p q : Bool) (G : BitVec 32) :
    (if (p ^^ q) = true then G else 0) =
      (if p = true then G else 0) ^^^ (if q = true then G else 0) := by
  cases p <;> cases q <;> simp

theorem gen_xor (a b : BitVec 32) : gen (a ^^^ b) = gen a ^^^ gen b := by
  simp only [gen, BitVec.getLsbD_xor, ite_xor_bool]
  ac_rfl

theorem gen_zero : gen 0 = 0 := by decide

theorem and_xor_distrib (a b c : BitVec 32) : (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_xor, Bool.and_xor_distrib_right]

theorem shift_xor (a b : BitVec 32) : shift (a ^^^ b) = shift a ^^^ shift b := by
  unfold shift
  rw [and_xor_distrib, BitVec.shiftLeft_xor_distrib, BitVec.ushiftRight_xor_distrib,
    gen_xor]
  ac_rfl

theorem shift_zero : shift 0 = 0 := by decide

/-- `x >>> k = 0` says `x < 2^k`. -/
theorem ushr_eq_zero_iff (x : BitVec 32) (k : ℕ) : x >>> k = 0 ↔ x.toNat < 2 ^ k := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_zero32,
    Nat.div_eq_zero_iff]
  have := Nat.two_pow_pos k
  omega

theorem gen_lt (b : BitVec 32) : (gen b).toNat < 2 ^ 30 := by
  have h (p : Bool) (G : BitVec 32) (hG : G.toNat < 2 ^ 30) :
      (if p = true then G else 0).toNat < 2 ^ 30 := by
    split
    · exact hG
    · simp
  simp only [gen, BitVec.toNat_xor]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (h _ _ (by decide)) (h _ _ (by decide))) (h _ _ (by decide))) (h _ _ (by decide)))
    (h _ _ (by decide))

theorem toNat_and_mask (c : BitVec 32) : (c &&& 0x1ffffff).toNat = c.toNat % 2 ^ 25 := by
  rw [BitVec.toNat_and, show (0x1ffffff : BitVec 32).toNat = 2 ^ 25 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_masked_shift (c : BitVec 32) :
    ((c &&& 0x1ffffff) <<< 5).toNat = c.toNat % 2 ^ 25 * 32 := by
  rw [BitVec.toNat_shiftLeft, toNat_and_mask, Nat.shiftLeft_eq]
  have := Nat.mod_lt c.toNat (show 0 < 2 ^ 25 by decide)
  apply Nat.mod_eq_of_lt
  omega

/-- The state always stays below `2^30`. -/
theorem shift_lt (c : BitVec 32) : shift c >>> 30 = 0 := by
  rw [ushr_eq_zero_iff, shift, BitVec.toNat_xor, toNat_masked_shift]
  have := Nat.mod_lt c.toNat (show 0 < 2 ^ 25 by decide)
  exact Nat.xor_lt_two_pow (by omega) (gen_lt _)

/-- For small values `shift` is a plain left shift by 5. -/
theorem shift_small {c : BitVec 32} (hc : c >>> 25 = 0) : shift c = c <<< 5 := by
  have hlt := (ushr_eq_zero_iff c 25).mp hc
  have hmask : c &&& 0x1ffffff = c := by
    rw [← BitVec.toNat_inj, toNat_and_mask, Nat.mod_eq_of_lt hlt]
  rw [shift, hc, hmask, gen_zero, xor0]

/-- Kernel check: the low 5 bits of `gen t` vanish only for `t = 0`. -/
theorem gen_low_bits : ∀ m < 32, (gen (BitVec.ofNat 32 m)).toNat % 32 = 0 → m = 0 := by
  decide

/-- `shift` is injective on 30-bit states (the generator polynomial has a
nonzero constant term). -/
theorem shift_eq_zero {c : BitVec 32} (hc : c >>> 30 = 0) (h : shift c = 0) : c = 0 := by
  have hc' := (ushr_eq_zero_iff c 30).mp hc
  set t := c >>> 25 with ht_def
  have ht : t.toNat = c.toNat / 2 ^ 25 := by
    rw [ht_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  -- `(c mod 2^25)·32 = gen t`, so `gen t` has zero low bits, so `t = 0`.
  have heq : (c &&& 0x1ffffff) <<< 5 = gen t := BitVec.xor_eq_zero_iff.mp h
  have hnat := congrArg BitVec.toNat heq
  rw [toNat_masked_shift] at hnat
  have ht0 : t.toNat = 0 := by
    apply gen_low_bits t.toNat (by rw [ht]; omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hnat]
    omega
  have : t = 0 := by rw [← BitVec.toNat_inj]; simpa using ht0
  rw [this, gen_zero, toNat_zero32] at hnat
  rw [← BitVec.toNat_inj, toNat_zero32]
  omega

/-- Appending a 5-bit value to a value shifted left by 5 is addition. -/
theorem nat_xor_eq_add (a : ℕ) {v : ℕ} (hv : v < 32) : (a * 2 ^ 5) ^^^ v = a * 2 ^ 5 + v := by
  have hdisj (i : ℕ) : ((a * 2 ^ 5).testBit i && v.testBit i) = false := by
    by_cases hi : i < 5
    · rw [Nat.testBit_mul_two_pow]; simp [hi]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
        (Nat.pow_le_pow_right (n := 2) (by decide) (show 5 ≤ i by omega)))]
      simp
  rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt (by omega) a, Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_or]
  have := hdisj i
  cases h1 : (a * 2 ^ 5).testBit i <;> cases h2 : v.testBit i <;> simp_all

/-- Feeding a small symbol into a small state: `y·32 + v`. -/
theorem toNat_step_small {y : BitVec 32} {v : ℕ} (hy : y.toNat < 2 ^ 25) (hv : v < 32) :
    (step y v).toNat = y.toNat * 32 + v := by
  have hy' : y >>> 25 = 0 := (ushr_eq_zero_iff y 25).mpr hy
  rw [step, shift_small hy', BitVec.toNat_xor, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : y.toNat * 2 ^ 5 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : v < 2 ^ 32), nat_xor_eq_add _ hv]
  omega

/-- Feeding six chunks of a 30-bit value `q` into a zero state gives `q` back. -/
theorem polymodFrom_zero_chunks {q : BitVec 32} (hq : q >>> 30 = 0) :
    polymodFrom 0 (chunks q) = q := by
  have hq' := (ushr_eq_zero_iff q 30).mp hq
  have hc (k : ℕ) : ((q >>> k) &&& 31).toNat = q.toNat / 2 ^ k % 32 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show (31 : BitVec 32).toNat = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  simp only [polymodFrom, chunks, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, hc]
  rw [← BitVec.toNat_inj]
  have h0 := toNat_zero32
  -- Each step appends one 5-bit chunk: the state is `q / 2^(25-5j)` after `j+1` steps.
  have s1 := toNat_step_small (y := 0) (v := q.toNat / 2 ^ 25 % 32) (by simp)
    (Nat.mod_lt _ (by decide))
  rw [h0] at s1
  have s2 := toNat_step_small (v := q.toNat / 2 ^ 20 % 32) (by omega) (Nat.mod_lt _ (by decide))
    (y := step 0 (q.toNat / 2 ^ 25 % 32))
  rw [s1] at s2
  have s3 := toNat_step_small (v := q.toNat / 2 ^ 15 % 32) (by omega) (Nat.mod_lt _ (by decide))
    (y := step (step 0 (q.toNat / 2 ^ 25 % 32)) (q.toNat / 2 ^ 20 % 32))
  rw [s2] at s3
  have s4 := toNat_step_small (v := q.toNat / 2 ^ 10 % 32) (by omega) (Nat.mod_lt _ (by decide))
    (y := step (step (step 0 (q.toNat / 2 ^ 25 % 32)) (q.toNat / 2 ^ 20 % 32))
      (q.toNat / 2 ^ 15 % 32))
  rw [s3] at s4
  have s5 := toNat_step_small (v := q.toNat / 2 ^ 5 % 32) (by omega) (Nat.mod_lt _ (by decide))
    (y := step (step (step (step 0 (q.toNat / 2 ^ 25 % 32)) (q.toNat / 2 ^ 20 % 32))
      (q.toNat / 2 ^ 15 % 32)) (q.toNat / 2 ^ 10 % 32))
  rw [s4] at s5
  have s6 := toNat_step_small (v := q.toNat / 2 ^ 0 % 32) (by omega) (Nat.mod_lt _ (by decide))
    (y := step (step (step (step (step 0 (q.toNat / 2 ^ 25 % 32)) (q.toNat / 2 ^ 20 % 32))
      (q.toNat / 2 ^ 15 % 32)) (q.toNat / 2 ^ 10 % 32)) (q.toNat / 2 ^ 5 % 32))
  rw [s5] at s6
  rw [s6]
  omega

/-! ## Linearity -/

theorem iterate_shift_xor (k : ℕ) (a b : BitVec 32) :
    shift^[k] (a ^^^ b) = shift^[k] a ^^^ shift^[k] b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ', Function.comp, ih, shift_xor]

theorem iterate_shift_zero (k : ℕ) : shift^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ', Function.comp, ih, shift_zero]

theorem iterate_shift_eq_zero {k : ℕ} {c : BitVec 32} (hc : c >>> 30 = 0)
    (h : shift^[k] c = 0) : c = 0 := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ, Function.comp] at h
    exact shift_eq_zero hc (ih (shift_lt c) h)

/-- Two runs over the same symbols differ by the shifted difference of their start states. -/
theorem polymodFrom_xor (s s' : BitVec 32) (vs : List ℕ) :
    polymodFrom s vs ^^^ polymodFrom s' vs = shift^[vs.length] (s ^^^ s') := by
  induction vs generalizing s s' with
  | nil => rfl
  | cons v vs ih =>
    simp only [polymodFrom, List.foldl_cons] at ih ⊢
    rw [ih, List.length_cons, Function.iterate_succ, Function.comp, step, step]
    congr 1
    rw [shift_xor, xor_xor_cancel]

theorem polymodFrom_append (s : BitVec 32) (us vs : List ℕ) :
    polymodFrom s (us ++ vs) = polymodFrom (polymodFrom s us) vs := by
  simp [polymodFrom, List.foldl_append]

theorem polymodFrom_zeros (s : BitVec 32) (k : ℕ) :
    polymodFrom s (List.replicate k 0) = shift^[k] s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, polymodFrom, List.foldl_cons, ← polymodFrom, ih, step,
      Function.iterate_succ_apply]
    simp only [BitVec.xor_zero]

/-! ## Checksums made by the encoder verify -/

/-- **Encoder correctness**: appending `createChecksum` makes the checksum valid. -/
theorem verify_createChecksum (enc : Encoding) (hrp : List Char) (data : List ℕ) :
    verifyChecksum enc hrp (data ++ createChecksum enc hrp data) = true := by
  set x := polymod (hrpExpand hrp ++ data)
  have hzeros : polymod (hrpExpand hrp ++ data ++ [0, 0, 0, 0, 0, 0]) = shift^[6] x := by
    rw [polymod, polymodFrom_append, ← polymod,
      show [0, 0, 0, 0, 0, 0] = List.replicate 6 0 from rfl, polymodFrom_zeros]
  -- The new state is `shift⁶ x` xor the chunks fed in, which reassemble to `shift⁶ x ^ const`.
  have hq : (shift^[6] x ^^^ enc.const) >>> 30 = 0 := by
    have : shift^[6] x >>> 30 = 0 := by
      rw [Function.iterate_succ', Function.comp]; exact shift_lt _
    rw [ushr_eq_zero_iff] at this ⊢
    rw [BitVec.toNat_xor]
    exact Nat.xor_lt_two_pow this (by cases enc <;> decide)
  have hlen : (createChecksum enc hrp data).length = 6 := by simp [createChecksum, chunks]
  have hc : polymodFrom 0 (createChecksum enc hrp data) = shift^[6] x ^^^ enc.const := by
    rw [createChecksum, hzeros, polymodFrom_zero_chunks hq]
  have key := polymodFrom_xor x 0 (createChecksum enc hrp data)
  rw [hlen, hc] at key
  rw [verifyChecksum, ← List.append_assoc, polymod, polymodFrom_append, ← polymod, beq_iff_eq]
  -- key : A ^ (B ^ C) = shift⁶ (x ^ 0) = B, hence A = C.
  rw [xor0] at key
  -- key : A ^ (B ^ C) = B, hence A = C.
  calc polymodFrom x (createChecksum enc hrp data)
      = polymodFrom x (createChecksum enc hrp data) ^^^ (shift^[6] x ^^^ enc.const) ^^^
          (shift^[6] x ^^^ enc.const) := (xor_cancel_right _ _).symm
    _ = enc.const := by rw [key, xor_cancel]

/-- **No ambiguity**: a checksum cannot be valid for both Bech32 and Bech32m. -/
theorem not_both_valid (hrp : List Char) (data : List ℕ) :
    ¬ (verifyChecksum .bech32 hrp data = true ∧ verifyChecksum .bech32m hrp data = true) := by
  rintro ⟨h1, h2⟩
  simp only [verifyChecksum, beq_iff_eq] at h1 h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ## Error detection -/

theorem ofNat_xor_ne_zero {a b : ℕ} (ha : a < 32) (hb : b < 32) (hab : a ≠ b) :
    BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp h)
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem ofNat_xor_lt {a b : ℕ} (ha : a < 32) (hb : b < 32) :
    (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b) >>> 30 = 0 := by
  rw [ushr_eq_zero_iff, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact Nat.xor_lt_two_pow (n := 30) (by omega) (by omega)

/-- **Substitution errors are detected**: changing any single symbol (to a
different 5-bit value) changes the checksum state. -/
theorem substitution_detected (s : BitVec 32) (pre suf : List ℕ) {a b : ℕ}
    (ha : a < 32) (hb : b < 32) (hab : a ≠ b) :
    polymodFrom s (pre ++ a :: suf) ≠ polymodFrom s (pre ++ b :: suf) := by
  intro h
  rw [polymodFrom_append, polymodFrom_append] at h
  change polymodFrom (step (polymodFrom s pre) a) suf =
    polymodFrom (step (polymodFrom s pre) b) suf at h
  have key := polymodFrom_xor (step (polymodFrom s pre) a) (step (polymodFrom s pre) b) suf
  have hdiff : step (polymodFrom s pre) a ^^^ step (polymodFrom s pre) b =
      BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b := by
    unfold step; exact xor_xor_cancel_left _ _ _
  rw [h, xorSelf, hdiff] at key
  exact ofNat_xor_ne_zero ha hb hab
    (iterate_shift_eq_zero (ofNat_xor_lt ha hb) key.symm)

/-- Substitution detection for address checksums: if a string is valid,
changing one data or checksum character to another makes it invalid. -/
theorem verifyChecksum_substitution (enc : Encoding) (hrp : List Char) (d₁ d₂ : List ℕ) {a b : ℕ}
    (ha : a < 32) (hb : b < 32) (hab : a ≠ b)
    (hvalid : verifyChecksum enc hrp (d₁ ++ a :: d₂) = true) :
    verifyChecksum enc hrp (d₁ ++ b :: d₂) = false := by
  simp only [verifyChecksum, beq_iff_eq, beq_eq_false_iff_ne, polymod] at hvalid ⊢
  rw [← List.append_assoc] at hvalid ⊢
  rw [← hvalid]
  exact (substitution_detected 1 _ d₂ ha hb hab).symm

/-! ## The `q`-insertion mutation (the reason for BIP350)

`q` is the symbol 0 and `p` the symbol 1. We look at a valid string whose data
ends in symbol `v`, and insert (or delete) `k` copies of `q` right before it. -/

/-- After inserting `k` zeros before the final symbol, the state is `shiftᵏ` of
the shifted original state, xor `v`. -/
theorem polymodFrom_insert (s : BitVec 32) (pre : List ℕ) (k v : ℕ) :
    polymodFrom s (pre ++ List.replicate k 0 ++ [v]) =
      shift^[k] (shift (polymodFrom s pre)) ^^^ BitVec.ofNat 32 v := by
  rw [polymodFrom_append, polymodFrom_append, polymodFrom_zeros, polymodFrom, List.foldl_cons,
    List.foldl_nil, step, ← Function.iterate_succ_apply' shift, Function.iterate_succ_apply]

/-- The mutation question reduces to whether `const ^ v` is a fixed point of `shiftᵏ`. -/
theorem insert_valid_iff (enc : Encoding) (s : BitVec 32) (pre : List ℕ) (k v : ℕ)
    (hvalid : polymodFrom s (pre ++ [v]) = enc.const) :
    polymodFrom s (pre ++ List.replicate k 0 ++ [v]) = enc.const ↔
      shift^[k] (enc.const ^^^ BitVec.ofNat 32 v) = enc.const ^^^ BitVec.ofNat 32 v := by
  have h0 := polymodFrom_insert s pre 0 v
  simp only [List.replicate_zero, List.append_nil, Function.iterate_zero, id] at h0
  rw [h0] at hvalid
  have hx : shift (polymodFrom s pre) = enc.const ^^^ BitVec.ofNat 32 v := by
    rw [← hvalid, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [polymodFrom_insert, hx]
  exact xor_eq_iff _ _ _

/-- Deleting `k` zeros before the final symbol: the same fixed-point condition. -/
theorem delete_valid_imp (enc : Encoding) (s : BitVec 32) (pre : List ℕ) (k v : ℕ)
    (hvalid : polymodFrom s (pre ++ List.replicate k 0 ++ [v]) = enc.const)
    (hdel : polymodFrom s (pre ++ [v]) = enc.const) :
    shift^[k] (enc.const ^^^ BitVec.ofNat 32 v) = enc.const ^^^ BitVec.ofNat 32 v :=
  (insert_valid_iff enc s pre k v hdel).mp hvalid

/-- **The Bech32 weakness**: in a valid Bech32 string ending in `p`, any
number of `q`s can be inserted before the final `p`, and any run of `q`s
there can be deleted, without invalidating the checksum. -/
theorem bech32_q_mutation (hrp : List Char) (d : List ℕ) (k : ℕ) :
    verifyChecksum .bech32 hrp (d ++ [1]) = true ↔
      verifyChecksum .bech32 hrp (d ++ List.replicate k 0 ++ [1]) = true := by
  simp only [verifyChecksum, beq_iff_eq, polymod, ← List.append_assoc]
  -- `const ^ p = 1 ^ 1 = 0`, a fixed point of every `shiftᵏ`.
  have hfix : shift^[k] (Encoding.bech32.const ^^^ BitVec.ofNat 32 1) =
      Encoding.bech32.const ^^^ BitVec.ofNat 32 1 := by
    simp only [Encoding.const]
    exact iterate_shift_zero k
  constructor
  · intro h; exact (insert_valid_iff .bech32 1 _ k 1 h).mpr hfix
  · intro h
    have hx := polymodFrom_insert 1 (hrpExpand hrp ++ d) k 1
    rw [h] at hx
    -- `shiftᵏ⁺¹ x = 0` forces `x = 0`, so the shorter string is valid too.
    have hz : shift^[k] (shift (polymodFrom 1 (hrpExpand hrp ++ d))) = 0 := by
      have := congrArg (· ^^^ BitVec.ofNat 32 1) hx
      simpa [Encoding.const, BitVec.xor_assoc] using this.symm
    have h1 := iterate_shift_eq_zero (shift_lt _) hz
    have h0 := polymodFrom_insert 1 (hrpExpand hrp ++ d) 0 1
    simp only [List.replicate_zero, List.append_nil, Function.iterate_zero, id] at h0
    rw [h0, h1]; rfl

/-- Check that `shiftᵏ x ≠ x` for `k = 1 … K`. -/
def noFixedPoint (x : BitVec 32) : ℕ → BitVec 32 → Bool
  | 0, _ => true
  | K + 1, y => shift y != x && noFixedPoint x K (shift y)

theorem noFixedPoint_spec {x : BitVec 32} {K : ℕ} {y : BitVec 32} (h : noFixedPoint x K y = true)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ K) : shift^[k] y ≠ x := by
  induction K generalizing y k with
  | zero => omega
  | succ K ih =>
    simp only [noFixedPoint, Bool.and_eq_true, bne_iff_ne] at h
    obtain ⟨h1, h2⟩ := h
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · simpa using h1
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      exact ih h2 (by omega) (by omega)

/-- Kernel computation: for Bech32m, `const ^ v` is not a fixed point of
`shiftᵏ` for any final symbol `v` and any `k` from 1 to 89. -/
theorem bech32m_no_fixed_points :
    (List.range 32).all (fun v =>
      noFixedPoint (Encoding.bech32m.const ^^^ BitVec.ofNat 32 v) 89
        (Encoding.bech32m.const ^^^ BitVec.ofNat 32 v)) = true := by
  decide +kernel

/-- Kernel computation: for Bech32, the only final symbol with a fixed point is `p` (= 1). -/
theorem bech32_no_fixed_points_except_p :
    ((List.range 32).filter (· ≠ 1)).all (fun v =>
      noFixedPoint (Encoding.bech32.const ^^^ BitVec.ofNat 32 v) 89
        (Encoding.bech32.const ^^^ BitVec.ofNat 32 v)) = true := by
  decide +kernel

/-- **Bech32m fixes the weakness**: in a valid Bech32m string, inserting
between 1 and 89 `q`s before the final character (whatever it is) always
invalidates the checksum. (Strings are at most 90 characters.) -/
theorem bech32m_q_insertion_detected (hrp : List Char) (d : List ℕ) {v k : ℕ}
    (hv : v < 32) (hk1 : 1 ≤ k) (hk : k ≤ 89)
    (hvalid : verifyChecksum .bech32m hrp (d ++ [v]) = true) :
    verifyChecksum .bech32m hrp (d ++ List.replicate k 0 ++ [v]) = false := by
  simp only [verifyChecksum, beq_iff_eq, beq_eq_false_iff_ne, polymod, ← List.append_assoc]
    at hvalid ⊢
  rw [ne_eq, insert_valid_iff .bech32m 1 _ k v hvalid]
  have := bech32m_no_fixed_points
  rw [List.all_eq_true] at this
  exact noFixedPoint_spec (this v (List.mem_range.mpr hv)) hk1 hk

/-- **Bech32m fixes the weakness (deletion)**: deleting between 1 and 89 `q`s
before the final character of a valid Bech32m string always invalidates it. -/
theorem bech32m_q_deletion_detected (hrp : List Char) (d : List ℕ) {v k : ℕ}
    (hv : v < 32) (hk1 : 1 ≤ k) (hk : k ≤ 89)
    (hvalid : verifyChecksum .bech32m hrp (d ++ List.replicate k 0 ++ [v]) = true) :
    verifyChecksum .bech32m hrp (d ++ [v]) = false := by
  simp only [verifyChecksum, beq_iff_eq, beq_eq_false_iff_ne, polymod, ← List.append_assoc]
    at hvalid ⊢
  intro hdel
  have := bech32m_no_fixed_points
  rw [List.all_eq_true] at this
  exact noFixedPoint_spec (this v (List.mem_range.mpr hv)) hk1 hk
    (delete_valid_imp .bech32m 1 _ k v hvalid hdel)

/-- **Exactly the `p` case**: for Bech32, inserting 1 to 89 `q`s before the
final character of a valid string goes undetected if and only if that
character is `p`. -/
theorem bech32_q_insertion_undetected_iff (hrp : List Char) (d : List ℕ) {v k : ℕ}
    (hv : v < 32) (hk1 : 1 ≤ k) (hk : k ≤ 89)
    (hvalid : verifyChecksum .bech32 hrp (d ++ [v]) = true) :
    verifyChecksum .bech32 hrp (d ++ List.replicate k 0 ++ [v]) = true ↔ v = 1 := by
  constructor
  · intro h
    by_contra hv1
    simp only [verifyChecksum, beq_iff_eq, polymod, ← List.append_assoc] at hvalid h
    rw [insert_valid_iff .bech32 1 _ k v hvalid] at h
    have := bech32_no_fixed_points_except_p
    rw [List.all_eq_true] at this
    exact noFixedPoint_spec (this v (List.mem_filter.mpr ⟨List.mem_range.mpr hv, by simpa⟩))
      hk1 hk h
  · rintro rfl
    exact (bech32_q_mutation hrp d k).mp hvalid

end Bech32
