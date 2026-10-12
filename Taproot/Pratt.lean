import Mathlib

/-!
# Pratt primality certificates

`Nat.Prime` cannot be decided by trial division for 256-bit numbers, so we
prove primality with Lucas' theorem (`lucas_primality` in Mathlib): `p` is
prime if some `a` has `a^(p-1) ≡ 1` but `a^((p-1)/q) ≢ 1 (mod p)` for every
prime `q ∣ p - 1`. Checking this needs the factorization of `p - 1`, whose
large factors are proven prime the same way (a Pratt certificate).

The modular exponentiations are checked by the kernel (`decide +kernel`),
using `powMod`, which is structurally recursive so the kernel can evaluate it.
-/

namespace Pratt

/-- Square-and-multiply `a ^ b % m`, structurally recursive on a fuel argument. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | fuel + 1, a, b, m =>
    if b = 0 then 1 % m else
    let r := powModAux fuel (a * a % m) (b / 2) m
    if b % 2 = 0 then r else a * r % m

/-- `a ^ b % m` for `b < 2 ^ 512`. -/
def powMod (a b m : ℕ) : ℕ := powModAux 512 a b m

theorem powModAux_eq (fuel : ℕ) : ∀ a b m, b < 2 ^ fuel → powModAux fuel a b m = a ^ b % m := by
  induction fuel with
  | zero => intro a b m hb; simp at hb; simp [powModAux, hb]
  | succ fuel ih =>
    intro a b m hb
    simp only [powModAux]
    split_ifs with h0 h2
    · simp [h0]
    · rw [ih _ _ _ (by omega), ← Nat.pow_mod, ← pow_two, ← pow_mul]
      congr 2; omega
    · rw [ih _ _ _ (by omega), ← Nat.pow_mod, Nat.mul_mod_mod, ← pow_two, ← pow_mul, ← pow_succ']
      congr 2; omega

theorem powMod_eq (a b m : ℕ) (hb : b < 2 ^ 512) : powMod a b m = a ^ b % m :=
  powModAux_eq 512 a b m hb

/-- The computational part of a Pratt certificate for `p` with witness `a` and
factorization `fs = [(q₁, e₁), …]` of `p - 1`, as a single Boolean check. -/
def check (p a : ℕ) (fs : List (ℕ × ℕ)) : Bool :=
  2 ≤ p && p < 2 ^ 512 &&
  (fs.map fun qe => qe.1 ^ qe.2).prod == p - 1 &&
  powMod a (p - 1) p == 1 &&
  fs.all fun qe => powMod a ((p - 1) / qe.1) p != 1

theorem prime_of_check (p a : ℕ) (fs : List (ℕ × ℕ))
    (hprimes : ∀ qe ∈ fs, qe.1.Prime) (hcheck : check p a fs = true) : p.Prime := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at hcheck
  obtain ⟨⟨⟨⟨hp2, hp⟩, hprod⟩, hferm⟩, hwit⟩ := hcheck
  -- `(a : ZMod p) ^ k` agrees with `powMod a k p` for the exponents we use.
  have cast_pow (k : ℕ) (hk : k ≤ p - 1) : ((a : ZMod p) ^ k) = ((powMod a k p : ℕ) : ZMod p) := by
    rw [powMod_eq _ _ _ (by omega), ZMod.natCast_mod, Nat.cast_pow]
  have lt_p (k : ℕ) (hk : k ≤ p - 1) : powMod a k p < p := by
    rw [powMod_eq _ _ _ (by omega)]; exact Nat.mod_lt _ (by omega)
  apply lucas_primality p a
  · rw [cast_pow _ le_rfl, hferm, Nat.cast_one]
  · intro q hq hdvd
    rw [← hprod, hq.prime.dvd_prod_iff] at hdvd
    obtain ⟨_, hmem, hqd⟩ := hdvd
    obtain ⟨qe, hqe, rfl⟩ := List.mem_map.mp hmem
    have hqeq : q = qe.1 :=
      (Nat.prime_dvd_prime_iff_eq hq (hprimes qe hqe)).mp (hq.dvd_of_dvd_pow hqd)
    subst hqeq
    have hle : (p - 1) / qe.1 ≤ p - 1 := Nat.div_le_self _ _
    rw [cast_pow _ hle]
    intro h
    have h' : ((powMod a ((p - 1) / qe.1) p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [h, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (lt_p _ hle),
      Nat.mod_eq_of_lt (by omega : 1 < p)] at h'
    exact hwit qe hqe h'

/-- Powers in `ZMod p` can be computed with `powMod`. -/
theorem natCast_pow_eq_powMod (a k p : ℕ) (hk : k < 2 ^ 512) :
    (a : ZMod p) ^ k = ((powMod a k p : ℕ) : ZMod p) := by
  rw [powMod_eq _ _ _ hk, ZMod.natCast_mod, Nat.cast_pow]

end Pratt
