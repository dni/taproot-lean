import Mathlib

/-!
# The curve interface used by BIP340/341

BIP340 only ever works with multiples of the generator `G`, which has prime
order `n`. So instead of requiring the whole curve to be a `ZMod n`-module
(which for secp256k1 would mean counting its points), we ask for an additive
group with a point `G` of order `n`, plus the x-coordinate / even-y / `lift_x`
operations BIP340 uses, with the properties those operations need.

`Taproot.Secp256k1` builds this interface from Mathlib's elliptic-curve
group, so every theorem proven against it holds for secp256k1.
-/

namespace Taproot

/-- What BIP340/341 need from an elliptic-curve group:
`E` is the group of points, `X` the type of x-coordinates, `n` the order of `G`. -/
structure Curve (n : ℕ) (E X : Type*) [AddCommGroup E] where
  /-- The generator. -/
  G : E
  G_ne_zero : G ≠ 0
  order_G : n • G = 0
  /-- The x-coordinate of a point (meaningless for the point at infinity). -/
  x : E → X
  /-- Whether the point's y-coordinate is even (BIP340 `has_even_y`). -/
  hasEvenY : E → Bool
  /-- BIP340 `lift_x`: the point with this x-coordinate and an even y, if any. -/
  liftX : X → Option E
  x_neg (P : E) : x (-P) = x P
  hasEvenY_neg (P : E) : P ≠ 0 → hasEvenY (-P) = !hasEvenY P
  liftX_x (P : E) : P ≠ 0 → hasEvenY P = true → liftX (x P) = some P
  /-- `lift_x` only returns nonzero even-y points with the requested x-coordinate. -/
  liftX_spec (r : X) (P : E) : liftX r = some P → P ≠ 0 ∧ hasEvenY P = true ∧ x P = r

namespace Curve

variable {n : ℕ} [Fact n.Prime] {E X : Type*} [AddCommGroup E] (C : Curve n E X)

theorem addOrderOf_G : addOrderOf C.G = n :=
  addOrderOf_eq_prime C.order_G C.G_ne_zero

/-- Scalar multiplication of the generator, `k ↦ k·G`, as a group homomorphism
from `ZMod n` (well defined because `n·G = 0`). -/
def mulG : ZMod n →+ E :=
  ZMod.lift n ⟨zmultiplesHom E C.G, by simp [C.order_G]⟩

theorem mulG_eq_val_smul (k : ZMod n) : C.mulG k = k.val • C.G := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k, ← Int.cast_natCast]
  rw [mulG, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]

theorem mulG_eq_zero {k : ZMod n} : C.mulG k = 0 ↔ k = 0 := by
  rw [mulG_eq_val_smul, ← addOrderOf_dvd_iff_nsmul_eq_zero, addOrderOf_G,
    ← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]

theorem mulG_ne_zero {k : ZMod n} (hk : k ≠ 0) : C.mulG k ≠ 0 :=
  (C.mulG_eq_zero).not.mpr hk

/-- Multiplying a multiple of `G` by a scalar, the way BIP340 computes `e·P`. -/
theorem val_smul_mulG (e d : ZMod n) : e.val • C.mulG d = C.mulG (e * d) := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

/-- BIP340's normalization: negate `d` if needed so that `d·G` has an even y
(`d = d' if has_even_y(P) else n - d'`). -/
def evenScalar (d : ZMod n) : ZMod n :=
  if C.hasEvenY (C.mulG d) then d else -d

theorem evenScalar_ne_zero {d : ZMod n} (hd : d ≠ 0) : C.evenScalar d ≠ 0 := by
  unfold evenScalar; split_ifs <;> simp [hd]

theorem hasEvenY_evenScalar {d : ZMod n} (hd : d ≠ 0) :
    C.hasEvenY (C.mulG (C.evenScalar d)) = true := by
  unfold evenScalar
  split_ifs with h
  · exact h
  · rw [map_neg, C.hasEvenY_neg _ (C.mulG_ne_zero hd)]
    simpa using h

theorem x_evenScalar (d : ZMod n) : C.x (C.mulG (C.evenScalar d)) = C.x (C.mulG d) := by
  unfold evenScalar; split_ifs <;> simp [C.x_neg]

/-- `lift_x(x(d·G))` recovers the even-y version of `d·G`. -/
theorem liftX_x_mulG {d : ZMod n} (hd : d ≠ 0) :
    C.liftX (C.x (C.mulG d)) = some (C.mulG (C.evenScalar d)) := by
  rw [← C.x_evenScalar d]
  exact C.liftX_x _ (C.mulG_ne_zero (C.evenScalar_ne_zero hd)) (C.hasEvenY_evenScalar hd)

theorem mulG_injective : Function.Injective C.mulG := by
  intro a b h
  rw [← sub_eq_zero, ← C.mulG_eq_zero, map_sub, h, sub_self]

omit [Fact n.Prime] in
/-- Two nonzero points with the same x-coordinate and the same y-parity are equal. -/
theorem eq_of_x_eq {P Q : E} (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : C.x P = C.x Q)
    (hy : C.hasEvenY P = C.hasEvenY Q) : P = Q := by
  cases hPe : C.hasEvenY P
  · have hQe : C.hasEvenY Q = false := hy ▸ hPe
    have h1 := C.liftX_x (-P) (neg_ne_zero.mpr hP) (by rw [C.hasEvenY_neg _ hP, hPe]; rfl)
    have h2 := C.liftX_x (-Q) (neg_ne_zero.mpr hQ) (by rw [C.hasEvenY_neg _ hQ, hQe]; rfl)
    rw [C.x_neg, hx, ← C.x_neg, h2, Option.some.injEq] at h1
    exact neg_injective h1.symm
  · have h1 := C.liftX_x P hP hPe
    rw [hx, C.liftX_x Q hQ (hy ▸ hPe), Option.some.injEq] at h1
    exact h1.symm

/-! ## Groups of prime order

Some results (batch verification) need every point, not just the multiples of
`G`, to satisfy `n·P = 0`. For secp256k1 this holds because the group has
exactly `n` points (cofactor 1), but proving that needs point counting, which
is not done here, so these results take it as a hypothesis. -/

/-- Every point satisfies `n·P = 0` (for secp256k1: the group has prime order `n`). -/
def PrimeOrder (n : ℕ) (E : Type*) [AddCommGroup E] : Prop := ∀ P : E, n • P = 0

omit [Fact n.Prime] in
theorem nsmul_mod {P : E} (hP : n • P = 0) (k : ℕ) : (k % n) • P = k • P := by
  conv_rhs => rw [← Nat.mod_add_div k n, add_nsmul, mul_nsmul, hP, nsmul_zero, add_zero]

theorem val_mul_smul {P : E} (hP : n • P = 0) (a b : ZMod n) :
    (a * b).val • P = a.val • b.val • P := by
  rw [ZMod.val_mul, nsmul_mod hP, ← mul_nsmul']

theorem val_sub_smul {P : E} (hP : n • P = 0) (a b : ZMod n) :
    (a - b).val • P = a.val • P - b.val • P := by
  have h : ((a - b).val + b.val) % n = a.val % n := by
    rw [← ZMod.val_add, sub_add_cancel, Nat.mod_eq_of_lt (ZMod.val_lt a)]
  rw [eq_sub_iff_add_eq, ← add_nsmul, ← nsmul_mod hP, h, nsmul_mod hP]

/-- In a group of prime order, a nonzero scalar kills only the zero point. -/
theorem eq_zero_of_val_smul {P : E} (hP : n • P = 0) {k : ZMod n} (hk : k ≠ 0)
    (h : k.val • P = 0) : P = 0 := by
  have h1 : (k⁻¹ * k).val • P = 0 := by rw [val_mul_smul hP, h, nsmul_zero]
  rwa [inv_mul_cancel₀ hk, ZMod.val_one, one_nsmul] at h1

end Curve

end Taproot
