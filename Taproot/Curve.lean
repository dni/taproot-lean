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

end Curve

end Taproot
