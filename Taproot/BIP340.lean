import Taproot.Curve

/-!
# BIP340: Schnorr signatures

The BIP340 key generation, signing and verification algorithms, and a proof
that **every signature produced by `sign` is accepted by `verify`**.

Modelling choices:
* Secret keys, nonces and `s` are elements of `ZMod n`. BIP340's range checks
  (`0 < d' < n`, `s < n`) become part of the type; the "fail if zero" checks
  are kept.
* Public keys and `r` are x-coordinates (`X`). Byte encodings are left out.
* The tagged hashes are arbitrary functions: `challenge` is
  `int(hash_BIP0340/challenge(r ‖ P ‖ m)) mod n`, and `nonce` derives `k'` from
  `d`, `P`, `m` (and the aux randomness, which it can close over).
  Correctness holds for *every* choice of hash function.
-/

namespace Taproot.BIP340

open Curve

variable {n : ℕ} [Fact n.Prime] {E X M : Type*} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  (C : Curve n E X)

/-- `PubKey(sk)`: the x-coordinate of `sk·G`. Fails for `sk = 0`. -/
def pubkey (sk : ZMod n) : Option X :=
  if sk = 0 then none else some (C.x (C.mulG sk))

/-- BIP340 `Sign(sk, m)`, returning the signature `(r, s)`. -/
def sign (challenge : X → X → M → ZMod n) (nonce : ZMod n → X → M → ZMod n)
    (sk : ZMod n) (m : M) : Option (X × ZMod n) :=
  if sk = 0 then none else
  let P := C.mulG sk
  let d := C.evenScalar sk
  let k₀ := nonce d (C.x P) m
  if k₀ = 0 then none else
  let R := C.mulG k₀
  let k := C.evenScalar k₀
  let e := challenge (C.x R) (C.x P) m
  some (C.x R, k + e * d)

/-- BIP340 `Verify(pk, m, sig)`. -/
def verify (challenge : X → X → M → ZMod n) (pk : X) (m : M) (sig : X × ZMod n) : Bool :=
  match C.liftX pk with
  | none => false
  | some P =>
    let (r, s) := sig
    let e := challenge r pk m
    let R := C.mulG s - e.val • P
    decide (R ≠ 0) && C.hasEvenY R && decide (C.x R = r)

/-- **Correctness of BIP340**: a signature made with secret key `sk` verifies
under the public key of `sk`, for every message and every hash function. -/
theorem verify_sign (challenge : X → X → M → ZMod n) (nonce : ZMod n → X → M → ZMod n)
    {sk : ZMod n} {m : M} {pk : X} {sig : X × ZMod n}
    (hpk : pubkey C sk = some pk) (hsig : sign C challenge nonce sk m = some sig) :
    verify C challenge pk m sig = true := by
  unfold pubkey at hpk
  unfold sign at hsig
  dsimp only at hsig
  split_ifs at hpk hsig with hsk hk
  cases hpk
  cases hsig
  -- `s·G - e·P` with `s = k + e·d` and `P = d·G` is `k·G`, the even-y version of `R`.
  simp only [verify, C.liftX_x_mulG hsk, C.val_smul_mulG, ← map_sub, add_sub_cancel_right]
  simp [C.mulG_ne_zero (C.evenScalar_ne_zero hk), C.hasEvenY_evenScalar hk, C.x_evenScalar]

end Taproot.BIP340
