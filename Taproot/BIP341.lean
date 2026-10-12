import Taproot.BIP340

/-!
# BIP341: Taproot

The Taproot output key commits to an internal key `P` and an optional script
tree: `Q = P + t·G`, where `t = hash_TapTweak(P ‖ merkle_root)`. We prove:

* **Key tweaking is consistent**: tweaking the secret key the BIP341 way gives
  exactly the secret key of the tweaked public key `Q`.
* **Key-path spending works**: a BIP340 signature made with the tweaked secret
  key verifies under the output key.
* **Script-path spending works**: for every leaf of the script tree, the
  control block built from its Merkle path passes BIP341's commitment check.

As in `BIP340`, the hashes are arbitrary functions and byte encodings are left
out: `tweak` is `int(hash_TapTweak(p ‖ root)) mod n`, `leafHash` is
`hash_TapLeaf`, and `branch` is `hash_TapBranch` on its two (sorted) children.
-/

namespace Taproot.BIP341

open Curve BIP340

variable {n : ℕ} [Fact n.Prime] {E X : Type*} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  (C : Curve n E X)

section Tweak

variable {T : Type*} (tweak : X → Option T → ZMod n)

/-- `taproot_tweak_pubkey(p, root)`: the output key `x(Q)` and the parity of `Q`'s y. -/
def outputKey (p : X) (root : Option T) : Option (X × Bool) :=
  match C.liftX p with
  | none => none
  | some P =>
    let Q := P + (tweak p root).val • C.G
    if Q = 0 then none else some (C.x Q, C.hasEvenY Q)

/-- `taproot_tweak_seckey(sk, root)`. -/
def tweakSeckey (sk : ZMod n) (root : Option T) : Option (ZMod n) :=
  if sk = 0 then none else
  let d := C.evenScalar sk + tweak (C.x (C.mulG sk)) root
  if d = 0 then none else some d

omit [DecidableEq X] in
/-- **Tweaking is consistent**: the tweaked secret key `d` satisfies `d·G = Q`,
so the output key is exactly `d`'s public key. -/
theorem outputKey_of_tweakSeckey {sk d : ZMod n} {root : Option T} {p : X}
    (hpk : pubkey C sk = some p) (hd : tweakSeckey C tweak sk root = some d) :
    outputKey C tweak p root = some (C.x (C.mulG d), C.hasEvenY (C.mulG d)) := by
  unfold pubkey at hpk
  unfold tweakSeckey at hd
  dsimp only at hd
  split_ifs at hpk hd with hsk hd0
  cases hpk
  cases hd
  have hQ : C.mulG (C.evenScalar sk) + (tweak (C.x (C.mulG sk)) root).val • C.G =
      C.mulG (C.evenScalar sk + tweak (C.x (C.mulG sk)) root) := by
    rw [map_add, ← mulG_eq_val_smul]
  simp only [outputKey, C.liftX_x_mulG hsk, hQ, C.mulG_ne_zero hd0, ite_false]

/-- **Key-path spending**: signing with the tweaked secret key gives a
signature that verifies under the output key `x(Q)`. -/
theorem keyPath_verify {M : Type*} (challenge : X → X → M → ZMod n)
    (nonce : ZMod n → X → M → ZMod n) {sk d : ZMod n} {root : Option T} {p q : X}
    {parity : Bool} {m : M} {sig : X × ZMod n}
    (hpk : pubkey C sk = some p) (hd : tweakSeckey C tweak sk root = some d)
    (hQ : outputKey C tweak p root = some (q, parity))
    (hsig : sign C challenge nonce d m = some sig) :
    verify C challenge q m sig = true := by
  rw [outputKey_of_tweakSeckey C tweak hpk hd] at hQ
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hQ)
  have hd0 : d ≠ 0 := by
    unfold tweakSeckey at hd; dsimp only at hd; split_ifs at hd with _ h; cases hd; exact h
  exact verify_sign C challenge nonce (by simp [pubkey, hd0]) hsig

end Tweak

section ScriptPath

variable {L T : Type*} [LinearOrder T] (leafHash : L → T) (branch : T → T → T)

/-- `hash_TapBranch` of two children, sorted first (as BIP341 does). -/
def tapBranch (a b : T) : T :=
  if a ≤ b then branch a b else branch b a

theorem tapBranch_comm (a b : T) : tapBranch branch a b = tapBranch branch b a := by
  unfold tapBranch
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.le, not_le.mpr h]
  · rfl
  · simp [h.le, not_le.mpr h]

/-- A Taproot script tree: leaves are scripts, nodes are pairs of subtrees. -/
inductive ScriptTree (L : Type*)
  | leaf (l : L)
  | node (left right : ScriptTree L)

namespace ScriptTree

/-- The Merkle root of a script tree. -/
def root : ScriptTree L → T
  | leaf l => leafHash l
  | node a b => tapBranch branch (a.root) (b.root)

/-- Every leaf together with its Merkle path (sibling hashes, bottom-up),
as put in the control block. -/
def paths : ScriptTree L → List (L × List T)
  | leaf l => [(l, [])]
  | node a b =>
    (a.paths.map fun lp => (lp.1, lp.2 ++ [b.root leafHash branch])) ++
    (b.paths.map fun lp => (lp.1, lp.2 ++ [a.root leafHash branch]))

end ScriptTree

/-- The Merkle root recomputed from a leaf and its path, as in BIP341 script-path validation. -/
def computeRoot (l : L) (path : List T) : T :=
  path.foldl (tapBranch branch) (leafHash l)

/-- Recomputing the root from any leaf's path gives the tree's root. -/
theorem computeRoot_of_mem (t : ScriptTree L) {l : L} {path : List T}
    (h : (l, path) ∈ t.paths leafHash branch) :
    computeRoot leafHash branch l path = t.root leafHash branch := by
  induction t generalizing l path with
  | leaf l' =>
    simp only [ScriptTree.paths, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | node a b iha ihb =>
    simp only [ScriptTree.paths, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨⟨l', p'⟩, hmem, rfl, rfl⟩ | ⟨⟨l', p'⟩, hmem, rfl, rfl⟩
    · simp only [computeRoot, List.foldl_append, List.foldl_cons, List.foldl_nil] at iha ⊢
      rw [iha hmem, ScriptTree.root]
    · simp only [computeRoot, List.foldl_append, List.foldl_cons, List.foldl_nil] at ihb ⊢
      rw [ihb hmem, ScriptTree.root, tapBranch_comm]

/-- BIP341 script-path commitment check: given the output key `q`, the parity
bit and internal key `p` from the control block, and a leaf with its Merkle
path, recompute `Q = P + t·G` and compare. -/
def verifyScriptPath (tweak : X → Option T → ZMod n) (q : X) (parity : Bool) (p : X)
    (l : L) (path : List T) : Bool :=
  match C.liftX p with
  | none => false
  | some P =>
    let Q := P + (tweak p (some (computeRoot leafHash branch l path))).val • C.G
    decide (Q ≠ 0) && decide (C.x Q = q) && (C.hasEvenY Q == parity)

omit [Fact n.Prime] in
/-- **Script-path spending**: if `q` is the output key committing to script
tree `t`, every leaf of `t` passes the commitment check with its Merkle path. -/
theorem verifyScriptPath_of_mem (tweak : X → Option T → ZMod n) (t : ScriptTree L)
    {p q : X} {parity : Bool} {l : L} {path : List T}
    (hQ : outputKey C tweak p (some (t.root leafHash branch)) = some (q, parity))
    (hmem : (l, path) ∈ t.paths leafHash branch) :
    verifyScriptPath C leafHash branch tweak q parity p l path = true := by
  unfold outputKey at hQ
  unfold verifyScriptPath
  rw [computeRoot_of_mem leafHash branch t hmem]
  split at hQ
  · cases hQ
  · dsimp only at hQ ⊢
    split_ifs at hQ with h0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hQ)
    simp [h0]

end ScriptPath

end Taproot.BIP341
