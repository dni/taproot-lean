import Taproot.BIP340
import Taproot.Secp256k1

/-!
# BIP340 test vectors

Byte-level BIP340 (`pubkeyBytes`, `signBytes`, `verifyBytes`) with SHA-256
tagged hashes, built directly on the **proven** definitions
`BIP340.pubkey/sign/verify` for `secp256k1`. Every official test vector from
`bip-0340/test-vectors.csv` is checked against it.

Running elliptic-curve arithmetic needs fast scalar multiplication, so we also
define `…Fast` versions that use double-and-add, and **prove** they are equal to
the reference versions; the vector checks run the fast versions with
`native_decide` (which trusts Lean's compiler).
-/

set_option linter.style.longLine false
set_option linter.style.native false

namespace Taproot.BIP340Vectors

open Secp256k1

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-! ## SHA-256 (FIPS 180-4) -/

def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def sha256H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- Message padding: `0x80`, zeros, then the 64-bit big-endian bit length. -/
def sha256Pad (msg : Bytes) : Bytes :=
  let len := msg.length
  msg ++ ([0x80] : Bytes) ++ List.replicate ((119 - len % 64) % 64) (0 : UInt8) ++
    (List.range 8).reverse.map (fun i => ((len * 8) >>> (8 * i)).toUInt8)

def be32 (b : Array UInt8) (i : ℕ) : UInt32 :=
  (b[i]!.toUInt32 <<< 24) ||| (b[i + 1]!.toUInt32 <<< 16) ||| (b[i + 2]!.toUInt32 <<< 8) |||
    b[i + 3]!.toUInt32

/-- The SHA-256 compression function on the 64-byte block at offset `off`. -/
def sha256Block (h : Array UInt32) (blk : Array UInt8) (off : ℕ) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for i in [0:16] do
    w := w.push (be32 blk (off + 4 * i))
  for i in [16:64] do
    let s0 := rotr w[i - 15]! 7 ^^^ rotr w[i - 15]! 18 ^^^ (w[i - 15]! >>> 3)
    let s1 := rotr w[i - 2]! 17 ^^^ rotr w[i - 2]! 19 ^^^ (w[i - 2]! >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := hh + S1 + ch + sha256K[i]! + w[i]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
    h[7]! + hh]

/-- SHA-256. -/
def sha256 (msg : Bytes) : Bytes := Id.run do
  let padded := (sha256Pad msg).toArray
  let mut h := sha256H0
  for i in [0:padded.size / 64] do
    h := sha256Block h padded (64 * i)
  return h.toList.flatMap fun (x : UInt32) =>
    ([(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8] : Bytes)

/-- BIP340 tagged hash: `SHA256(SHA256(tag) ‖ SHA256(tag) ‖ msg)`. -/
def taggedHash (tag : String) (msg : Bytes) : Bytes :=
  let th := sha256 tag.toUTF8.toList
  sha256 (th ++ th ++ msg)

/-! ## Byte encodings -/

/-- `int(b)`: big-endian bytes to a number. -/
def toNatBE (b : Bytes) : ℕ := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- `bytes(x)`: a number as 32 big-endian bytes. -/
def bytes32 (x : ℕ) : Bytes := (List.range 32).reverse.map fun i => (x / 256 ^ i % 256).toUInt8

/-- Bytes from a hex string. -/
def hex (s : String) : Bytes :=
  let digit (c : Char) : ℕ :=
    if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
  let rec go : List Char → Bytes
    | a :: b :: rest => (16 * digit a + digit b).toUInt8 :: go rest
    | _ => []
  go s.toList

/-! ## BIP340 on bytes, built on the proven definitions -/

/-- `e = int(hash_BIP0340/challenge(bytes(r) ‖ bytes(P) ‖ m)) mod n`. -/
def challenge (r pk : F) (m : Bytes) : ZMod n :=
  (toNatBE (taggedHash "BIP0340/challenge" (bytes32 r.val ++ bytes32 pk.val ++ m)) : ZMod n)

/-- `k' = int(hash_BIP0340/nonce(bytes(d) xor hash_BIP0340/aux(a) ‖ bytes(P) ‖ m)) mod n`. -/
def nonce (aux : Bytes) (d : ZMod n) (px : F) (m : Bytes) : ZMod n :=
  let t := List.zipWith (· ^^^ ·) (bytes32 d.val) (taggedHash "BIP0340/aux" aux)
  (toNatBE (taggedHash "BIP0340/nonce" (t ++ bytes32 px.val ++ m)) : ZMod n)

/-- `PubKey(sk)`. -/
def pubkeyBytes (sk : Bytes) : Option Bytes :=
  let d := toNatBE sk
  if d = 0 ∨ n ≤ d then none
  else (BIP340.pubkey secp256k1 (d : ZMod n)).map (fun x => bytes32 x.val)

/-- `Sign(sk, m, a)`. -/
def signBytes (sk m aux : Bytes) : Option Bytes :=
  let d := toNatBE sk
  if d = 0 ∨ n ≤ d then none
  else (BIP340.sign secp256k1 challenge (nonce aux) (d : ZMod n) m).map
    fun rs => bytes32 rs.1.val ++ bytes32 rs.2.val

/-- `Verify(pk, m, sig)`, including BIP340's range checks on the inputs. -/
def verifyBytes (pk m sig : Bytes) : Bool :=
  let x := toNatBE pk
  let r := toNatBE (sig.take 32)
  let s := toNatBE (sig.drop 32)
  pk.length == 32 && sig.length == 64 && decide (x < p) && decide (r < p) && decide (s < n) &&
    BIP340.verify secp256k1 challenge (x : F) m ((r : F), (s : ZMod n))

/-! ## Fast evaluation, proven equal -/

/-- `k·G` by double-and-add. -/
def mulGFast (k : ZMod n) : Point := smulDA k.val G

theorem mulGFast_eq (k : ZMod n) : mulGFast k = secp256k1.mulG k := by
  rw [mulGFast, smulDA_eq, Curve.mulG_eq_val_smul]; rfl

/-- `lift_x` with the square root computed by fast modular exponentiation. -/
def liftXFast (x : F) : Option Point :=
  let y : F := ((Pratt.powMod (x ^ 3 + 7).val ((p + 1) / 4) p : ℕ) : F)
  if h : y ^ 2 = x ^ 3 + 7 then
    some (.some x (evenRoot y) ((nonsingular_iff _ _).mpr (by rw [evenRoot_sq, h])))
  else none

theorem powMod_sqrt (x : F) :
    ((Pratt.powMod (x ^ 3 + 7).val ((p + 1) / 4) p : ℕ) : F) = (x ^ 3 + 7) ^ sqrtExp := by
  rw [sqrtExp_def, ← Pratt.natCast_pow_eq_powMod _ _ _ (by decide +kernel), ZMod.natCast_zmod_val]

theorem liftXFast_eq (x : F) : liftXFast x = liftX x := by
  unfold liftXFast liftX
  simp only [powMod_sqrt]

def evenScalarFast (d : ZMod n) : ZMod n := if hasEvenY (mulGFast d) then d else -d

theorem evenScalarFast_eq (d : ZMod n) : evenScalarFast d = secp256k1.evenScalar d := by
  unfold evenScalarFast Curve.evenScalar
  rw [mulGFast_eq]
  rfl

def signFast (aux : Bytes) (sk : ZMod n) (m : Bytes) : Option (F × ZMod n) :=
  if sk = 0 then none else
  let P := mulGFast sk
  let d := evenScalarFast sk
  let k₀ := nonce aux d (xCoord P) m
  if k₀ = 0 then none else
  let R := mulGFast k₀
  let k := evenScalarFast k₀
  let e := challenge (xCoord R) (xCoord P) m
  some (xCoord R, k + e * d)

theorem signFast_eq (aux : Bytes) (sk : ZMod n) (m : Bytes) :
    signFast aux sk m = BIP340.sign secp256k1 challenge (nonce aux) sk m := by
  unfold signFast BIP340.sign
  simp only [mulGFast_eq, evenScalarFast_eq]
  rfl

def verifyFast (pk : F) (m : Bytes) (sig : F × ZMod n) : Bool :=
  match liftXFast pk with
  | none => false
  | some P =>
    let e := challenge sig.1 pk m
    let R := mulGFast sig.2 - smulDA e.val P
    decide (R ≠ 0) && hasEvenY R && decide (xCoord R = sig.1)

/-- The `lift_x` of the packaged curve. (Proven by reducing the projection;
plain `rfl` makes Lean unfold `liftX` and try to evaluate `c^((p+1)/4)`.) -/
theorem secp256k1_liftX : secp256k1.liftX = liftX := by
  simp only [secp256k1]

theorem verifyFast_eq (pk : F) (m : Bytes) (sig : F × ZMod n) :
    verifyFast pk m sig = BIP340.verify secp256k1 challenge pk m sig := by
  obtain ⟨r, s⟩ := sig
  unfold verifyFast BIP340.verify
  rw [liftXFast_eq, secp256k1_liftX]
  cases liftX pk with
  | none => rfl
  | some P =>
    simp only [mulGFast_eq, smulDA_eq]
    rfl

def pubkeyBytesFast (sk : Bytes) : Option Bytes :=
  let d := toNatBE sk
  if d = 0 ∨ n ≤ d then none else some (bytes32 (xCoord (mulGFast (d : ZMod n))).val)

theorem pubkeyBytesFast_eq (sk : Bytes) : pubkeyBytesFast sk = pubkeyBytes sk := by
  unfold pubkeyBytesFast pubkeyBytes BIP340.pubkey
  by_cases h : toNatBE sk = 0 ∨ n ≤ toNatBE sk
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    have hne : ((toNatBE sk : ℕ) : ZMod n) ≠ 0 := by
      intro h0
      rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff', Nat.zero_mod,
        Nat.mod_eq_of_lt (by omega)] at h0
      omega
    simp only [hne, ↓reduceIte, mulGFast_eq]
    rfl

def signBytesFast (sk m aux : Bytes) : Option Bytes :=
  let d := toNatBE sk
  if d = 0 ∨ n ≤ d then none
  else (signFast aux (d : ZMod n) m).map fun rs => bytes32 rs.1.val ++ bytes32 rs.2.val

theorem signBytesFast_eq (sk m aux : Bytes) : signBytesFast sk m aux = signBytes sk m aux := by
  simp only [signBytesFast, signBytes, signFast_eq]

def verifyBytesFast (pk m sig : Bytes) : Bool :=
  let x := toNatBE pk
  let r := toNatBE (sig.take 32)
  let s := toNatBE (sig.drop 32)
  pk.length == 32 && sig.length == 64 && decide (x < p) && decide (r < p) && decide (s < n) &&
    verifyFast (x : F) m ((r : F), (s : ZMod n))

theorem verifyBytesFast_eq (pk m sig : Bytes) : verifyBytesFast pk m sig = verifyBytes pk m sig := by
  simp only [verifyBytesFast, verifyBytes, verifyFast_eq]

/-! ## The official test vectors -/

/-- A row of `bip-0340/test-vectors.csv`. -/
structure Vector where
  index : ℕ
  secretKey : Option String
  publicKey : String
  auxRand : Option String
  message : String
  signature : String
  result : Bool

def vectors : List Vector := [
  ⟨0, some "0000000000000000000000000000000000000000000000000000000000000003", "F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9", some "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0", true⟩,
  ⟨1, some "B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF", "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", some "0000000000000000000000000000000000000000000000000000000000000001",
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE33418906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A", true⟩,
  ⟨2, some "C90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C9", "DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8", some "C87AA53824B4D7AE2EB035A2B5BBBCCC080E76CDC6D1692C4B0B62D798E6D906",
    "7E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C",
    "5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1BAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7", true⟩,
  ⟨3, some "0B432B2677937381AEF05BB02A66ECD012773062CF3FA2549E44F58ED2401710", "25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517", some "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
    "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
    "7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3", true⟩,
  ⟨4, none, "D69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9", none,
    "4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703",
    "00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C6376AFB1548AF603B3EB45C9F8207DEE1060CB71C04E80F593060B07D28308D7F4", true⟩,
  ⟨5, none, "EEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B", false⟩,
  ⟨6, none, "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "FFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A14602975563CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2", false⟩,
  ⟨7, none, "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "1FA62E331EDBC21C394792D2AB1100A7B432B013DF3F6FF4F99FCB33E0E1515F28890B3EDB6E7189B630448B515CE4F8622A954CFE545735AAEA5134FCCDB2BD", false⟩,
  ⟨8, none, "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769961764B3AA9B2FFCB6EF947B6887A226E8D7C93E00C5ED0C1834FF0D0C2E6DA6", false⟩,
  ⟨9, none, "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "0000000000000000000000000000000000000000000000000000000000000000123DDA8328AF9C23A94C1FEECFD123BA4FB73476F0D594DCB65C6425BD186051", false⟩,
  ⟨10, none, "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "00000000000000000000000000000000000000000000000000000000000000017615FBAF5AE28864013C099742DEADB4DBA87F11AC6754F93780D5A1837CF197", false⟩,
  ⟨11, none, "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "4A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B", false⟩,
  ⟨12, none, "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B", false⟩,
  ⟨13, none, "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", false⟩,
  ⟨14, none, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30", none,
    "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
    "6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B", false⟩,
  ⟨15, some "0340034003400340034003400340034003400340034003400340034003400340", "778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117", some "0000000000000000000000000000000000000000000000000000000000000000",
    "",
    "71535DB165ECD9FBBC046E5FFAEA61186BB6AD436732FCCC25291A55895464CF6069CE26BF03466228F19A3A62DB8A649F2D560FAC652827D1AF0574E427AB63", true⟩,
  ⟨16, some "0340034003400340034003400340034003400340034003400340034003400340", "778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117", some "0000000000000000000000000000000000000000000000000000000000000000",
    "11",
    "08A20A0AFEF64124649232E0693C583AB1B9934AE63B4C3511F3AE1134C6A303EA3173BFEA6683BD101FA5AA5DBC1996FE7CACFC5A577D33EC14564CEC2BACBF", true⟩,
  ⟨17, some "0340034003400340034003400340034003400340034003400340034003400340", "778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117", some "0000000000000000000000000000000000000000000000000000000000000000",
    "0102030405060708090A0B0C0D0E0F1011",
    "5130F39A4059B43BC7CAC09A19ECE52B5D8699D1A71E3C52DA9AFDB6B50AC370C4A482B77BF960F8681540E25B6771ECE1E5A37FD80E5A51897C5566A97EA5A5", true⟩,
  ⟨18, some "0340034003400340034003400340034003400340034003400340034003400340", "778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117", some "0000000000000000000000000000000000000000000000000000000000000000",
    "99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999",
    "403B12B0D8555A344175EA7EC746566303321E5DBFA8BE6F091635163ECA79A8585ED3E3170807E7C03B720FC54C7B23897FCBA0E9D0B4A06894CFD249F22367", true⟩]

/-- Sanity check of the hash: `SHA256("abc")`. -/
theorem sha256_abc :
    sha256 "abc".toUTF8.toList =
      hex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  native_decide

/-- Every vector's verification result matches. -/
theorem vectors_verify :
    vectors.all (fun v => verifyBytes (hex v.publicKey) (hex v.message) (hex v.signature) == v.result)
      = true := by
  simp only [← verifyBytesFast_eq]
  native_decide

/-- For every vector with a secret key: `PubKey(sk)` is the listed public key and
`Sign(sk, m, aux)` is exactly the listed signature. -/
theorem vectors_sign :
    vectors.all (fun v => match v.secretKey, v.auxRand with
      | some sk, some aux =>
        pubkeyBytes (hex sk) == some (hex v.publicKey) &&
        signBytes (hex sk) (hex v.message) (hex aux) == some (hex v.signature)
      | _, _ => true) = true := by
  simp only [← pubkeyBytesFast_eq, ← signBytesFast_eq]
  native_decide

end Taproot.BIP340Vectors
