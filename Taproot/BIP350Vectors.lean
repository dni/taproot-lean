import Taproot.BIP350

/-!
# Bech32/Bech32m strings, segwit addresses, and the BIP350 test vectors

String encoding/decoding and segwit address rules, following the reference
Python implementation linked from BIP350 (`segwit_addr.py`), and every test
vector from BIP350's "Test vectors" section, checked by the Lean kernel.
-/

namespace Bech32

/-- The Bech32 character set: symbol `i` is written as `charset[i]`. -/
def charset : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList

/-- Position of `c` in `l`, if present. -/
def indexOf (c : Char) : List Char → Option ℕ
  | [] => none
  | d :: ds => if d = c then some 0 else (indexOf c ds).map (· + 1)

/-- Position of the last occurrence of `c` in `l`, if present. -/
def lastIndexOf (c : Char) (l : List Char) : Option ℕ :=
  (indexOf c l.reverse).map (l.length - 1 - ·)

/-- `bech32_encode`: `hrp ++ "1" ++ data ++ checksum`, lowercase. -/
def encode (enc : Encoding) (hrp : List Char) (data : List ℕ) : List Char :=
  hrp ++ ['1'] ++ (data ++ createChecksum enc hrp data).map (charset.getD · 'q')

/-- `bech32_decode`: returns the HRP, the data (without checksum), and which
encoding's checksum it satisfies. -/
def decode (s : List Char) : Option (List Char × List ℕ × Encoding) :=
  if s.any (fun c => c.toNat < 33 || 126 < c.toNat) then none else
  if s.map Char.toLower ≠ s ∧ s.map Char.toUpper ≠ s then none else
  let s := s.map Char.toLower
  match lastIndexOf '1' s with
  | none => none
  | some pos =>
    if pos < 1 ∨ s.length < pos + 7 ∨ 90 < s.length then none else
    let hrp := s.take pos
    match (s.drop (pos + 1)).mapM (indexOf · charset) with
    | none => none
    | some data =>
      let chk := polymod (hrpExpand hrp ++ data)
      if chk = Encoding.bech32.const then some (hrp, data.take (data.length - 6), .bech32)
      else if chk = Encoding.bech32m.const then some (hrp, data.take (data.length - 6), .bech32m)
      else none

/-- `convertbits`: regroup `frombits`-bit values into `tobits`-bit values. -/
def convertbits (data : List ℕ) (frombits tobits : ℕ) (pad : Bool) : Option (List ℕ) :=
  let maxv := 2 ^ tobits - 1
  let maxAcc := 2 ^ (frombits + tobits - 1) - 1
  let rec go : List ℕ → ℕ → ℕ → List ℕ → Option (List ℕ)
    | [], acc, bits, ret =>
      if pad then
        some (if bits > 0 then ret ++ [(acc <<< (tobits - bits)) &&& maxv] else ret)
      else if frombits ≤ bits ∨ ((acc <<< (tobits - bits)) &&& maxv) ≠ 0 then none
      else some ret
    | v :: vs, acc, bits, ret =>
      if v >>> frombits ≠ 0 then none else
      let acc := ((acc <<< frombits) ||| v) &&& maxAcc
      let rec emit (acc bits : ℕ) (ret : List ℕ) (fuel : ℕ) : ℕ × List ℕ :=
        match fuel with
        | 0 => (bits, ret)
        | fuel + 1 =>
          if tobits ≤ bits then
            emit acc (bits - tobits) (ret ++ [(acc >>> (bits - tobits)) &&& maxv]) fuel
          else (bits, ret)
      let (bits, ret) := emit acc (bits + frombits) ret (bits + frombits)
      go vs acc bits ret
  go data 0 0 []

/-- Segwit address decoding (`segwit_addr.decode`), returning the witness
version and program. Enforces BIP350: v0 must use Bech32, v1+ Bech32m. -/
def decodeSegwit (hrp : List Char) (addr : List Char) : Option (ℕ × List ℕ) :=
  match decode addr with
  | none => none
  | some (hrpGot, data, enc) =>
    if hrpGot ≠ hrp then none else
    match data with
    | [] => none
    | ver :: rest =>
      match convertbits rest 5 8 false with
      | none => none
      | some prog =>
        if prog.length < 2 ∨ 40 < prog.length then none
        else if 16 < ver then none
        else if ver = 0 ∧ prog.length ≠ 20 ∧ prog.length ≠ 32 then none
        else if (ver = 0 ∧ enc ≠ .bech32) ∨ (ver ≠ 0 ∧ enc ≠ .bech32m) then none
        else some (ver, prog)

/-- Segwit address encoding (`segwit_addr.encode`): Bech32 for v0, Bech32m for v1+. -/
def encodeSegwit (hrp : List Char) (ver : ℕ) (prog : List ℕ) : Option (List Char) :=
  let enc := if ver = 0 then Encoding.bech32 else Encoding.bech32m
  match convertbits prog 8 5 true with
  | none => none
  | some data =>
    let addr := encode enc hrp (ver :: data)
    if (decodeSegwit hrp addr).isSome then some addr else none

/-- The scriptPubKey for a witness program: `OP_n <len> <program>`. -/
def scriptPubKey (ver : ℕ) (prog : List ℕ) : List ℕ :=
  (if ver = 0 then 0 else 0x50 + ver) :: prog.length :: prog

/-- Bytes from a hex string. -/
def hexBytes (s : String) : List ℕ :=
  let digit (c : Char) : ℕ := (indexOf c.toLower "0123456789abcdef".toList).getD 0
  let rec go : List Char → List ℕ
    | a :: b :: rest => (16 * digit a + digit b) :: go rest
    | _ => []
  go s.toList

/-! ## BIP350 test vectors: Bech32m strings -/

/-- Strings that are valid Bech32m. -/
def validBech32m : List String :=
  ["A1LQFN3A", "a1lqfn3a",
   "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6",
   "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx",
   "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8",
   "split1checkupstagehandshakeupstreamerranterredcaperredlc445v",
   "?1v759aa"]

/-- Strings that are not valid Bech32m. -/
def invalidBech32m : List String :=
  [String.singleton (Char.ofNat 0x20) ++ "1xj0phk",
   String.singleton (Char.ofNat 0x7F) ++ "1g6xzxy",
   String.singleton (Char.ofNat 0x80) ++ "1vctc34",
   "an84characterslonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11d6pts4",
   "qyrz8wqd2c9m", "1qyrz8wqd2c9m", "y1b0jsk6g", "lt1igcx5c0", "in1muywd", "mm1crxm3i",
   "au1s5cgom", "M1VUXWEZ", "16plkw9", "1p2gdwpf"]

/-- Every valid vector decodes, with a Bech32m checksum. -/
theorem validBech32m_ok :
    validBech32m.all (fun s => ((decode s.toList).map (·.2.2)) == some .bech32m) = true := by
  decide +kernel

/-- No valid vector is accepted as Bech32 (no string is valid under both). -/
theorem validBech32m_not_bech32 :
    validBech32m.all (fun s => ((decode s.toList).map (·.2.2)) != some .bech32) = true := by
  decide +kernel

/-- Every invalid vector is rejected by the decoder. -/
theorem invalidBech32m_rejected :
    invalidBech32m.all (fun s => (decode s.toList).isNone) = true := by
  decide +kernel

/-! ## BIP350 test vectors: segwit addresses -/

/-- Valid segwit addresses and their scriptPubKeys. -/
def validSegwit : List (String × String) :=
  [("BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4",
     "0014751e76e8199196d454941c45d1b3a323f1433bd6"),
   ("tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7",
     "00201863143c14c5166804bd19203356da136c985678cd4d27a1b8c6329604903262"),
   ("bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y",
     "5128751e76e8199196d454941c45d1b3a323f1433bd6751e76e8199196d454941c45d1b3a323f1433bd6"),
   ("BC1SW50QGDZ25J", "6002751e"),
   ("bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs", "5210751e76e8199196d454941c45d1b3a323"),
   ("tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy",
     "0020000000c4a5cad46221b2a187905e5266362b99d5e91c6ce24d165dab93e86433"),
   ("tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c",
     "5120000000c4a5cad46221b2a187905e5266362b99d5e91c6ce24d165dab93e86433"),
   ("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0",
     "512079be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")]

/-- Invalid segwit addresses (each is rejected for both `bc` and `tb`). -/
def invalidSegwit : List String :=
  ["tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut",
   "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd",
   "tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf",
   "BC1S0XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ54WELL",
   "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh",
   "tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47",
   "bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4",
   "BC130XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ7ZWS8R",
   "bc1pw5dgrnzv",
   "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav",
   "BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P",
   "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq",
   "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf",
   "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j",
   "bc1gmk9yu"]

/-- The HRP of a test address (`bc` or `tb`), from its lowercase form. -/
def hrpOf (addr : String) : List Char := (addr.toList.map Char.toLower).take 2

/-- Every valid address decodes to the expected scriptPubKey, and re-encoding
the decoded program gives back the (lowercase) address. -/
theorem validSegwit_ok :
    validSegwit.all (fun (addr, spk) =>
      match decodeSegwit (hrpOf addr) addr.toList with
      | none => false
      | some (ver, prog) =>
        scriptPubKey ver prog == hexBytes spk &&
        encodeSegwit (hrpOf addr) ver prog == some (addr.toList.map Char.toLower)) = true := by
  decide +kernel

/-- Every invalid address is rejected. -/
theorem invalidSegwit_rejected :
    invalidSegwit.all (fun addr =>
      (decodeSegwit ['b', 'c'] addr.toList).isNone &&
      (decodeSegwit ['t', 'b'] addr.toList).isNone) = true := by
  decide +kernel

end Bech32
