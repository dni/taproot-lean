import Taproot.Pratt

/-!
# Primality of the secp256k1 field size `p` and group order `n`

Pratt certificates generated with PARI/GP and checked here by the Lean kernel.
Primes below 2^16 are proven by `norm_num`.
-/

set_option linter.style.longLine false

namespace Taproot.Primes

theorem prime_85831 : Nat.Prime 85831 :=
  Pratt.prime_of_check 85831 3
    [(2, 1), (3, 1), (5, 1), (2861, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_96557 : Nat.Prime 96557 :=
  Pratt.prime_of_check 96557 2
    [(2, 2), (101, 1), (239, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_120233 : Nat.Prime 120233 :=
  Pratt.prime_of_check 120233 3
    [(2, 3), (7, 1), (19, 1), (113, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_305873 : Nat.Prime 305873 :=
  Pratt.prime_of_check 305873 3
    [(2, 4), (7, 1), (2731, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_1206781 : Nat.Prime 1206781 :=
  Pratt.prime_of_check 1206781 10
    [(2, 2), (3, 1), (5, 1), (20113, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_1627771 : Nat.Prime 1627771 :=
  Pratt.prime_of_check 1627771 3
    [(2, 1), (3, 1), (5, 1), (29, 1), (1871, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_4681609 : Nat.Prime 4681609 :=
  Pratt.prime_of_check 4681609 23
    [(2, 3), (3, 1), (97, 1), (2011, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_7240687 : Nat.Prime 7240687 :=
  Pratt.prime_of_check 7240687 3
    [(2, 1), (3, 1), (1206781, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, prime_1206781⟩)
    (by decide +kernel)

theorem prime_13331831 : Nat.Prime 13331831 :=
  Pratt.prime_of_check 13331831 13
    [(2, 1), (5, 1), (971, 1), (1373, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_44706919 : Nat.Prime 44706919 :=
  Pratt.prime_of_check 44706919 6
    [(2, 1), (3, 1), (797, 1), (9349, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_107590001 : Nat.Prime 107590001 :=
  Pratt.prime_of_check 107590001 3
    [(2, 4), (5, 4), (7, 1), (29, 1), (53, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_545358713 : Nat.Prime 545358713 :=
  Pratt.prime_of_check 545358713 5
    [(2, 3), (41, 1), (59, 1), (28181, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel)

theorem prime_297159362677 : Nat.Prime 297159362677 :=
  Pratt.prime_of_check 297159362677 2
    [(2, 2), (3, 2), (11, 1), (461, 1), (1627771, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_1627771⟩)
    (by decide +kernel)

theorem prime_107361793816595537 : Nat.Prime 107361793816595537 :=
  Pratt.prime_of_check 107361793816595537 3
    [(2, 4), (16699, 1), (85831, 1), (4681609, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, prime_85831, prime_4681609⟩)
    (by decide +kernel)

theorem prime_173378833005251801 : Nat.Prime 173378833005251801 :=
  Pratt.prime_of_check 173378833005251801 6
    [(2, 3), (5, 2), (2621, 1), (24809, 1), (13331831, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_13331831⟩)
    (by decide +kernel)

theorem prime_174723607534414371449 : Nat.Prime 174723607534414371449 :=
  Pratt.prime_of_check 174723607534414371449 3
    [(2, 3), (17, 1), (59, 1), (4051, 1), (120233, 1), (44706919, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_120233, prime_44706919⟩)
    (by decide +kernel)

theorem prime_22149492674086928081353 : Nat.Prime 22149492674086928081353 :=
  Pratt.prime_of_check 22149492674086928081353 5
    [(2, 3), (3, 1), (5323, 1), (173378833005251801, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, prime_173378833005251801⟩)
    (by decide +kernel)

theorem prime_132896956044521568488119 : Nat.Prime 132896956044521568488119 :=
  Pratt.prime_of_check 132896956044521568488119 6
    [(2, 1), (3, 1), (22149492674086928081353, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, prime_22149492674086928081353⟩)
    (by decide +kernel)

theorem prime_29047611873442575647497758179 : Nat.Prime 29047611873442575647497758179 :=
  Pratt.prime_of_check 29047611873442575647497758179 2
    [(2, 1), (293, 1), (305873, 1), (545358713, 1), (297159362677, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, prime_305873, prime_545358713, prime_297159362677⟩)
    (by decide +kernel)

theorem prime_341948486974166000522343609283189 : Nat.Prime 341948486974166000522343609283189 :=
  Pratt.prime_of_check 341948486974166000522343609283189 2
    [(2, 2), (3, 3), (109, 1), (29047611873442575647497758179, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, prime_29047611873442575647497758179⟩)
    (by decide +kernel)

theorem prime_255515944373312847190720520512484175977 : Nat.Prime 255515944373312847190720520512484175977 :=
  Pratt.prime_of_check 255515944373312847190720520512484175977 3
    [(2, 3), (7, 2), (11, 1), (1627, 1), (2657, 1), (4423, 1), (41201, 1), (96557, 1), (7240687, 1), (107590001, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_96557, prime_7240687, prime_107590001⟩)
    (by decide +kernel)

theorem prime_205115282021455665897114700593932402728804164701536103180137503955397371 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 :=
  Pratt.prime_of_check 205115282021455665897114700593932402728804164701536103180137503955397371 10
    [(2, 1), (3, 1), (5, 1), (29, 2), (31, 1), (7723, 1), (132896956044521568488119, 1), (255515944373312847190720520512484175977, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_132896956044521568488119, prime_255515944373312847190720520512484175977⟩)
    (by decide +kernel)

theorem prime_115792089237316195423570985008687907852837564279074904382605163141518161494337 : Nat.Prime 115792089237316195423570985008687907852837564279074904382605163141518161494337 :=
  Pratt.prime_of_check 115792089237316195423570985008687907852837564279074904382605163141518161494337 7
    [(2, 6), (3, 1), (149, 1), (631, 1), (107361793816595537, 1), (174723607534414371449, 1), (341948486974166000522343609283189, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_107361793816595537, prime_174723607534414371449, prime_341948486974166000522343609283189⟩)
    (by decide +kernel)

theorem prime_115792089237316195423570985008687907853269984665640564039457584007908834671663 : Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 :=
  Pratt.prime_of_check 115792089237316195423570985008687907853269984665640564039457584007908834671663 3
    [(2, 1), (3, 1), (7, 1), (13441, 1), (205115282021455665897114700593932402728804164701536103180137503955397371, 1)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_205115282021455665897114700593932402728804164701536103180137503955397371⟩)
    (by decide +kernel)

/-- The secp256k1 field size `p = 2^256 - 2^32 - 977` is prime. -/
theorem prime_p : Nat.Prime (2 ^ 256 - 2 ^ 32 - 977) :=
  prime_115792089237316195423570985008687907853269984665640564039457584007908834671663

/-- The secp256k1 group order `n` is prime. -/
theorem prime_n : Nat.Prime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 :=
  prime_115792089237316195423570985008687907852837564279074904382605163141518161494337

end Taproot.Primes
