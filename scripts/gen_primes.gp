\\ Generates Taproot/Primes.lean: Pratt certificates for the secp256k1 field size p
\\ and group order n. Usage (from the repo root):
\\   gp -q scripts/gen_primes.gp < /dev/null > Taproot/Primes.lean
\\ The two readable aliases prime_p / prime_n at the end of Primes.lean are added by hand.
default(parisizemax, 2^30);
certs = Map();
cert(p) = {
  my(f, a);
  if (p < 2^16 || mapisdefined(certs, p), return);
  f = factor(p - 1);
  for (i = 1, #f~, if (!isprime(f[i,1]), error("not prime: ", f[i,1])));
  a = 2;
  while (Mod(a,p)^(p-1) != 1 || sum(i = 1, #f~, Mod(a,p)^((p-1)/f[i,1]) == 1) > 0, a++);
  mapput(certs, p, [a, f]);
  for (i = 1, #f~, cert(f[i,1]));
}
P = 2^256 - 2^32 - 977;
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141;
cert(P); cert(N);
M = Mat(certs);
print("import Taproot.Pratt\n");
print("/-!\n# Primality of the secp256k1 field size `p` and group order `n`\n");
print("Pratt certificates generated with PARI/GP and checked here by the Lean kernel.");
print("Primes below 2^16 are proven by `norm_num`.\n-/\n");
print("namespace Secp256k1.Primes\n");
{
for (i = 1, #M~,
  my(p = M[i,1], a = M[i,2][1], f = M[i,2][2], fs = "", pf = "");
  for (j = 1, #f~,
    fs = Str(fs, if (j > 1, ", ", ""), "(", f[j,1], ", ", f[j,2], ")");
    pf = Str(pf, if (j > 1, ", ", ""), if (f[j,1] < 2^16, "by norm_num", Str("prime_", f[j,1]))));
  print("theorem prime_", p, " : Nat.Prime ", p, " :=");
  print("  Pratt.prime_of_check ", p, " ", a);
  print("    [", fs, "]");
  print("    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]");
  print("        exact ⟨", pf, "⟩)");
  print("    (by decide +kernel)\n"));
}
print("end Secp256k1.Primes");
