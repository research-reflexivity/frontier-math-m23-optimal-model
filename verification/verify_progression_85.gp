\\ Exact universal M23 specialization certificate for T = 83 (mod 85).
\\
\\ External theorem: HJLPPZ prove that the splitting field of the exact
\\ polynomial loaded below has Galois group M23 over Q(T).

read("../data/Fint_coefficients_Z.gp");

check(condition, message) = if(!condition, error(message));

factor_degrees(f, p) =
{
  my(A = factor(Mod(1,p) * f));
  concat(vector(matsize(A)[1], i,
    vector(A[i,2], j, poldegree(lift(A[i,1])))));
};

verify_progression() =
{
  my(base, primitive, shifted, f5, f17, q17, expected5, expected17,
     maximal_orders, primes = [5,17]);

  base = subst(F, T, 83);
  check(poldegree(base, V) == 23, "base specialization has wrong degree");
  primitive = base / content(base);
  check(content(primitive) == 1, "primitive normalization failed");

  f5 = subst(primitive, V, x);
  f17 = f5;
  expected5 = [1,2,4,8,8];
  expected17 = [23];
  check(factor_degrees(f5, 5) == expected5,
        "unexpected order-8 factorization modulo 5");
  check(factor_degrees(f17, 17) == expected17,
        "specialization is not irreducible modulo 17");
  check(polisirreducible(Mod(1,17) * f17),
        "Rabin irreducibility check failed modulo 17");
  q17 = Mod(1,17) * f17;
  check(lift(Mod(x,q17)^(17^23)) == x,
        "Rabin Frobenius identity failed modulo 17");
  check(poldegree(gcd(q17,lift(Mod(x,q17)^17)-x)) == 0,
        "Rabin proper-subfield exclusion failed modulo 17");

  for(i = 1, #primes,
    my(p = primes[i]);
    shifted = subst(F, T, 83 + 85*n);
    check(Mod(1,p)*shifted == Mod(1,p)*base,
          Str("universal progression congruence failed modulo ", p));
    check(poldegree(Mod(1,p)*base, V) == 23,
          Str("degree drops modulo ", p));
    check(poldegree(gcd(Mod(1,p)*base, deriv(Mod(1,p)*base,V)),V) == 0,
          Str("reduction is not squarefree modulo ", p));
  );

  maximal_orders = [443520,40320,40320,20160,7920,5760,253];
  check(sum(i=1,#maximal_orders,maximal_orders[i]%23 == 0) == 1,
        "unexpected maximal subgroup order divisible by 23");
  check(maximal_orders[7] == 23*11 && maximal_orders[7]%2 == 1,
        "23:11 order exclusion failed");

  check((22013-2)%319 == 0 && (22013-83)%85 == 0,
        "common-subprogression CRT representative is wrong");
  check(319*85 == 27115, "common-subprogression modulus is wrong");

  print("PASS_HJLPPZ_PROGRESSION_85_CERTIFICATE");
  print("F(83+85*n,V) is squarefree modulo 5 and 17");
  print("factor_degrees_mod_5=[1,2,4,8,8] cycle_order=8");
  print("factor_degrees_mod_17=[23] cycle_order=23");
  print("generic_M23_plus_maximal_subgroup_exclusion_implies_specialized_M23");
  print("intersection_with_2_mod_319=22013_mod_27115");
};

verify_progression();
