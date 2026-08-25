import M23Certificate.Data
import M23Certificate.FiniteFieldIrreducibility
import M23Certificate.Specialization

open Polynomial

namespace M23Certificate

open Data

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

local instance fact_prime_31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

theorem p7Monic_monic : p7Monic.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 23
  · simpa [p7Monic, fromCoefficients, toF31, p7MonicCoefficients] using
      Coefficients.natDegree_realize_le (toF31 p7MonicCoefficients)
  · norm_num [p7Monic, fromCoefficients, toF31, p7MonicCoefficients,
      Coefficients.coeff_realize]

theorem p7Monic_natDegree : p7Monic.natDegree = 23 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simpa [p7Monic, fromCoefficients, toF31, p7MonicCoefficients] using
      Coefficients.natDegree_realize_le (toF31 p7MonicCoefficients)
  · norm_num [p7Monic, fromCoefficients, toF31, p7MonicCoefficients,
      Coefficients.coeff_realize]

theorem p7Monic_eq_unit_mul : p7Monic = C (20 : F31) * p7 := by
  have hraw : toF31 p7MonicCoefficients =
      Coefficients.scale (20 : F31) (toF31 p7Coefficients) := by
    decide
  change Coefficients.realize (toF31 p7MonicCoefficients) =
    C (20 : F31) * Coefficients.realize (toF31 p7Coefficients)
  rw [hraw, Coefficients.realize_scale]

theorem p7_eq_specialization : P.map (evalRingHom (7 : F31)) = p7 := by
  unfold P p7 fromCoefficients
  rw [Coefficients.map_realize]
  apply congrArg Coefficients.realize
  simp only [List.map_map]
  change List.map (fun row => Polynomial.eval (7 : F31)
    (Coefficients.realize (toF31 row))) coefficientsWThenT = toF31 p7Coefficients
  simp_rw [Coefficients.eval_realize]
  decide

private theorem frobenius_steps_raw : ∀ i : Fin 23,
    Coefficients.expand 31 (frobeniusRemainderRaw i) =
      Coefficients.add
        (Coefficients.mul (frobeniusQuotientRaw i) (toF31 p7MonicCoefficients))
        (frobeniusRemainderRaw (i + 1)) ++ List.replicate 30 0 := by
  decide

private theorem realize_expand_31_pow (a : List F31) :
    Coefficients.realize (Coefficients.expand 31 a) =
      Coefficients.realize a ^ 31 := by
  induction a with
  | nil => simp [Coefficients.expand, Coefficients.realize]
  | cons a as ih =>
      rw [Coefficients.realize_expand_cons 31 (by norm_num)]
      simp only [Coefficients.realize]
      rw [add_pow_char, mul_pow, ih, ← C_pow]
      have ha : a ^ 31 = a := ZMod.pow_card a
      rw [ha]

theorem frobenius_step (i : Fin 23) :
    frobeniusRemainder i ^ 31 =
      frobeniusQuotient i * p7Monic + frobeniusRemainder (i + 1) := by
  have h := congrArg Coefficients.realize (frobenius_steps_raw i)
  rw [Coefficients.realize_append_replicate_zero] at h
  simpa [frobeniusRemainder, frobeniusQuotient, p7Monic, fromCoefficients,
    realize_expand_31_pow, Coefficients.realize_mul,
    Coefficients.realize_add] using h

theorem frobenius_initial : frobeniusRemainder 0 = X := by
  norm_num [frobeniusRemainder, frobeniusRemainderRaw,
    frobeniusRemainderCoefficients, toF31, fromCoefficients, Coefficients.realize]

theorem frobenius_final : frobeniusRemainder 23 = X := by
  norm_num [frobeniusRemainder, frobeniusRemainderRaw,
    frobeniusRemainderCoefficients, toF31, fromCoefficients, Coefficients.realize]

theorem card_F31 : Nat.card F31 = 31 := by
  norm_num [Nat.card_eq_fintype_card]

theorem p7Monic_frobenius_dvd :
    p7Monic ∣ X ^ (Nat.card F31) ^ 23 - X := by
  have h := dvd_frobenius_of_chain p7Monic (Nat.card F31) 23
    frobeniusRemainder frobeniusQuotient frobenius_initial
    (by
      intro i hi
      rw [card_F31]
      exact frobenius_step ⟨i, hi⟩)
  rw [frobenius_final] at h
  exact h

private theorem bezout_raw :
    Coefficients.add
      (Coefficients.mul (toF31 bezoutACoefficients) (toF31 p7MonicCoefficients))
      (Coefficients.mul (toF31 bezoutBCoefficients) (toF31 frobeniusOneCoefficients)) =
        toF31 bezoutIdentityCoefficients := by
  decide

private theorem frobenius_one_realize :
    Coefficients.realize (toF31 frobeniusOneCoefficients) = X ^ 31 - X := by
  have h30 : (30 : F31) = -1 := by decide
  norm_num [frobeniusOneCoefficients, toF31, Coefficients.realize]
  rw [h30, map_neg, map_one]
  ring

private theorem bezout_identity_realize :
    Coefficients.realize (toF31 bezoutIdentityCoefficients) = 1 := by
  norm_num [bezoutIdentityCoefficients, toF31, Coefficients.realize]

theorem p7Monic_bezout :
    bezoutA * p7Monic + bezoutB * (X ^ 31 - X) = 1 := by
  have h := congrArg Coefficients.realize bezout_raw
  have hpoly :
      bezoutA * p7Monic +
        bezoutB * Coefficients.realize (toF31 frobeniusOneCoefficients) =
          Coefficients.realize (toF31 bezoutIdentityCoefficients) := by
    simpa [bezoutA, bezoutB, p7Monic, fromCoefficients,
      Coefficients.realize_mul, Coefficients.realize_add] using h
  simpa only [frobenius_one_realize, bezout_identity_realize] using hpoly

theorem p7Monic_coprime_frobenius : IsCoprime p7Monic (X ^ 31 - X) :=
  ⟨bezoutA, bezoutB, p7Monic_bezout⟩

theorem p7Monic_irreducible : Irreducible p7Monic := by
  apply irreducible_of_prime_degree_frobenius (K := F31) (f := p7Monic)
    (n := 23) (by norm_num) p7Monic_natDegree
  · exact p7Monic_frobenius_dvd
  · rw [card_F31]
    exact p7Monic_coprime_frobenius

theorem p7_irreducible : Irreducible p7 := by
  have hunit : IsUnit (C (20 : F31) : F31[X]) := by
    apply isUnit_C.mpr
    refine ⟨⟨20, 14, ?_, ?_⟩, rfl⟩ <;> decide
  have hirreducible := p7Monic_irreducible
  rw [p7Monic_eq_unit_mul] at hirreducible
  exact (irreducible_isUnit_mul hunit).mp hirreducible

private theorem primitive_bezout_raw :
    Coefficients.add
      (Coefficients.mul (toF31 primitiveACoefficients)
        (toF31 (coefficientsWThenT.getD 0 [])))
      (Coefficients.mul (toF31 primitiveBCoefficients)
        (toF31 (coefficientsWThenT.getD 1 []))) =
        toF31 primitiveIdentityCoefficients := by
  decide

theorem primitive_bezout :
    primitiveA * P.coeff 0 + primitiveB * P.coeff 1 = 1 := by
  have h := congrArg Coefficients.realize primitive_bezout_raw
  simpa [primitiveA, primitiveB, P, fromCoefficients, coefficientsWThenT,
    primitiveIdentityCoefficients, toF31, Coefficients.coeff_realize,
    Coefficients.realize_mul, Coefficients.realize_add, Coefficients.realize] using h

/-- First requested certificate component: primitivity in `F_31[T][W]`. -/
theorem P_primitive : P.IsPrimitive := by
  intro r hr
  rw [isUnit_iff_dvd_one, ← primitive_bezout]
  rw [C_dvd_iff_dvd_coeff] at hr
  exact (dvd_mul_of_dvd_right (hr 0) primitiveA).add
    (dvd_mul_of_dvd_right (hr 1) primitiveB)

theorem P_natDegree : P.natDegree = 23 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simpa [P, fromCoefficients, coefficientsWThenT] using
      Coefficients.natDegree_realize_le
        (coefficientsWThenT.map fun row => fromCoefficients (toF31 row))
  · intro h
    have hcoeff := congrArg (fun q : F31[X] => q.coeff 4) h
    norm_num [P, fromCoefficients, coefficientsWThenT, toF31,
      Coefficients.coeff_realize] at hcoeff

theorem p7_natDegree : p7.natDegree = 23 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simpa [p7, fromCoefficients, p7Coefficients, toF31] using
      Coefficients.natDegree_realize_le (toF31 p7Coefficients)
  · norm_num [p7, fromCoefficients, p7Coefficients, toF31,
      Coefficients.coeff_realize]
    decide

/-- Second requested certificate component: specialization at T=7 preserves W-degree. -/
theorem specialization_preserves_W_degree :
    (P.map (evalRingHom (7 : F31))).natDegree = P.natDegree := by
  rw [p7_eq_specialization, p7_natDegree, P_natDegree]

/-- Fourth requested component: the proved specialization lemma applied to P. -/
theorem P_irreducible : Irreducible P := by
  apply irreducible_of_primitive_of_specialization
    (R := F31[X]) (S := F31) (evalRingHom (7 : F31)) P
    P_primitive specialization_preserves_W_degree
  simpa only [p7_eq_specialization] using p7_irreducible

end M23Certificate
