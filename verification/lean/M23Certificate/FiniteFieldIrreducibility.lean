import Mathlib.FieldTheory.Finite.Extension

open Polynomial

namespace M23Certificate

/-! A proof-producing Frobenius chain.  The concrete certificate supplies the
remainders `r i` and quotients `s i`; each checked identity
`(r i)^q = (s i) f + r (i+1)` is a compact witness for one modular reduction. -/
theorem dvd_frobenius_of_chain {R : Type*} [CommRing R]
    (f : R[X]) (q n : ℕ) (r s : ℕ → R[X])
    (hzero : r 0 = X)
    (hstep : ∀ i < n, r i ^ q = s i * f + r (i + 1)) :
    f ∣ X ^ q ^ n - r n := by
  have hchain : ∀ i ≤ n, f ∣ X ^ q ^ i - r i := by
    intro i hi
    induction i with
    | zero => simp [hzero]
    | succ i ih =>
        have hpow : f ∣ (X ^ q ^ i) ^ q - (r i) ^ q :=
          (ih (Nat.le_of_succ_le hi)).trans (sub_dvd_pow_sub_pow _ _ _)
        have hreduce : f ∣ (r i) ^ q - r (i + 1) := by
          refine ⟨s i, ?_⟩
          rw [hstep i (Nat.lt_of_succ_le hi)]
          ring
        simpa [Nat.pow_succ, pow_mul] using hpow.add hreduce
  exact hchain n le_rfl

private theorem degree_one_dvd_frobenius {K : Type*} [Field K] [Fintype K]
    {g : K[X]} (hdegree : g.natDegree = 1) :
    g ∣ X ^ Nat.card K - X := by
  have hg_ne : g ≠ 0 := by
    intro hg
    simp [hg] at hdegree
  have hdegree' : g.degree = 1 := by
    rw [degree_eq_natDegree hg_ne, hdegree]
    simp
  obtain ⟨a, ha⟩ := exists_root_of_degree_eq_one hdegree'
  have hlinear : X - C a ∣ g := dvd_iff_isRoot.mpr ha
  have hassociated : Associated (X - C a) g :=
    associated_of_dvd_of_natDegree_le hlinear hg_ne (by simp [hdegree])
  apply hassociated.dvd_iff_dvd_left.mp
  apply dvd_iff_isRoot.mpr
  have ha_pow : a ^ Fintype.card K = a := FiniteField.pow_card a
  simp [IsRoot, ha_pow]

/-- Prime-degree form of the finite-field irreducibility criterion.  For prime
`n`, the two certificate obligations are the final Frobenius congruence and the
absence of linear factors, expressed by coprimality with `X^q - X`. -/
theorem irreducible_of_prime_degree_frobenius
    {K : Type*} [Field K] [Fintype K]
    {f : K[X]} {n : ℕ}
    (hn : n.Prime)
    (hdegree : f.natDegree = n)
    (hfinal : f ∣ X ^ (Nat.card K) ^ n - X)
    (hlinear : IsCoprime f (X ^ Nat.card K - X)) :
    Irreducible f := by
  have hf_ne : f ≠ 0 := by
    intro hf
    apply hn.ne_zero
    rw [← hdegree]
    simp [hf]
  have hfactor_dvd : f.factor ∣ f :=
    factor_dvd_of_natDegree_ne_zero (hdegree.trans_ne hn.ne_zero)
  have hfactor_irreducible : Irreducible f.factor := irreducible_factor f
  have hfactor_final : f.factor ∣ X ^ (Nat.card K) ^ n - X :=
    hfactor_dvd.trans hfinal
  have hfactor_degree_dvd : f.factor.natDegree ∣ n :=
    hfactor_irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hfactor_final
  rcases (Nat.dvd_prime hn).mp hfactor_degree_dvd with hone | hnfull
  · have hfactor_linear : f.factor ∣ X ^ Nat.card K - X :=
      degree_one_dvd_frobenius hone
    exact (hfactor_irreducible.not_isUnit
      (hlinear.isUnit_of_dvd' hfactor_dvd hfactor_linear)).elim
  · exact (associated_of_dvd_of_natDegree_le hfactor_dvd hf_ne
      (by rw [hdegree, hnfull])).irreducible hfactor_irreducible

end M23Certificate
