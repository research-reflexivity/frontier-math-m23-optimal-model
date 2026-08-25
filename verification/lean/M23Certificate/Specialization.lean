import Mathlib

open Polynomial

namespace M23Certificate

/-!
The form of specialization used by the certificate.  The degree hypothesis rules
out a factor becoming constant after specialization, and primitivity then turns
an already-constant factor into a unit over the coefficient ring.
-/
theorem irreducible_of_primitive_of_specialization
    {R S : Type*} [CommRing R] [IsDomain R] [Field S]
    (phi : R →+* S) (f : R[X])
    (hprimitive : f.IsPrimitive)
    (hdegree : (f.map phi).natDegree = f.natDegree)
    (hirreducible : Irreducible (f.map phi)) :
    Irreducible f := by
  refine ⟨?_, ?_⟩
  · intro hfunit
    exact hirreducible.not_isUnit (hfunit.map (Polynomial.mapRingHom phi))
  · intro a b hab
    have hfmap_ne : f.map phi ≠ 0 := hirreducible.ne_zero
    have hf_ne : f ≠ 0 := fun hf ↦ hfmap_ne (by simp [hf])
    have ha_ne : a ≠ 0 := fun ha ↦ hf_ne (by simp [hab, ha])
    have hb_ne : b ≠ 0 := fun hb ↦ hf_ne (by simp [hab, hb])
    have hmapped : a.map phi * b.map phi = f.map phi := by
      simp [hab]
    rcases hirreducible.isUnit_or_isUnit hmapped.symm with haunit | hbunit
    · left
      have hma_ne : a.map phi ≠ 0 := fun h ↦ hfmap_ne (by rw [← hmapped, h, zero_mul])
      have hmb_ne : b.map phi ≠ 0 := fun h ↦ hfmap_ne (by rw [← hmapped, h, mul_zero])
      have hsum : a.natDegree + b.natDegree = f.natDegree := by
        simpa [hab] using (natDegree_mul ha_ne hb_ne).symm
      have hle : f.natDegree ≤ b.natDegree := by
        rw [← hdegree, ← hmapped, natDegree_mul hma_ne hmb_ne,
          natDegree_eq_zero_of_isUnit haunit, zero_add]
        exact natDegree_map_le
      have hadeg : a.natDegree = 0 := by omega
      rw [eq_C_of_natDegree_eq_zero hadeg]
      exact (isUnit_C.mpr <| hprimitive _ <| by
        rw [← eq_C_of_natDegree_eq_zero hadeg]
        exact ⟨b, hab⟩)
    · right
      have hma_ne : a.map phi ≠ 0 := fun h ↦ hfmap_ne (by rw [← hmapped, h, zero_mul])
      have hmb_ne : b.map phi ≠ 0 := fun h ↦ hfmap_ne (by rw [← hmapped, h, mul_zero])
      have hsum : a.natDegree + b.natDegree = f.natDegree := by
        simpa [hab] using (natDegree_mul ha_ne hb_ne).symm
      have hle : f.natDegree ≤ a.natDegree := by
        rw [← hdegree, ← hmapped, natDegree_mul hma_ne hmb_ne,
          natDegree_eq_zero_of_isUnit hbunit, add_zero]
        exact natDegree_map_le
      have hbdeg : b.natDegree = 0 := by omega
      rw [eq_C_of_natDegree_eq_zero hbdeg]
      exact (isUnit_C.mpr <| hprimitive _ <| by
        rw [← eq_C_of_natDegree_eq_zero hbdeg]
        exact ⟨a, by simpa [mul_comm] using hab⟩)

end M23Certificate
