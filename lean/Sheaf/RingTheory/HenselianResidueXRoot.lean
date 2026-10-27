/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Lifting the zero of a polynomial whose reduction is X

Source: Stacks Project, Algebra, Tag 04GG, simple-root characterization;
the reciprocal-polynomial reduction in the proof of
`lem-per-henselian-simple-root-stability`.
(blueprint: lem-per-henselian-residue-X-root)
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

namespace HenselianLocalRing

/-- A polynomial reducing to `X` has a simple root in the maximal ideal.

Source: Stacks Project, Algebra, Tag 04GG (simple-root lifting), with the
explicit reciprocal reduction of the simple-root stability argument.
(blueprint: lem-per-henselian-residue-X-root)

Proof: Put `p = H(1-X)` and `N = natDegree H + 1`. Its constant coefficient
`H(1)` has residue one and is a unit `u`. The polynomial
`Q = u⁻¹ * reflect N p` has degree at most `N` and coefficient one at `N`,
so is monic. Its reduction is `X^N - X^(N-1)`, whose root one is simple
in every characteristic. Monic Hensel lifting supplies a root `y` reducing
to one. Thus `y` is a unit. Reflection gives `H(1-y⁻¹)=0`; the element
`z = 1-y⁻¹` reduces to zero. Finally, reduction of `H'` is one, so
`H'(z)` reduces to one and is a unit. -/
theorem exists_simple_root_of_map_eq_X
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (H : R[X]) (hH : H.map (residue R) = X) :
    ∃ z : R, z ∈ maximalIdeal R ∧ H.IsRoot z ∧ IsUnit (H.derivative.eval z) := by
  classical
  have hHone : residue R (H.eval 1) = 1 := by
    rw [← eval_map_apply, hH]
    simp
  obtain ⟨u, hu⟩ := (residue_ne_zero_iff_isUnit (H.eval 1)).mp (by
    rw [hHone]
    exact one_ne_zero)
  have hu_res : residue R (u : R) = 1 := by rw [hu, hHone]
  have hu_inv : residue R (↑(u⁻¹) : R) = 1 := by
    calc
      residue R (↑(u⁻¹) : R) = residue R (↑(u⁻¹) : R) * residue R (u : R) := by
        rw [hu_res, mul_one]
      _ = 1 := by rw [← map_mul]; simp
  let p : R[X] := H.comp (1 - X)
  let N := H.natDegree + 1
  have hpdeg : p.natDegree ≤ N := by
    calc
      p.natDegree ≤ H.natDegree * (1 - (X : R[X])).natDegree := natDegree_comp_le
      _ ≤ H.natDegree * 1 := Nat.mul_le_mul_left _ (by
        exact (natDegree_sub_le _ _).trans (by simp))
      _ ≤ N := by dsimp [N]; omega
  let q := p.reflect N
  let Q := C (↑(u⁻¹) : R) * q
  have hQmonic : Q.Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one N
    · calc
        Q.natDegree ≤ (C (↑(u⁻¹) : R)).natDegree + q.natDegree := natDegree_mul_le
        _ = q.natDegree := by simp
        _ ≤ max N p.natDegree := natDegree_reflect_le
        _ = N := max_eq_left hpdeg
    · simp only [Q, coeff_C_mul, q, coeff_reflect, revAt_le (le_refl N), Nat.sub_self]
      have hpzero : p.coeff 0 = H.eval 1 := by
        simpa [p] using (coeff_zero_eq_eval_zero p)
      rw [hpzero, ← hu]
      simp
  have hpmap : p.map (residue R) = 1 - X := by simp [p, map_comp, hH]
  have hQmap : Q.map (residue R) = X ^ N - X ^ H.natDegree := by
    simp only [Q, Polynomial.map_mul, map_C, hu_inv, C_1, one_mul, q,
      ← reflect_map, hpmap, reflect_sub, reflect_one]
    rw [show (X : (ResidueField R)[X]) = X ^ 1 by simp, reflect_monomial,
      revAt_le (by dsimp [N]; omega)]
    simp [N]
  have hQroot : aeval (1 : ResidueField R) Q = 0 := by
    rw [aeval_def, ← eval_map]
    simp [hQmap, N]
  have hQderiv : aeval (1 : ResidueField R) Q.derivative ≠ 0 := by
    rw [aeval_def, ← eval_map, ResidueField.algebraMap_eq, ← derivative_map, hQmap]
    simp [N, derivative_X_pow]
  have lift := ((HenselianLocalRing.TFAE R).out 0 1).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨y, hy, hy_res⟩ := lift Q hQmonic 1 hQroot hQderiv
  obtain ⟨w, hw⟩ := (residue_ne_zero_iff_isUnit y).mp (by rw [hy_res]; exact one_ne_zero)
  have hw_res : residue R (w : R) = 1 := by rw [hw, hy_res]
  have hw_inv : residue R (↑(w⁻¹) : R) = 1 := by
    calc
      residue R (↑(w⁻¹) : R) = residue R (↑(w⁻¹) : R) * residue R (w : R) := by
        rw [hw_res, mul_one]
      _ = 1 := by rw [← map_mul]; simp
  let z : R := 1 - ↑(w⁻¹)
  have hzres : residue R z = 0 := by simp [z, hw_inv]
  have hqroot : q.eval y = 0 := by
    have h := congrArg (fun r : R ↦ (u : R) * r) hy
    simpa [IsRoot, Q, eval_mul, eval_C, mul_assoc] using h
  have hzroot : H.IsRoot z := by
    let : Invertible (↑(w⁻¹) : R) := ⟨↑w, by simp, by simp⟩
    have h := (eval₂_reflect_eq_zero_iff (RingHom.id R) (↑(w⁻¹) : R) N p hpdeg).mp
      (by simpa [q, hw] using hqroot)
    simpa [p, z, IsRoot] using h
  refine ⟨z, (residue_eq_zero_iff z).mp hzres, hzroot, ?_⟩
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [← eval_map_apply, ← derivative_map, hH]
  simp

end HenselianLocalRing
