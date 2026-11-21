/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.LinearAlgebra.IdempotentCharpoly
import WeilConjectures.LinearAlgebra.IdempotentCharpolyLocalCharpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.LocalProperties.Submodule

/-! # Idempotent leading coefficient of a summand determinant

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph, with the
finite-projective local calculation made explicit.
-/

@[expose] public section

universe u v

namespace Matrix

/-- The leading coefficient of the determinant on a commuting idempotent summand
is itself idempotent.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph. -/
theorem isIdempotentElem_idempotentCharpoly_leadingCoeff
    {A : Type u} [CommRing A] {n : Type v} [Fintype n] [DecidableEq n]
    (T P : Matrix n n A) (hP : P * P = P) (hTP : T * P = P * T) :
    IsIdempotentElem (idempotentCharpoly T P).leadingCoeff := by
  obtain ⟨r, f, hspan, hchar⟩ := exists_standardCover_idempotentCharpoly_eq_charpoly T P hP hTP
  have hlocal (i : Fin r) :
      IsIdempotentElem (algebraMap A (Localization.Away (f i))
        (idempotentCharpoly T P).leadingCoeff) := by
    obtain ⟨d, U, hU⟩ := hchar i
    let q := (idempotentCharpoly T P).map (algebraMap A (Localization.Away (f i)))
    have hmonic : q.Monic := by rw [show q = U.charpoly from hU]; exact U.charpoly_monic
    have hle : q.natDegree ≤ (idempotentCharpoly T P).natDegree := Polynomial.natDegree_map_le
    have hc : algebraMap A (Localization.Away (f i)) (idempotentCharpoly T P).leadingCoeff =
        q.coeff (idempotentCharpoly T P).natDegree := by
      rw [Polynomial.leadingCoeff, Polynomial.coeff_map]
    rw [hc]
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      simp [IsIdempotentElem]
    · rw [← heq, hmonic.coeff_natDegree]
      simp [IsIdempotentElem]
  have hz : (idempotentCharpoly T P).leadingCoeff *
      (idempotentCharpoly T P).leadingCoeff - (idempotentCharpoly T P).leadingCoeff = 0 := by
    apply Module.eq_zero_of_isLocalized_span (Set.range f) hspan
      (fun a : {a // a ∈ Set.range f} ↦ Localization.Away (a : A))
      (fun a ↦ Algebra.linearMap A (Localization.Away (a : A)))
    rintro ⟨_, ⟨i, rfl⟩⟩
    change algebraMap A (Localization.Away (f i))
      ((idempotentCharpoly T P).leadingCoeff * (idempotentCharpoly T P).leadingCoeff -
        (idempotentCharpoly T P).leadingCoeff) = 0
    rw [map_sub, map_mul]
    exact sub_eq_zero.mpr (hlocal i)
  exact sub_eq_zero.mp hz

end Matrix
