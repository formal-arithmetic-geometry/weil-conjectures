/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionPartialLocalFlat

/-!
# Flatness of relative global complete intersections

A relative global complete intersection is flat over its coefficient ring.

## Implementation details

At each maximal ideal of the quotient, the localized quotient is flat over `R` by the
partial-local flatness result with all equations, and
`Module.flat_of_isLocalized_maximal` checks flatness on these localizations without localizing
`R`. The zero quotient has no maximal ideals.

## References

* [Stacks, Tag 00SW]
-/

@[expose] public section

universe u

namespace Algebra

/-- A polynomial quotient that is a relative global complete intersection is flat over
its coefficient ring. -/
theorem flat_of_isRelativeGlobalCompleteIntersection_quotient
    (R : Type u) [CommRing R] (n c : ℕ) (relations : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation relations) :
    RingHom.Flat
      (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations))) := by
  let P := MvPolynomial (Fin n) R
  let I : Ideal P := Ideal.span (Set.range relations)
  let S := P ⧸ I
  rw [RingHom.flat_algebraMap_iff]
  apply Module.flat_of_isLocalized_maximal S S
    (fun q ↦ Localization.AtPrime q) (fun q ↦ Algebra.linearMap S _)
  intro q hq
  let q' : PrimeSpectrum P := PrimeSpectrum.comap (Ideal.Quotient.mk I) ⟨q, inferInstance⟩
  let L := Localization.AtPrime q'.asIdeal
  let Q := L ⧸ I.map (algebraMap P L)
  have hfull : relations '' {j : Fin c | j.val < c} = Set.range relations := by
    simp
  have hflat : Module.Flat R Q := by
    have ht := relativeGlobalCompleteIntersection_partial_local_flat R n c relations h
      ⟨q, inferInstance⟩ c le_rfl
    change Module.Flat R
      (L ⧸ Ideal.map (algebraMap P L) (Ideal.span (relations '' {j : Fin c | j.val < c})))
      at ht
    rw [hfull] at ht
    exact ht
  have hmon : Algebra.algebraMapSubmonoid S q'.asIdeal.primeCompl = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q
  have : IsLocalization q.primeCompl Q := by
    rw [← hmon]
    infer_instance
  have : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R P Q, IsScalarTower.algebraMap_apply R P S,
      ← IsScalarTower.algebraMap_apply P S Q]
  let e := IsLocalization.algEquiv q.primeCompl Q (Localization.AtPrime q)
  exact Module.Flat.of_linearEquiv (e.symm.restrictScalars R).toLinearEquiv

end Algebra
