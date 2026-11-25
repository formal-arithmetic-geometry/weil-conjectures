/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.DVRCompletionGenericFiber
import WeilConjectures.RingTheory.CompletionClosedFiber

/-!
# Regularity of completion maps for characteristic-zero discrete valuation rings

The completion map `A ⟶ Â` of a discrete valuation ring `A` at its maximal ideal is regular if
the fraction field of `A` has characteristic zero.

## Implementation details

The map is flat, and its only fibres are the generic fibre
(`AdicCompletion.isGeometricallyRegular_genericFiber_of_isDiscreteValuationRing_of_charZero`)
and the closed fibre (`AdicCompletion.isGeometricallyRegular_closedFiber`), both geometrically
regular.

## References

* Stacks Project, More on Algebra, Proposition Tag 07PX, proof of (3) and (4).
* Stacks Project, Algebra, Lemma Tag 00PD.
-/

@[expose] public section

universe u v

namespace AdicCompletion

/-- The completion map `A ⟶ Â` of a discrete valuation ring `A` at its maximal ideal is regular
if the fraction field of `A` has characteristic zero. -/
theorem isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] :
    RingHom.IsRegular (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  classical
  rw [RingHom.IsRegular, toAlgebra_algebraMap]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, ?_⟩
  intro p hp
  by_cases h : p = ⊥
  · subst p
    exact isGeometricallyRegular_genericFiber_of_isDiscreteValuationRing_of_charZero A K
  · have : p.IsMaximal := IsPrime.to_maximal_ideal h
    have heq : p = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
    subst p
    exact isGeometricallyRegular_closedFiber A

end AdicCompletion
