/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.GeometricRegularityFieldIso

/-!
# Transporting geometric regularity along a choice of fraction field

Geometric regularity of the generic fibre of an `A`-algebra does not depend on the chosen model of
the fraction field of `A`.

## References

* [Stacks, Tag 07PS]
-/

@[expose] public section
universe u
/-- Geometric regularity of the generic fibre over a Noetherian domain `A` transfers from the
canonical fraction field `(⊥ : Ideal A).ResidueField` to any fraction field `K` of `A`. -/
theorem fractionField_geometricallyRegular_tensorProduct_transport
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (C : Type u) [CommRing C] [Algebra A C]
    (h : Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).Fiber C)) :
    Algebra.IsGeometricallyRegular K (TensorProduct A K C) := by
  let e : (⊥ : Ideal A).ResidueField ≃ₐ[A] K :=
    IsLocalization.algEquiv (nonZeroDivisors A) _ _
  let E := Algebra.TensorProduct.congr e (AlgEquiv.refl : C ≃ₐ[A] C)
  apply Algebra.isGeometricallyRegular_of_fieldIso e.toRingEquiv E.toRingEquiv ?_ h
  intro x y
  simp only [Algebra.smul_def, map_mul]
  congr 1
