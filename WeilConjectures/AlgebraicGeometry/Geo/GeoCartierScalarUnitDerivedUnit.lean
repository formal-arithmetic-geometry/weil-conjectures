/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The ordinary derived-unit form of a Cartier scalar unit
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The Cartier scalar-unit predicate is the derived-unit universal property
for the exact restriction functor. -/
theorem geoCartierScalarUnit_derivedUnit
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) (Z : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))
    (H : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj H)
    (h : GeoCartierScalarUnit φ Z F H η) :
    (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).DerivedUnit F H η := by
  unfold GeoCartierScalarUnit at h
  simpa only [Functor.DerivedUnit, Sheaf.IsDerivedBaseChange,
    Sheaf.derivedRestrictScalars, Category.assoc] using h

end AlgebraicGeometry.ProEtale
