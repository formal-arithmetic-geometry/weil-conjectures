/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

/-! # Canonical current finite-coefficient six-functor datum

The operations are the published small-etale constructions; only the finite-Tor
stability assumptions are recorded here.  Compact-support stability is required
only when the target is of finite type over the field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace WeilConjectures

/-- The étale derived category of `Λ`-modules on `X`. -/
abbrev CurrentDerived (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  AlgebraicGeometry.Etale.DerivedCategoryModule Λ X

/-- The bounded constructible objects of finite Tor amplitude. -/
abbrev currentCtf (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    ObjectProperty (CurrentDerived Λ X) :=
  AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleFiniteTor Λ X

/-- The derived pullback along `f`. -/
noncomputable abbrev currentPull
    {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CurrentDerived Λ Y ⥤ CurrentDerived Λ X :=
  L((f)^*[ModuleCat.{u + 1} Λ])

/-- The derived compact-support direct image along `f`. -/
noncomputable abbrev currentShriek
    {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : CurrentDerived Λ X ⥤ CurrentDerived Λ Y :=
  R(f)_![ModuleCat.{u + 1} Λ]

/-- The derived tensor product. -/
noncomputable abbrev currentTensor
    {Λ : Type (u + 1)} [CommRing Λ] (X : Scheme.{u}) :
    CurrentDerived Λ X ⥤ CurrentDerived Λ X ⥤ CurrentDerived Λ X :=
  -⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]

end WeilConjectures
