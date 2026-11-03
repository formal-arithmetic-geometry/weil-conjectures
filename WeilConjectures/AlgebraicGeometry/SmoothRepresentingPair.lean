/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic

/-! # Representing objects

Source: latest blueprint, `part-duality-trace-formula/sec-smooth-purity/`
`sec-the-trace-map-of-affine-space/sk-def-sp-representing-pair/_section.md`,
Definition "Representing objects" (blueprint: sk-def-sp-representing-pair).

The two structures below are the étale and pro-étale realizations of the same definition.
The functor `Rf_!` is the existing compact-support functor of the chosen compactification.
The representing object and target are ambient unbounded derived objects; only the test object
is required to be bounded constructible with finite Tor amplitude.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A pair representing `Hom(Rf_!(-), K)` on all bounded constructible finite-Tor tests in
`D(X, Z/ell^n Z)` for the small étale site. The functor is the canonical compact-support
construction for the smooth morphism `f`; `object` and `K` are ambient derived objects.
Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-def-sp-representing-pair/_section.md,
Definition "Representing objects" (blueprint: sk-def-sp-representing-pair). -/
structure RepresentingPair (ell n : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [HasCompactification f]
    (K : DerivedCategoryModule (ULift.{u + 1} (ZMod (ell ^ n))) Y) where
  /-- The representing object is an unrestricted object of the ambient derived category on X. -/
  object : DerivedCategoryModule (ULift.{u + 1} (ZMod (ell ^ n))) X
  /-- The specified morphism from the compactly supported image of the object to K. -/
  counit : (rightDerivedLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))) f).obj object ⟶ K
  /-- Composition with the counit gives the required bijection for every Dctf test object. -/
  map_bijective : ∀ M : DerivedCategoryModule (ULift.{u + 1} (ZMod (ell ^ n))) X,
    DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod (ell ^ n))) X M →
    (∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} (ZMod (ell ^ n))) X a b M) →
    Function.Bijective (fun b : M ⟶ object ↦
      (rightDerivedLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))) f).map b ≫ counit)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- A pair representing `Hom(Rf_!(-), K)` on all bounded constructible finite-Tor tests in
`D(X, Z/ell^n Z)` for the small pro-étale site. The functor is the canonical compact-support
construction for the smooth morphism `f`; `object` and `K` are ambient derived objects.
Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-def-sp-representing-pair/_section.md,
Definition "Representing objects" (blueprint: sk-def-sp-representing-pair). -/
structure RepresentingPair (ell n : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))))) where
  /-- The representing object is an unrestricted object of the ambient derived category on X. -/
  object : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))))
  /-- The specified morphism from the compactly supported image of the object to K. -/
  counit : (rightDerivedLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))) f).obj object ⟶ K
  /-- Composition with the counit gives the required bijection for every Dctf test object. -/
  map_bijective : ∀ M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n))))),
    DerivedCategory.boundedConstructibleIntrinsic (ULift.{u + 1} (ZMod (ell ^ n))) X M →
    (∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
      (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n))))) a b M) →
    Function.Bijective (fun b : M ⟶ object ↦
      (rightDerivedLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))) f).map b ≫ counit)

end AlgebraicGeometry.ProEtale
