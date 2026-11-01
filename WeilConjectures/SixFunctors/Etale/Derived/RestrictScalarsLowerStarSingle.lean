/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar

/-!
# Restriction of scalars and the derived direct image of a sheaf in degree `0`

For a ring map `φ : Λ →+* Λ'` and a morphism of schemes `f : X ⟶ Y`, restriction of scalars
along `φ` commutes with the derived direct image `Rf_*` of a sheaf of `Λ'`-modules placed in
degree `0` (`AlgebraicGeometry.Etale.restrictScalarsRightDerivedLowerStarSingleIso`), in the
unbounded derived categories.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section RestrictScalars

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') {X Y : Scheme.{u}}
  (f : X ⟶ Y)

/-- Restriction of scalars along `φ : Λ →+* Λ'` commutes with the derived direct image of a sheaf
placed in degree `0`: `Res (Rf_* M) ≅ Rf_* (Res M)`. This is the bounded below comparison
`AlgebraicGeometry.Etale.rightDerivedLowerStarRestrictScalars`, transported to the unbounded
derived categories. -/
noncomputable def restrictScalarsRightDerivedLowerStarSingleIso
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategory.obj
        ((R((f)_*[ModuleCat.{u + 1} Λ'])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj M)) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M)) :=
  (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategory.mapIso
      ((((f)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlusCompatibility.app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M)).symm) ≪≫
    ((Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlusCompatibility.app
      _).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      (asIso ((rightDerivedLowerStarRestrictScalars φ f).app _) ≪≫
        ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
          (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusSingleFunctor
            0).app M)) ≪≫
    ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _

end RestrictScalars

end Etale

end AlgebraicGeometry
