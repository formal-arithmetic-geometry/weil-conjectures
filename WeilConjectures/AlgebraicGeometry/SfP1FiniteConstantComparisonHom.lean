/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.SfP1NativeConstantHom
/-! # Finite constant inverse-image comparison -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

attribute [local irreducible] DerivedCategory.singleFunctors upperStar lowerStar
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

/-- The single-degree constant comparison is the native finite constant comparison. -/
theorem finiteConstantComparison_hom
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
        (ordinaryFiniteConstant A Y) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
          (ModuleCat.of A A)) =
    (leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} A) f
      (ModuleCat.of A A)).hom := by
  exact nativeConstant_hom (ModuleCat.{u + 1} A) f (ModuleCat.of A A)

end AlgebraicGeometry.Etale.SfP1Transport
