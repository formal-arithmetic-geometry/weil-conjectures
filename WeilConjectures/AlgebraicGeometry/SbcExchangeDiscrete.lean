/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageComparison
public import WeilConjectures.SixFunctors.BaseChange.Derived

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-- The bounded-below discrete-module presentation of the specified exchange.
Source: blueprint `sk-lem-sbc-exchange-compatibility`, equation (2).
The map is the mate of the localized pro-etale pullback comparison.
(blueprint: sk-lem-sbc-exchange-compatibility)
-/
def sbcDiscreteExchangePlus (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare u f' f g) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctorPlus ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategoryPlus ⟶
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) u).mapDerivedCategoryPlus ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f').rightDerivedFunctorPlus :=
  (mateEquiv
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).derivedAdjunctionPlus
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f').derivedAdjunctionPlus
    (TwoSquare.mk _ _ _ _
      ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (ProEtale.upperStarCompIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.w.symm) ≪≫
        Functor.mapDerivedCategoryPlusCompIso _ _).hom)).natTrans

end AlgebraicGeometry.Scheme
