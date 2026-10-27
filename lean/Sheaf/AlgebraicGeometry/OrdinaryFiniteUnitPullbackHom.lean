/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # Constant-object pullback comparisons

Source: blueprint vector integration, compatibility with restriction.
(blueprint: lem-amb-ordinary-finite-unit-pullback-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor upperStar

/-- The concrete constant-object pullback has its specified two factors.
Source: the definition of ordinaryFiniteUnitPullback, blueprint vector integration.
(blueprint: lem-amb-ordinary-finite-unit-pullback-hom). -/
theorem ordinaryFiniteUnitPullback_hom (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFiniteUnitPullback A f).hom =
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
        (ordinaryFiniteConstant A Y) ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
          (ModuleCat.of A A)) := rfl

end AlgebraicGeometry.Etale
