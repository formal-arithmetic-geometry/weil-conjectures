/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all Mathlib.Logic.Small.Defs
/-!

# Constant coefficient comparison component
-/
@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
attribute [local irreducible] DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar

/-- The canonical constant comparison has its two prescribed factors.

Specialize the generic component equation to module coefficients, leaving the
single-complex comparison and constant-sheaf comparison as the two factors. -/
theorem ordinaryFiniteConstantPullback_hom (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSinglePullbackIso (ModuleCat.{u + 1} A) f (ModuleCat.of A A)).hom =
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
          (ordinaryFiniteConstant A Y) ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
            (ModuleCat.of A A)) := by
  exact constantSinglePullbackIso_hom (ModuleCat.{u + 1} A) f (ModuleCat.of A A)

end AlgebraicGeometry.Etale
