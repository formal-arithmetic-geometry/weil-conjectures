/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import all Mathlib.Logic.Small.Defs
import Sheaf.AlgebraicGeometry.EtaleSectionUnitNormalization
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-ordinary-finite-constant-unit-square).

# The canonical constant pullback unit square
-/
@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
attribute [local irreducible] DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar

/-- The canonical constant pullback preserves the module coefficient unit.
Source: blueprint thm-amb-p1-adjunction.proof.md, constant coefficient normalization.
Specialize the proved canonical constant-complex unit square to module coefficients;
the coefficient monoidal unit is the module A itself.
(blueprint: lem-z8-ordinary-finite-constant-unit-square). -/
theorem ordinaryFiniteConstantUnit_square (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSinglePullbackIso (ModuleCat.{u + 1} A) f (ModuleCat.of A A)).hom ≫
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom =
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom := by
  exact (constantUnitPullback_unit (ModuleCat.{u + 1} A) f).symm

end AlgebraicGeometry.Etale
