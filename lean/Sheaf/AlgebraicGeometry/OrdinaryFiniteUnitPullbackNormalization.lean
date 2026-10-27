/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import all Mathlib.Logic.Small.Defs
import Sheaf.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare
import Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-ordinary-finite-unit-pullback-normalization).

# Unit normalization for the ordinary constant pullback comparison
-/
@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
attribute [local irreducible] DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar

/-- The ordinary constant pullback comparison preserves the derived unit. -/
theorem ordinaryFiniteUnitPullback_hom_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFiniteUnitPullback A f).hom ≫
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom =
      (ordinaryFinitePullback A f).map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom := by
  calc
    _ = (constantSinglePullbackIso (ModuleCat.{u + 1} A) f (ModuleCat.of A A)).hom ≫
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom := by
      exact congrArg (fun q ↦ q ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom)
        (ordinaryFiniteUnitPullback_hom_eq_constant A f)
    _ = _ := ordinaryFiniteConstantUnit_square A f

end AlgebraicGeometry.Etale
