/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all Mathlib.Logic.Small.Defs
import Sheaf.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
import Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-ordinary-finite-unit-pullback-comparison).

# The ordinary constant pullback component
-/
@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
attribute [local irreducible] DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar

/-- The ordinary single-iso factorization is the canonical constant comparison.
Source: blueprint thm-amb-p1-adjunction.proof.md, canonical constant coefficient pullback.
Expand the two component formulas, which are the same single-degree comparison
followed by the single functor applied to the constant-sheaf comparison.
(blueprint: lem-z8-ordinary-finite-unit-pullback-comparison). -/
theorem ordinaryFiniteUnitPullback_hom_eq_constant (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFiniteUnitPullback A f).hom =
      (constantSinglePullbackIso (ModuleCat.{u + 1} A) f (ModuleCat.of A A)).hom := by
  exact (ordinaryFiniteUnitPullback_hom A f).trans (ordinaryFiniteConstantPullback_hom A f).symm

end AlgebraicGeometry.Etale
