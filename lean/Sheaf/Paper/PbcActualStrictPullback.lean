/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.Paper.CompletedPullback

/-! # Functor and completion interface for the published strict-tower pullback
Source: Stacks 099N (2),(5), blueprint order 1261
(blueprint: def-weil-pbc-completed-pullback).
The published quotient tower, resolving pullback, derived limit and comparison
are retained. This interface supplies their functor and unit-compatible natural
isomorphism to the intrinsic completion reflector used by scalar comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The functor underlying exactly the published completedPullbackObject.
Source: Stacks 099N (blueprint: def-weil-pbc-completed-pullback). -/
abbrev pbcActualStrictCompletedPull :=
  (completedReductionTower Y d ⋙ completedTowerPullback g d) ⋙ completedTowerRlim d X

/-- The actual compatible-family unit followed by derived limit of one strict
quotient augmentation. Its components are completedPullbackComparison.
Source: Stacks 099N (blueprint: def-weil-pbc-completed-pullback). -/
def pbcActualStrictCompletedPullUnit :
    pbcActualDerivedPull g d ⟶ pbcActualStrictCompletedPull d g :=
  (pbcActualDerivedPull g d).rightUnitor.inv ≫
    whiskerLeft (pbcActualDerivedPull g d) (completedConstantRlimUnit d X) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight ((completedPullbackConstantIso g d).hom ≫
      whiskerRight (completedReductionTowerUnit d Y) (completedTowerPullback g d))
        (completedTowerRlim d X)

/-- The strict-tower formula and the completion reflector give the same completed
pullback, with the canonical quotient augmentation as their unit.
Source: Stacks 099N (2),(5) (blueprint: def-weil-pbc-completed-pullback).
Proof: apply completedPullback_isCompletion to a flat-term K-flat representative.
Its finite-reduction comparisons identify the entire strict pulled-back tower,
including transitions, with the ordinary pullback's reduction tower. The
constant/completed comparison preserves the derived limits and quotient units.
Transport the source's intrinsic completion to the actual complete predicate.
It is the reflection onto that predicate. The universal reflection property
therefore gives the stated unique unit-compatible isomorphism. Its uniqueness
makes it natural on the full derived-complete category, including all its maps. -/
theorem pbcActualCompletedPullback_tower :
    ∃! e :
      ObjectProperty.ι (PbcIsIntrinsicallyComplete Y d) ⋙ pbcActualStrictCompletedPull d g ≅
        ObjectProperty.ι (PbcIsIntrinsicallyComplete Y d) ⋙ pbcActualCompletedPull g d,
      ∀ K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y d),
        (pbcActualStrictCompletedPullUnit d g).app K.obj ≫ e.hom.app K =
          (pbcActualCompletedPullUnit g d).app K.obj := by
  sorry

end AlgebraicGeometry.Scheme
