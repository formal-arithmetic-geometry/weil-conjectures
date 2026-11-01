/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactPullbackComparisonMonoidal

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapAssoc
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence

/-! # The native compactification projection as a right tensor action

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-identification/def-sf-cup.md, final associativity and unit sentence;
the native projection-input calculation expanded in the DAG
(blueprint: lem-sf-compact-projection-right-tensor-action).

The maps below use the ordinary unbounded internal-module categories, their relative
K-flat derived tensor, and the specified native adjunctions. No completion is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The inverse canonical open-support projection, with its target identified with native
left derived pullback by the landed canonical exact comparison `supportPullbackExactComparison`
(the `c_j` of lem-sf-exact-pullback-comparison-monoidal). The inverse is taken only after the
recorded support projection formula, applied to the actual closed complement, supplies
invertibility.
Source: def-sf-cup, projection construction
(blueprint: lem-sf-compact-projection-right-tensor-action). -/
def compactProjectionOpenInverse {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (supportModules Λ U)) (V : DerivedCategory (supportModules Λ X)) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.obj K ⊗ V ⟶
      (openImmersionLowerShriek Λ j).mapDerivedCategory.obj
        (K ⊗ (upperStar Λ j).leftDerivedFunctor.obj V) :=
  @inv _ _ _ _ (openSupportProjection Λ j K V)
      ((openClosedSupportProjectionFormula Λ j.closedComplement j
        j.range_closedComplement).2 K V) ≫
    (openImmersionLowerShriek Λ j).mapDerivedCategory.map
      (K ◁ (supportPullbackExactComparison Λ j).inv.app V)

/-- The inverse native compositor `Lj* Lp* ≅ Lf*`, including the specified factorization
identity of the compactification.
Source: def-sf-cup, native pullback compositor
(blueprint: lem-sf-compact-projection-right-tensor-action). -/
def compactProjectionPullbackCompositor {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (upperStar Λ c.g).leftDerivedFunctor ⋙ (upperStar Λ c.i).leftDerivedFunctor ≅
      (upperStar Λ f).leftDerivedFunctor :=
  ((upperStar Λ f).leftDerivedFunctorNatIso (upperStarCongr Λ c.comm) ≪≫
    leftDerivedUpperStarComp Λ c.i c.g).symm

/-- The precise compactification projection: the counit mate for `p`, the inverse
unit-induced open projection, then identity tensor the inverse native compositor.
Source: def-sf-cup, native projection-input construction
(blueprint: lem-sf-compact-projection-right-tensor-action). -/
def compactProjectionRightTensorMap {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (K : DerivedCategory (supportModules Λ X)) (N : DerivedCategory (supportModules Λ Y)) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⊗ N ⟶
      (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj
        (K ⊗ (moduleObjectDerivedPullback Λ f).obj N) :=
  letI : QuasiCompact c.obj.obj.i := c.obj.property
  moduleObjectProjectionMap Λ c.obj.obj.g
      ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K) N ≫
    (moduleObjectDerivedPushforward Λ c.obj.obj.g).map
      (compactProjectionOpenInverse Λ c.obj.obj.i K
        ((moduleObjectDerivedPullback Λ c.obj.obj.g).obj N)) ≫
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map
      (K ◁ (compactProjectionPullbackCompositor Λ c.obj.obj).hom.app N)

end AlgebraicGeometry.ProEtale.CondensedRing
