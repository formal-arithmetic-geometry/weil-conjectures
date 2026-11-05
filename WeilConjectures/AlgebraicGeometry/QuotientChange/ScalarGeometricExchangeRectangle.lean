/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedRealization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import all WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import all WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.NormalizedScalarSectionFamily
public import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle

/-! # Scalar extension and geometric exchange

Source: blueprint main-20261015, det-sf-comp-coherence-refinement.proof.md, (2),
coefficient devissage; Stacks Project, sites-cohomology.tex, Tags 07A7 and 0E47
(blueprint: lem-sfb-scalar-geometric-exchange-rectangle).

All functors are the existing ordinary unbounded internal-module derived functors.
The balancing maps are specified by their universal computation-counit normalization.
The direct-image maps are their actual mates, without an invertibility assumption.
-/

@[expose] public noncomputable section

set_option linter.all false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

attribute [local irreducible] CategoryTheory.mateEquiv
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedFunctor
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullback
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushforward
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedAdjunction
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullbackComposition
  AlgebraicGeometry.ProEtale.QuotientChange.scalarSectionPullComparison

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

attribute [local irreducible] scalarAmbientExchange scalarExchangeLeft scalarExchangeRight
  scalarSectionPushComparison sectionRectangleLambda sectionRectangleRho
  sectionRectangleExchange sectionRectangleSource sectionRectangleTarget
  sectionRectangleLeft sectionRectangleRight

attribute [local irreducible] rho SectionPullNormalized SectionScalarNormalized

end AlgebraicGeometry.ProEtale.QuotientChange
