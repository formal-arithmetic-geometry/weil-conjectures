/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import all WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import all WeilConjectures.AlgebraicGeometry.QuotientChange.NormalizedScalarRestrictionPush
import WeilConjectures.AlgebraicGeometry.QuotientChange.NormalizedScalarSectionFamily

/-! # Reduction of the actual unbounded integral exchange

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3);
Stacks Project, Tags 07A7, 0E47 and 0E48
(blueprint: lem-sfb-integral-quotient-exchange-comparison).

The equality is an equality of natural transformations. Its section-module realization
uses the independently specified ringed adjunctions and geometric compositors. Scalar
comparisons retain their balanced-generator and K-flat computation normalizations.
As in the direct-image comparison, n denotes quotient exponent n + 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale.QuotientChange
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  mateEquiv AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedFunctor
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullback
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushforward
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedAdjunction
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullbackComposition
  AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarComp

open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]

attribute [local irreducible] ambient sectionSquare sectionExchange pullSection pushSection
  scalarAmbientExchange scalarSectionPushComparison scalarSectionPullComparison
  sectionRectangleExchange

end Ambient

set_option allowUnsafeReducibility true
attribute [local semireducible] ModuleRingedComparison.derivedFunctor

section ScalarSectionRealization

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]
  (a : R ⟶ S) [IsMonHom a]

attribute [local irreducible] ScalarComparisonRealized sectionScalarProjection
  SectionScalarNormalized SectionPullNormalized rho scalarExchangeLeft scalarExchangeRight
  sectionRectangleLambda sectionRectangleRho sectionRectangleLeft sectionRectangleRight
  sectionRectangleSource sectionRectangleTarget

end ScalarSectionRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (n : ℕ)
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (integral l E) T)]
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (finite l E n) T)]

variable
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      D (reduction l E n) V ⋙ L (finite l E n) u ≅
        L (integral l E) u ⋙ D (reduction l E n) U)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}

end AlgebraicGeometry.ProEtale.IntegralQuotient
