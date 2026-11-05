/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
public import WeilConjectures.Algebra.Homology.KFlatRoos.KFlatRoosRepresentativeInvariance
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
/-! # Strict completion comparison interface

Source: blueprint main-20261015, localizing-closure finite-model proof, Locality;
Stacks Tags 09AA, 03EK, 014E and 08TC
(blueprint: def-sfb-strict-completion-restriction-data).

The presentation structures below only package the assertions of this node. Cone
objects, coordinates, tower arrows, Roos functor, augmentations and localized units
are all fixed by equations. No comparison or completion is selected from existence.
Positive exponent n+1 is indexed by n : ℕ, as in the recorded completion interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b c d w z
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures
open CategoryTheory.InternalAbelianSheafModule

namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open ModuleObjectRingedComparison

-- Keep the tensor-unit construction folded while checking the reduction interface.
-- Explicit identity-complex transport avoids rechecking that large tensor expression.
attribute [local irreducible] SheafOfModules.KFlatRoos.tensorUnit
  SheafOfModules.siteSheafTensorRight
  SheafOfModules.KFlatRoos.roos coefficientTotalTensor
  SheafOfModules.siteSheafTensorTmul coefficientTensorGenerator

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
