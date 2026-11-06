/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData

/-! # The derived tensor counit on complex objects

The general derived tensor counit equation is written on complex representatives,
with the quotient and prolonged-functor objects in their native presentations.
(blueprint: lem-sfb-coefficient-scalar-tensor-homotopy-complex)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  ModuleRingedComparison.totalComparison ModuleRingedComparison.ordinaryTensorComparison
  Localization.Monoidal.tensorBifunctor


end AlgebraicGeometry.ProEtale.CondensedRing
