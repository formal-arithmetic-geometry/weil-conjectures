/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorInternalComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeTotalPath
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientTensorLocalization

/-! # The localized left scalar tensor path

This is the first half of the representative diagram, before using the two factor
scalar equations and the assumed derived tensor square.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-left-path)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap internalScalarExtension
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  ModuleRingedComparison.totalComparison ModuleRingedComparison.ordinaryTensorComparison
  Localization.Monoidal.tensorBifunctor

-- Match native prolongations before reducing concrete section constructions.
attribute [local irreducible] HomologicalComplex₂.total Mod.inducingFunctorData
  InternalAbelianSheafModule.sectionModuleEquivalence SheafOfModules.monoidalCategory

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

end AlgebraicGeometry.ProEtale.CondensedRing
