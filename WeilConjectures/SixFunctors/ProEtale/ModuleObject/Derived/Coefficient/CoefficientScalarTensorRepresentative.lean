/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeEquation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeInternal
/-! # Tensor representatives under coefficient scalar reconstruction

Source: Stacks Project, Tags 03EK, 03EL, 06YY, 07A4 and 07A6;
steps 1--3 of `lem-sfb-coefficient-scalar-tensor-realization`.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap internalScalarExtension
  coefficientInternalScalarComplex coefficientSectionScalarPure coefficientSectionScalarTotal
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor derivedTensor
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
  Localization.Monoidal.tensorBifunctor
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]
end AlgebraicGeometry.ProEtale.CondensedRing
