/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentative

/-! # Section realization of coefficient scalar extension

Source: Stacks Project, Tags 03EK, 03EL, 06YY, 07A4 and 07A6;
steps 1--3 of `lem-sfb-coefficient-scalar-tensor-realization`.
(blueprint: lem-sfb-coefficient-scalar-section-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u d₁ d₂ r m c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap
  coefficientInternalScalarComplex coefficientSectionScalarPure coefficientSectionScalarTotal
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.ordinaryTensorComparison derivedTensor
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  internalScalarTensorIso internalScalarTensorComparison
  SheafOfModules.changeOfRingsHom
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor
  Adjunction.derivedAdjunction Mod.derivedExtendMapDerivedCategoryAdjunction
  Mod.derivedExtendRestrictAdjunction Mod.extendRestrictAdjunction
  Adjunction.mapHomotopyCategory Adjunction.mapHomologicalComplex Functor.preimageIso
  Functor.leftDerivedFunctorIsoMapDerivedCategory
  Functor.rightDerivedFunctorIsoMapDerivedCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] internalScalarExtension
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

end AlgebraicGeometry.ProEtale.CondensedRing
