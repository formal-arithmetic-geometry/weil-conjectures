/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData

/-! # Ordinary scalar tensor coordinates and total pullback

Source: Stacks Project, Tags 03EK, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-scalar-tensor-ordinary-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

/-- The restricted universal scalar counit on cochain representatives.
Source: Stacks 06YY (blueprint: lem-sfb-scalar-tensor-ordinary-pullback). -/
@[irreducible] def tensorScalarCounit {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules W A) ℤ) :
    (restriction a).mapDerivedCategory.obj
        ((proEtaleRingDerivedExtension a).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj
        (((restriction a).mapHomologicalComplex (.up ℤ)).obj
          (((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (restriction a).mapDerivedCategory.map
      ((proEtaleRingDerivedExtensionCounit a).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
    (restriction a).mapDerivedCategoryFactorsh.hom.app
      (((proEtaleRingExtension a).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The one-sided tensor comparison in the specified scalar coordinates.
Source: Stacks 06YY (blueprint: lem-sfb-scalar-tensor-ordinary-pullback). -/
@[irreducible] def tensorScalarCoordinates {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel W A) (P : CochainComplex (proEtaleRingModules W A) ℤ) :
    t.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (coefficientComplex a)) ⟶
      DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor P (coefficientComplex a) (proEtaleOrdinaryTensor W A)) :=
  (derivedTensorIso a t).inv.app (DerivedCategory.Q.obj P) ≫
    tensorScalarCounit a P ≫ DerivedCategory.Q.map (ordinaryComplexIso a P).hom

/-- The coefficient identification before localization, including the single-complex map.
Source: Stacks 03EL (blueprint: lem-sfb-scalar-tensor-ordinary-pullback). -/
@[irreducible] def tensorCoefficientComplexPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :
    (((proEtaleRingModulePullback f A (inverseRing f A)
      (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj (coefficientComplex a)) ≅
      coefficientComplex (inverseMap f a) :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _))
    (.up ℤ) 0).app (coefficient a)) ≪≫
    (CochainComplex.singleFunctor (proEtaleRingModules Z (inverseRing f A))
      (0 : ℤ)).mapIso (coefficientPullback f a)

/-- Ordinary total tensor pullback, followed by the fixed coefficient identification.
Source: Stacks 03EL, 07A4 (blueprint: lem-sfb-scalar-tensor-ordinary-pullback). -/
@[irreducible] def tensorScalarOrdinaryPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules T A) ℤ) :
    (((proEtaleRingModulePullback f A (inverseRing f A)
      (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P (coefficientComplex a) (proEtaleOrdinaryTensor T A))) ⟶
      CochainComplex.mapBifunctor
        (((proEtaleRingModulePullback f A (inverseRing f A)
          (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P)
        (coefficientComplex (inverseMap f a)) (proEtaleOrdinaryTensor Z (inverseRing f A)) :=
  (proEtaleTensorPullbackTotalIso f A (inverseRing f A) (Iso.refl _)
    P (coefficientComplex a)).inv ≫
    HomologicalComplex.mapBifunctorMap (𝟙 _)
      (tensorCoefficientComplexPullback f a).hom
      (proEtaleOrdinaryTensor Z (inverseRing f A)) (.up ℤ)

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  proEtaleRingModulePullback proEtaleRingDerivedPullbackFactors
  SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso HomologicalComplex₂.total
  Functor.mapBifunctorHomologicalComplex
attribute [local implicit_reducible] Functor.map₂HomologicalComplex

end AlgebraicGeometry.Scheme.DerivedScalarMate
