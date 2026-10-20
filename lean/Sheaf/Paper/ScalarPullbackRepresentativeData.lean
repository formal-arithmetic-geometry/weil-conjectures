/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q158 and R3
-/
module

public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-!
# Specified scalar/pullback representative data

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6 and 07A7
(blueprint: def-pur-scalar-pullback-representative-data).

These are the existing comparison constructions, shared by the representative
computation and the theorem identifying its geometric mate with projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

/-- The ordinary scalar/pullback identification, conjugate to the sectionwise
restriction/direct-image identity under the two composite adjunctions.
Source: Stacks 07A4 (blueprint: def-pur-scalar-pullback-representative-data). -/
def scalarSheafPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    ProEtale.etaleSheafExtendScalars φ W ⋙ upperStar (ModuleCat.{u + 1} B) f ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ ProEtale.etaleSheafExtendScalars φ Z :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ Z))
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ W).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm
    (lowerStarCompRestrictScalarsIso φ f).symm

/-- The same comparison on actual cochain complexes.
Source: Stacks 07A4 (blueprint: def-pur-scalar-pullback-representative-data). -/
def scalarSheafPullbackComplexIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :=
  Functor.mapHomologicalComplexCompIso (scalarSheafPullbackIso φ f) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (upperStar (ModuleCat.{u + 1} A) f ⋙
        ProEtale.etaleSheafExtendScalars φ Z)) (.up ℤ)).symm

/-- The geometric derived counit, with the homotopy quotient comparison included.
Source: Stacks 07A4 (blueprint: def-pur-scalar-pullback-representative-data). -/
def scalarGeometricRepresentative
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    _root_.DerivedCategory.Qh.map
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P)

/-- The specified identification f_A^{-1}B_W[0] = B_Z[0].
Source: Stacks 07A4 and 07A6 (blueprint: def-pur-scalar-pullback-representative-data). -/
def scalarCoefficientPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj (scalarCoefficient φ W) ≅
      scalarCoefficient φ Z :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app _ ≪≫
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((upperStarRestrictScalarsIsoSheaf φ f).app (𝟙_ _) ≪≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapIso
          (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) f)).symm)

end AlgebraicGeometry.Etale
