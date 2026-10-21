/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorPurityNormalization
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.PurEtaleScalarMateProjection

/-! # Degree-zero scalar comparisons for vector purity

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: def-pur-vector-purity-scalar-single).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The ordinary sheafified scalar extension and its actual adjunction.
Source: Stacks 03EK (blueprint: def-pur-vector-purity-scalar-single). -/
abbrev purityScalarSheaf {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B) :=
  ProEtale.etaleSheafExtendScalars φ T

/-- The ordinary scalar extension adjunction from the published sectionwise tensor.
Source: Stacks 03EK (blueprint: def-pur-vector-purity-scalar-single). -/
abbrev purityScalarSheafAdjunction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    purityScalarSheaf φ T ⊣ Sheaf.restrictScalars T.smallEtaleTopology φ :=
  ProEtale.etaleSheafExtendScalarsAdjunction φ T

/-- The universal derived scalar tensor, reusing the landed constant-ring adjunction.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
abbrev purityScalarExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  scalarExtension φ T

/-- The published scalar/pullback comparison, in the orientation used by reduction.
Source: Stacks 07A4 (blueprint: def-pur-vector-purity-scalar-single). -/
abbrev purityScalarPullback {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(upperStar (ModuleCat.{u + 1} A) f) ⋙ purityScalarExtension φ X ≅
      purityScalarExtension φ Y ⋙ L(upperStar (ModuleCat.{u + 1} B) f) :=
  (scalarPullbackIso φ f).symm

/-- The specified derived scalar adjunction, obtained from the landed right-adjoint instance.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
def purityScalarAdjunction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    purityScalarExtension φ T ⊣
      Sheaf.derivedRestrictScalars T.smallEtaleTopology φ :=
  Adjunction.ofIsRightAdjoint _

/-- Component of the published representative-normalized scalar tensor comparison.
Source: Stacks 07A4, `ExceptionalCoefficients.tensorIso`
(blueprint: def-pur-vector-purity-scalar-single). -/
def purityScalarTensor {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (K L : DerivedCategoryModule A T) :
    (purityScalarExtension φ T).obj (K ⊗ L) ≅
      (purityScalarExtension φ T).obj K ⊗ (purityScalarExtension φ T).obj L :=
  (ExceptionalCoefficients.tensorIso φ T).app (K, L)

end AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting

/-- Factor the scalar/single adjunction transpose in abstract categories, sharing its
functor endpoints before specializing to coefficient sheaves. This is the same unit
and exact-single comparison used below, with no extra choice of comparison.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
def purityAdjunctionSingleMap
    {C : Type v₁} {D : Type v₂} {E : Type v₃} {F : Type v₄}
    [Category.{w₁} C] [Category.{w₂} D] [Category.{w₃} E] [Category.{w₄} F]
    (S : C ⥤ D) (R : D ⥤ C) (Q : E ⥤ F) (V : F ⥤ E)
    (i : C ⥤ E) (j : D ⥤ F) (a : S ⊣ R) (b : Q ⊣ V)
    (c : j ⋙ V ≅ R ⋙ i) (M : C) : Q.obj (i.obj M) ⟶ j.obj (S.obj M) :=
  (b.homEquiv _ _).symm (i.map (a.unit.app M) ≫ c.inv.app (S.obj M))

/-- Transport a scalar-unit arrow along the specified single/unit identifications.
The generic endpoints keep kernel checking from expanding the derived monoidal data.
Source: sk-prop-an, Step 6 (blueprint: def-pur-vector-purity-scalar-single). -/
def purityTransportUnitMap {C : Type v₁} {D : Type v₂}
    [Category.{w₁} C] [Category.{w₂} D] (Q : C ⥤ D)
    {U U' : C} {V V' : D} (e : U ≅ U') (f : V ≅ V')
    (m : Q.obj U ⟶ V) : Q.obj U' ⟶ V' :=
  Q.map e.inv ≫ m ≫ f.hom

/-- The comparison on a sheaf in degree zero is the scalar transpose of the ordinary
scalar-unit map, followed by the exact restriction/single comparison.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
def purityScalarSingleMap {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (φ : A →+* A') (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Etale.purityScalarExtension φ T).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((Etale.purityScalarSheaf φ T).obj M) :=
  purityAdjunctionSingleMap (Etale.purityScalarSheaf φ T)
    (Sheaf.restrictScalars T.smallEtaleTopology φ) (Etale.purityScalarExtension φ T)
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (Etale.purityScalarSheafAdjunction φ T) (Etale.purityScalarAdjunction φ T)
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0) M

/-- The scalar image of the degree-zero coefficient unit, given by the published
normalized scalar unit identification `ExceptionalCoefficients.unitIso` (uniquely
fixed by the ordinary multiplication B tensor_A A -> B on the K-flat unit complex),
transported along both single/unit identifications.
Source: sk-prop-an, unit normalization in Step 6; Stacks 07A4
(blueprint: def-pur-vector-purity-scalar-single). -/
def purityScalarUnitMap {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (φ : A →+* A') (T : Scheme.{u}) :
    (Etale.purityScalarExtension φ T).obj
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _) :=
  purityTransportUnitMap (Etale.purityScalarExtension φ T)
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T).symm
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A') T).symm
    (Etale.ExceptionalCoefficients.unitIso φ T).hom

end WeilConjectures.PurityFiniteSetting
