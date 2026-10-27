/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Paper.ProperOpenCoefficientRefinement
public import Sheaf.Paper.BoundedFlatCoefficientSiteSquare
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Paper.EtaleSumCoefficientComputation
public import Sheaf.AlgebraicGeometry.Etale.OpenExtensionZeroEtaleAdjunctionAgreement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

import all Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import all Sheaf.Paper.EtaleOpenScalarExchange
import Sheaf.Paper.EtaleDirectImageScalarComposition
import Sheaf.Paper.FiniteCoefficientInputModels
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import Sheaf.AlgebraicGeometry.EtaleSumTensorTestComparison
import Sheaf.AlgebraicGeometry.EtaleConstantModuleFlat
import WeilConjectures.ConstructibleSheaf.ExtensionByZero
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Sheaf.SixFunctors.EtaleOpenTensorDefs
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

/-! # Flat models and the specified etale open coefficient counit

Source: blueprint main-20261015, det-sp-reduction-exceptional, Locality;
Stacks Project, Tag 0GL6 (blueprint: lem-sp-etale-open-counit-flat-models).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale
namespace OpenCounitFlatModels

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

/-- The identity-proper-factor compactification, with its canonical identity-direct-image
boundary removed. This is the specified compact-support coefficient map, not an arbitrary
open tensor identification. Source: Stacks 0GL6, blueprint Locality
(blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def coefficientMap {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategoryModule A U) :
    (scalarExtension φ X).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj
        ((scalarExtension φ U).obj K) :=
  (scalarExtension φ X).map
      ((rightDerivedLowerStarIdIso A X).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)) ≫
    ProEtale.CoefficientCompatibility.etaleCoefficientMap φ
      (Compactification.ofIsOpenImmersion j) K ≫
    (rightDerivedLowerStarIdIso B X).hom.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj
        ((scalarExtension φ U).obj K))

/-- The ordinary summandwise tensor comparison, determined by the evaluation and scalar
adjunctions and identity-on-sections restriction of scalars. Source: Stacks 03DI, 0GL6
(blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def sheafCoefficientIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
        ProEtale.etaleSheafExtendScalars φ X ≅
      ProEtale.etaleSheafExtendScalars φ U ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} B) j :=
  ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)).leftAdjointUniq
    (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
        (upperStarRestrictScalarsIsoSheaf φ j).symm)

/-- Apply the ordinary summandwise tensor map degreewise, keeping all localization
boundaries explicit. Source: Stacks 0GL6
(blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def coefficientComplexMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj P) ⟶
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapHomologicalComplex (.up ℤ)).obj
      (((ProEtale.etaleSheafExtendScalars φ U).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexCompIso (sheafCoefficientIso φ j) (.up ℤ)).hom.app P

/-- The unique extension-summand inclusion, from the actual open unit and its
restriction identification. Source: Stacks 03DI and 03S3
(blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def sheetMap (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (S : U.Etale) :=
  (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M) ≫
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj M)).hom.app (Opposite.op S)

/-- The tensor identification keeps each extension summand and its pure tensor.
Source: Stacks 03DI and 0GL6 (blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def sheetEquation {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  ∀ (n : ℤ) (S : U.Etale) (x : (P.X n).obj.obj (Opposite.op S)) (b : B),
    (((sheafCoefficientIso φ j).hom.app (P.X n)).hom.app
      (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj S))).hom
      (etaleScalarPureTensor φ X
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj (P.X n))
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj S))
        ((sheetMap A j (P.X n) S).hom x) b) =
    (sheetMap B j ((ProEtale.etaleSheafExtendScalars φ U).obj (P.X n)) S).hom
      (etaleScalarPureTensor φ U (P.X n) (Opposite.op S) x b)

/-- The ordinary sheaf counit applied in every degree. Source: Stacks 03DI and 03S3
(blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def evaluationComplexMap (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ⟶ P :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).counit.app P

/-- Flat bounded models for all four scalar/site operations, and their actual derived
scalar counits. All sites and tensors are the recorded ones. Source: Stacks 06YQ, 0G7E,
0GL6 (blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def scalarSiteModels {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (a b : ℤ)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  ProEtale.BoundedFlatCoefficientSiteSquare.modelProperties
      T.smallEtaleTopology A a b P ∧
    (∀ q : ℤ, IsConstructibleEtaleModuleSheaf (P.X q)) ∧
    ProEtale.BoundedFlatCoefficientSiteSquare.modelProperties T.smallEtaleTopology B a b
      (coefficientExtendedComplex φ T P) ∧
    @ProEtale.BoundedFlatCoefficientSiteSquare.modelProperties T.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) A inferInstance a b
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex
        (.up ℤ)).obj P) ∧
    @ProEtale.BoundedFlatCoefficientSiteSquare.modelProperties T.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) B inferInstance a b
      (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex
          (.up ℤ)).obj P)) ∧
    @ProEtale.BoundedFlatCoefficientSiteSquare.modelProperties T.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) B inferInstance a b
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapHomologicalComplex
        (.up ℤ)).obj (coefficientExtendedComplex φ T P)) ∧
    IsIso (scalarExtensionRepresentative φ T P) ∧
    IsIso (ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex
        (.up ℤ)).obj P))

/-- Preservation, essential surjectivity and the restricted comparison equivalence,
using the existing intrinsic bounded-constructible finite-Tor predicates. Source:
Stacks 09AL, 0963, 0E8I (blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def openDomains (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Prop :=
  (∀ K, ProEtale.exceptionalTransportEtaleObjects A X K →
    ProEtale.exceptionalTransportEtaleObjects A U
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)) ∧
  (∀ K, ProEtale.exceptionalTransportEtaleObjects A U K →
    ProEtale.exceptionalTransportEtaleObjects A X
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)) ∧
  (∀ M, ProEtale.exceptionalTransportProEtaleObjects A X M →
    ProEtale.exceptionalTransportProEtaleObjects A U
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M)) ∧
  (∀ M, ProEtale.exceptionalTransportProEtaleObjects A U M →
    ProEtale.exceptionalTransportProEtaleObjects A X
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M)) ∧
  ∀ T : Scheme.{u}, T ∈ [U, X] →
    (∀ M, ProEtale.exceptionalTransportProEtaleObjects A T M →
      ∃ K, ProEtale.exceptionalTransportEtaleObjects A T K ∧
        Nonempty ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
          K ≅ M)) ∧
    (∃ F : (ProEtale.exceptionalTransportEtaleObjects A T).FullSubcategory ⥤
        (ProEtale.exceptionalTransportProEtaleObjects A T).FullSubcategory,
      F.IsEquivalence ∧ Nonempty
        (F ⋙ (ProEtale.exceptionalTransportProEtaleObjects A T).ι ≅
          (ProEtale.exceptionalTransportEtaleObjects A T).ι ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory))

/-- Equality with the localized summandwise tensor map, including its canonical K-flat
and exact-localization boundaries. Source: Stacks 0GL6
(blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def coefficientModelEquation {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  (scalarExtension φ X).map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.inv.app P) ≫
    coefficientMap φ j (_root_.DerivedCategory.Q.obj P) ≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
      (scalarExtensionRepresentative φ U P) ≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.hom.app
      (coefficientExtendedComplex φ U P) =
  scalarExtensionRepresentative φ X
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj
        P) ≫
    _root_.DerivedCategory.Q.map (coefficientComplexMap φ j P)

/-- The derived counit is exactly the localization of the degreewise evaluation map.
Source: Stacks 03DI (blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def evaluationModelEquation (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P) ≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ≫
    _root_.DerivedCategory.Q.map (evaluationComplexMap A j P) =
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit.app
      (_root_.DerivedCategory.Q.obj P)

/-- The restricted and extended etale models and their site pullbacks represent the
corresponding actual operations. These are derived-category isomorphisms, rather than
only cohomology identifications. Source: Stacks 0963, 09AF, 03DI
(blueprint: lem-sp-etale-open-counit-flat-models). -/
@[irreducible] def operationModels (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (K : DerivedCategoryModule A X) : Prop :=
  Nonempty (_root_.DerivedCategory.Q.obj
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ≅
    (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) ∧
  Nonempty (_root_.DerivedCategory.Q.obj
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj
        (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P)) ≅
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)) ∧
  Nonempty (_root_.DerivedCategory.Q.obj
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U).mapHomologicalComplex
        (.up ℤ)).obj
        (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P)) ≅
    (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)) ∧
  Nonempty (_root_.DerivedCategory.Q.obj
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex
        (.up ℤ)).obj
        (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (.up ℤ)).obj
          (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P))) ≅
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)))

set_option backward.isDefEq.respectTransparency true

private theorem scalarSiteModels_of_flat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (a b : ℤ)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hf : ∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q)))
    (hc : ∀ q : ℤ, IsConstructibleEtaleModuleSheaf (P.X q))
    (hz : ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) :
    scalarSiteModels φ T a b P := by
  obtain ⟨hA, hB, hpA, hpB, hpB', he, hp, -⟩ :=
    ProEtale.BoundedFlatCoefficientSiteSquare.boundedFlatCoefficientSiteSquare
      T φ (min a b) b (min_le_right _ _) P hf
      (fun q hq ↦ hz q (hq.imp_left (fun h ↦ lt_of_lt_of_le h (min_le_left _ _))))
  unfold scalarSiteModels
  refine ⟨⟨hA.1.1, hz, hA.1.2.2⟩, hc, ⟨hB.1.1, ?_, hB.1.2.2⟩,
    ⟨hpA.1.1, ?_, hpA.1.2.2⟩, ⟨hpB.1.1, ?_, hpB.1.2.2⟩,
    ⟨hpB'.1.1, ?_, hpB'.1.2.2⟩, he, hp⟩
  · intro q hq
    exact (ProEtale.etaleSheafExtendScalars φ T).map_isZero (hz q hq)
  · intro q hq
    exact (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map_isZero (hz q hq)
  · intro q hq
    exact (ProEtale.sheafExtendScalars φ T).map_isZero
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map_isZero (hz q hq))
  · intro q hq
    exact (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).map_isZero
      ((ProEtale.etaleSheafExtendScalars φ T).map_isZero (hz q hq))

private theorem boundedConstructible_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : DerivedCategoryModule A T) :
    DerivedCategory.isBoundedConstructible A T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, h⟩
    exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
      (fun i hi ↦ h i (.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
        (fun i hi ↦ h i (.inr hi))⟩⟩,
      fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (hc i), min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).mp ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).mp hb i hi

private theorem etaleObjects_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : DerivedCategoryModule A T) :
    ProEtale.exceptionalTransportEtaleObjects A T K ↔
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, ht⟩
    exact ⟨(boundedConstructible_iff_source A T K).mp hc, a, b,
      DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht⟩
  · rintro ⟨hc, a, b, ht⟩
    refine ⟨(boundedConstructible_iff_source A T K).mpr hc, min a b, b,
      min_le_right _ _, ?_⟩
    exact DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (ht.mono (min_le_left _ _) le_rfl)

private theorem etale_restriction_preserves
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategoryModule A X) (hK : ProEtale.exceptionalTransportEtaleObjects A X K) :
    ProEtale.exceptionalTransportEtaleObjects A U
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) := by
  apply (etaleObjects_iff_source A U _).mpr
  have h := constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} A) j
    ((etaleObjects_iff_source A X K).mp hK)
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) U).prop_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).app K) h

private theorem etale_extension_preserves
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategoryModule A U) (hK : ProEtale.exceptionalTransportEtaleObjects A U K) :
    ProEtale.exceptionalTransportEtaleObjects A X
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) := by
  apply (etaleObjects_iff_source A X _).mpr
  obtain ⟨hc, a, b, ht⟩ := (etaleObjects_iff_source A U K).mp hK
  obtain ⟨⟨c, hge⟩, ⟨d, hle⟩⟩ := hc.1
  have h := constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek
    A j (min a c) (max b d)
    ⟨⟨hc, (show _root_.DerivedCategory.homologyConcentratedIn c d K from
      ⟨hge, hle⟩).mono (min_le_right _ _) (le_max_right _ _)⟩,
      ht.mono (min_le_left _ _) (le_max_left _ _)⟩
  exact ⟨h.1.1, min a c, max b d, h.2⟩

private theorem finiteTor_object_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T] :
    ProEtale.exceptionalTransportProEtaleObjects A T =
      (ProEtale.exceptionalTransportEtaleObjects A T).map
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory := by
  exact ProEtale.exceptionalTransport_object_comparison A T

private theorem finiteTor_comparison_equivalence
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T] :
    ∃ F : (ProEtale.exceptionalTransportEtaleObjects A T).FullSubcategory ⥤
        (ProEtale.exceptionalTransportProEtaleObjects A T).FullSubcategory,
      F.IsEquivalence ∧ Nonempty
        (F ⋙ (ProEtale.exceptionalTransportProEtaleObjects A T).ι ≅
          (ProEtale.exceptionalTransportEtaleObjects A T).ι ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory) := by
  let P := ProEtale.exceptionalTransportEtaleObjects A T
  let Q := ProEtale.exceptionalTransportProEtaleObjects A T
  let N := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  have h : Q = P.map N := finiteTor_object_comparison A T
  let F := P.ι ⋙ N
  have hF (K : P.FullSubcategory) : Q (F.obj K) := by
    rw [h]
    exact ObjectProperty.prop_map_obj P N K.property
  let H := Q.lift F hF
  have hbij (K L : P.FullSubcategory) : Function.Bijective
      (fun v : K ⟶ L ↦ H.map v) := by
    obtain ⟨a, b, hab, hL⟩ := L.property.1.2
    have hplus : _root_.DerivedCategory.TStructure.t.plus L.obj :=
      ⟨a, (_root_.DerivedCategory.isGE_iff L.obj a).2 (fun i hi ↦ hL i (.inl hi))⟩
    constructor
    · intro v w hvw
      apply ObjectProperty.hom_ext
      exact (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hplus).1
        (congrArg (fun z ↦ z.hom) hvw)
    · intro v
      obtain ⟨w, hw⟩ :=
        (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hplus).2 v.hom
      exact ⟨ObjectProperty.homMk w, Q.hom_ext hw⟩
  have : H.Full := ⟨fun v ↦ (hbij _ _).surjective v⟩
  have : H.Faithful := ⟨fun hvw ↦ (hbij _ _).injective hvw⟩
  have : H.EssSurj := ⟨fun K ↦ by
    have hK : (P.map N) K.obj := (congrFun h K.obj).mp K.property
    obtain ⟨L, hL, ⟨e⟩⟩ := hK
    exact ⟨⟨L, hL⟩, ⟨Q.isoMk e⟩⟩⟩
  exact ⟨H, {}, ⟨Iso.refl _⟩⟩

private theorem proObjects_of_iso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    {K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (e : K ≅ L) (hK : ProEtale.exceptionalTransportProEtaleObjects A T K) :
    ProEtale.exceptionalTransportProEtaleObjects A T L := by
  rw [finiteTor_object_comparison A T] at hK ⊢
  exact ObjectProperty.prop_of_iso _ e hK

private theorem pro_operation_preserves
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T S : Scheme.{u}) [IsNoetherian T] [IsNoetherian S]
    (F : DerivedCategoryModule A T ⥤ DerivedCategoryModule A S)
    (G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙ G ≅
      F ⋙ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory)
    (hF : ∀ K, ProEtale.exceptionalTransportEtaleObjects A T K →
      ProEtale.exceptionalTransportEtaleObjects A S (F.obj K))
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (hM : ProEtale.exceptionalTransportProEtaleObjects A T M) :
    ProEtale.exceptionalTransportProEtaleObjects A S (G.obj M) := by
  rw [finiteTor_object_comparison A T] at hM
  obtain ⟨K, hK, ⟨h⟩⟩ := hM
  rw [finiteTor_object_comparison A S]
  exact ⟨F.obj K, hF K hK, ⟨(e.app K).symm ≪≫ G.mapIso h⟩⟩

private theorem openDomains_of_noetherian
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [IsNoetherian U] [IsNoetherian X] : openDomains A j := by
  unfold openDomains
  refine ⟨etale_restriction_preserves A j, etale_extension_preserves A j, ?_, ?_, ?_⟩
  · exact pro_operation_preserves A X U _ _
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
        Functor.mapDerivedCategoryCompIso _ _)
      (etale_restriction_preserves A j)
  · exact pro_operation_preserves A U X _ _
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} A) j).symm ≪≫
        Functor.mapDerivedCategoryCompIso _ _)
      (etale_extension_preserves A j)
  · intro T hT
    have : IsNoetherian T := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl <;> infer_instance
    refine ⟨?_, finiteTor_comparison_equivalence A T⟩
    intro M hM
    rw [finiteTor_object_comparison A T] at hM
    exact hM

private theorem scalar_preserves_on_comparison
    (ell : ℕ) [Fact ell.Prime]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    (T : Scheme.{u}) [IsNoetherian T] (K : DerivedCategoryModule A T)
    (hK : ProEtale.exceptionalTransportEtaleObjects A T K) :
    ProEtale.exceptionalTransportEtaleObjects B T ((scalarExtension φ T).obj K) ∧
      ProEtale.exceptionalTransportProEtaleObjects B T
        ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K)) := by
  obtain ⟨a, b, hab, ht⟩ := hK.2
  obtain ⟨P, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hbc, ht', _, _, _, hcN, hbdN, htN⟩ :=
    finiteCoefficientInputModels T ell (Fact.out) A B hA hB φ a b hab K hK.1 ht
  exact ⟨⟨hbc, a, b, hab, ht'⟩, hbdN, hcN, a, b, hab, htN⟩

private theorem scalar_preserves
    (ell : ℕ) [Fact ell.Prime]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    (T : Scheme.{u}) [IsNoetherian T] :
    (∀ K, ProEtale.exceptionalTransportEtaleObjects A T K →
      ProEtale.exceptionalTransportEtaleObjects B T ((scalarExtension φ T).obj K)) ∧
    (∀ M, ProEtale.exceptionalTransportProEtaleObjects A T M →
      ProEtale.exceptionalTransportProEtaleObjects B T
        ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).obj M)) := by
  refine ⟨fun K hK ↦ (scalar_preserves_on_comparison ell hA hB φ T K hK).1, ?_⟩
  intro M hM
  rw [finiteTor_object_comparison A T] at hM
  obtain ⟨K, hK, ⟨e⟩⟩ := hM
  exact proObjects_of_iso B T
    ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).mapIso e)
    (scalar_preserves_on_comparison ell hA hB φ T K hK).2

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
  upperStarIsoLocalizationRestriction
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  scalarExtensionRepresentative openScalarExtension openScalarExtensionZero
  ProEtale.etaleSheafExtendScalars ProEtale.etaleSheafExtendScalarsAdjunction
  constantSheaf Scheme.etaleSumFlatModuleRealization Scheme.etaleSumFlatComplexRealization
  derivedOpenImmersionLowerShriekUpperStarAdjunction Adjunction.mapDerivedCategoryAdjunction

set_option maxRecDepth 2048 in
private theorem sheetEquation_of_flat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [IsNoetherian U] [IsNoetherian X]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hz : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, exactFunctor _ _ (tensorRight (P.X n))) :
    sheetEquation φ j P := by
  have h := (etaleSumCoefficientComputation φ j
    (Compactification.ofIsOpenImmersion j) P hz hf).2.2.2.2.2.2.2.2.2.2.2.2.2
  have he : sheafCoefficientIso φ j = etaleSumScalarSheafIso φ j := by
    unfold sheafCoefficientIso etaleSumScalarSheafIso
    rfl
  have hs (R : Type (u + 1)) [CommRing R]
      (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)) (S : U.Etale) :
      sheetMap R j M S = etaleSumSheetMap R j M S := by
    unfold sheetMap etaleSumSheetMap
    rfl
  unfold sheetEquation
  intro n S x b
  have h' := h n S x b
  simp only [← hs, ← he] at h'
  dsimp only [openImmersionLowerShriek, etaleLowerShriek,
    localizationLowerShriek, Scheme.smallEtaleTopology] at h' ⊢
  exact h'


private theorem openExtension_eq_sum
    (R : Type (u + 1)) [CommRing R] {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : openImmersionLowerShriek (ModuleCat.{u + 1} R) j =
      etaleLowerShriek (ModuleCat.{u + 1} R) j inferInstance := rfl

attribute [local irreducible] openImmersionLowerShriek etaleLowerShriek
  openImmersionLowerShriekUpperStarAdjunction etaleLowerShriekUpperStarAdjunction


private theorem identityBoundary
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (M : DerivedCategoryModule R T) :
    (Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} R) T) ≪≫
      (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryIdIso _).hom.app M =
      (rightDerivedLowerStarIdIso R T).hom.app M := by
  unfold rightDerivedLowerStarIdIso
  simp only [Iso.trans_hom, NatTrans.comp_app]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ (Functor.mapDerivedCategoryIdIso _).hom.app M)
      (rightDerivedFunctorNatIso_hom_app_comp_isoMapDerivedCategory_hom_app
        (lowerStarId (ModuleCat.{u + 1} R) T) M)

private theorem identityMate_boundary
    {C D : Type*} [Category C] [Category D] (S : C ⥤ D)
    {F : C ⥤ C} {G : D ⥤ D} (e : F ≅ 𝟭 C) (f : G ≅ 𝟭 D)
    (α : F ⋙ S ⟶ S ⋙ G) (M : C)
    (h : α.app M ≫ f.hom.app (S.obj M) = S.map (e.hom.app M))
    {N : D} (t : S.obj M ⟶ N) :
    S.map (e.inv.app M) ≫ (α.app M ≫ G.map t) ≫ f.hom.app N = t := by
  simp only [Category.assoc]
  have hn := f.hom.naturality t
  dsimp only [Functor.id_map] at hn
  rw [hn, reassoc_of% h, ← S.map_comp_assoc, Iso.inv_hom_id_app,
    S.map_id, Category.id_comp]

private theorem coefficientMap_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategoryModule A U) :
    coefficientMap φ j K = (openScalarExtension φ j).hom.app K := by
  have hi : properOpenCoefficientOpenInverse φ j K =
      (openScalarExtension φ j).inv.app K := by
    unfold properOpenCoefficientOpenInverse
    apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) j).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact (scalarOpen_unit φ j K).symm
  have hei : properOpenCoefficientOpenIso φ j K = (openScalarExtension φ j).app K := by
    apply Iso.ext_inv
    exact hi
  have ho := congrArg Iso.hom hei
  have hid := scalarMate_directImage_identity φ X
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)
  rw [identityBoundary, identityBoundary] at hid
  unfold coefficientMap ProEtale.CoefficientCompatibility.etaleCoefficientMap
  exact (identityMate_boundary (scalarExtension φ X)
    (rightDerivedLowerStarIdIso A X) (rightDerivedLowerStarIdIso B X)
    (scalarMate φ (𝟙 X)) _ hid (properOpenCoefficientOpenIso φ j K).hom).trans ho

private theorem exactFactors_on_quotient
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app P ≫
    𝟙 _ ≫ _root_.DerivedCategory.Qh.map (𝟙 _) = _
  erw [F.mapDerivedCategory.map_id, _root_.DerivedCategory.Qh.map_id]
  erw [Category.id_comp, Category.id_comp]
  exact Category.comp_id _

private theorem mapComplex_counit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
    (P : CochainComplex D ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F)) (.up ℤ)).hom.app P ≫
      (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app P ≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P =
      (adj.mapHomologicalComplex (.up ℤ)).counit.app P := by
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Iso.refl_hom, NatTrans.id_app, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f, Adjunction.mapHomologicalComplex_counit_app_f]
  erw [Category.id_comp, Category.comp_id]

private theorem exactCounit_on_complex
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [monC : MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex D ℤ) :
    adj.mapDerivedCategoryAdjunction.counit.app (_root_.DerivedCategory.Q.obj P) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        _root_.DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app P) := by
  have h := adj.mapDerivedCategoryAdjunction_counit_app_Qh_obj
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [exactFactors_on_quotient] at h
  change _ = _ ≫ F.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫ _ at h
  rw [exactFactors_on_quotient] at h
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  exact h

private theorem sheafCounit_on_complex
    (W : Type*) [Category.{u + 1} W] [Abelian W] [IsGrothendieckAbelian.{u + 1} W]
    [MonoidalCategory W] [MonoidalPreadditive W] [SymmetricCategory W] [MonoidalClosed W]
    [Abelian.HasFunctorialFlatResolution W]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology W) ℤ) :
    (openImmersionLowerShriek W j).mapDerivedCategory.map
        ((upperStar W j).mapDerivedCategoryFactors.hom.app P) ≫
      (openImmersionLowerShriek W j).mapDerivedCategoryFactors.hom.app
        (((upperStar W j).mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map
        (((openImmersionLowerShriekUpperStarAdjunction W j).mapHomologicalComplex
          (.up ℤ)).counit.app P) =
    (derivedOpenImmersionLowerShriekUpperStarAdjunction W j).counit.app
      (_root_.DerivedCategory.Q.obj P) := by
  unfold derivedOpenImmersionLowerShriekUpperStarAdjunction
  symm
  apply exactCounit_on_complex
    (monC := Etale.sheafMonoidalCategory W U)

section EvaluationModel

set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Functor.mapHomologicalComplex _root_.DerivedCategory.Q

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem evaluationModelEquation_all
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    evaluationModelEquation A j P := by
  unfold evaluationModelEquation evaluationComplexMap
  exact sheafCounit_on_complex (ModuleCat.{u + 1} A) j P

end EvaluationModel

private theorem operationModels_of_iso
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (K : DerivedCategoryModule A X) (e : _root_.DerivedCategory.Q.obj P ≅ K) :
    operationModels A j P K := by
  let F := upperStar (ModuleCat.{u + 1} A) j
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let NU := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U
  let NX := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let eF := (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e
  let eJ := (J.mapDerivedCategoryFactors.app FP).symm ≪≫ J.mapDerivedCategory.mapIso eF
  let r : NX.mapDerivedCategory ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ NU.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  let z : NU.mapDerivedCategory ⋙
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ≅
      J.mapDerivedCategory ⋙ NX.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) j).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  unfold operationModels
  exact ⟨⟨eF⟩, ⟨eJ⟩,
    ⟨(NU.mapDerivedCategoryFactors.app FP).symm ≪≫
      NU.mapDerivedCategory.mapIso eF ≪≫ (r.app K).symm⟩,
    ⟨(NX.mapDerivedCategoryFactors.app
      ((J.mapHomologicalComplex (.up ℤ)).obj FP)).symm ≪≫
      NX.mapDerivedCategory.mapIso eJ ≪≫ (z.app (F.mapDerivedCategory.obj K)).symm ≪≫
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.mapIso
        (r.app K).symm⟩⟩

attribute [local irreducible] Scheme.etaleConstantModuleFunctor
  Scheme.etaleConstantModuleRealization sheafCompose presheafToSheaf
  constantModuleHomRingIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem realizedKFlat_of_flat
    (A : Type (u + 1)) [CommRing A] (U : Scheme.{u})
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (b : ℤ) (hz : ∀ n, b < n → IsZero (P.X n))
    (hf : ∀ n, ObjectProperty.flat (P.X n)) : etaleKFlat U A P := by
  let R := (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let Q := (Scheme.etaleSumFlatComplexRealization U A).obj P
  have hQ (n : ℤ) : Q.X n =
      (Scheme.etaleSumFlatModuleRealization U A).obj (P.X n) := by
    dsimp only [Q]
    unfold Scheme.etaleSumFlatModuleRealization Scheme.etaleSumFlatComplexRealization
    rfl
  let : (Scheme.etaleSumFlatModuleRealization U A).IsEquivalence := by
    have h := Scheme.etaleSumTensorTestRealization_isEquivalence U A
    unfold Scheme.etaleSumFlatModuleRealization
    unfold Scheme.etaleSumTensorTestRealization at h
    exact h
  have : Q.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff Q b).mpr
    (fun n hn ↦ by
      rw [hQ]
      exact (Scheme.etaleSumFlatModuleRealization U A).map_isZero (hz n hn))
  change Q.IsKFlatIndependentCoefficients
  exact
    SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R Q b
      (fun n ↦ by
        rw [hQ]
        unfold Scheme.etaleSumFlatModuleRealization
        exact (Scheme.etaleConstantModule_flat_iff U A (P.X n)).mp (hf n))

private theorem mapComplex_comp_identity
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive D'] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {F' : C ⥤ D'} {G' : D' ⥤ E}
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    (e : F ⋙ G ≅ F' ⋙ G') (P : CochainComplex C ℤ) :
    (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G')) (.up ℤ)).inv.app P =
      (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app]
  exact Category.comp_id _

private theorem mapped_boundary_cancel
    {C D : Type*} [Category C] [Category D] (S : C ⥤ D)
    {M N : C} (e : M ≅ N) {Z : D} (f : S.obj M ⟶ Z) (g : S.obj N ⟶ Z)
    (h : f = S.map e.hom ≫ g) : S.map e.inv ≫ f = g := by
  rw [h, ← S.map_comp_assoc, e.inv_hom_id, S.map_id, Category.id_comp]

section CoefficientModel

set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Functor.mapHomologicalComplexCompIso
  NatIso.mapHomologicalComplex NatTrans.mapHomologicalComplex _root_.DerivedCategory.Q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryScalarIso_eq
  {A B : Type (u + 1)} [CommRing A] [CommRing B]
  (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openScalarExtensionZero φ j = sheafCoefficientIso φ j := by
  have ht : (openRestrictScalarsIso φ j).symm =
      upperStarRestrictScalarsIsoSheaf φ j :=
    Iso.ext (openRestrictScalarsIso_inv_eq φ j)
  have hres : openRestrictScalarsIso φ j =
      (upperStarRestrictScalarsIsoSheaf φ j).symm := by
    simpa only [Iso.symm_symm_eq] using congrArg Iso.symm ht
  unfold openScalarExtensionZero sheafCoefficientIso
  rw [hres]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryComplexMap_eq
  {A B : Type (u + 1)} [CommRing A] [CommRing B]
  (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientComplexMap φ j P =
    (Functor.mapHomologicalComplexCompIso (openScalarExtensionZero φ j) (.up ℤ)).hom.app P := by
  unfold coefficientComplexMap
  rw [ordinaryScalarIso_eq]


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem coefficientModelEquation_of_flat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (b : ℤ) (hz : ∀ n, b < n → IsZero (P.X n))
    (hf : ∀ n, ObjectProperty.flat (P.X n)) : coefficientModelEquation φ j P := by
  have hk := realizedKFlat_of_flat A U P b hz hf
  have h := (etaleOpenTensorComparisons φ j).q_normalized P hk
  unfold coefficientModelEquation
  rw [coefficientMap_eq, ordinaryComplexMap_eq]
  exact mapped_boundary_cancel (scalarExtension φ X)
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.app P)
    _ _ h

end CoefficientModel

private theorem flat_constructible_model_any_interval
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategoryModule A X) (hK : DerivedCategory.isBoundedConstructible A X K)
    (a b : ℤ) (ht : DerivedCategory.hasTorAmplitudeIn A X a b K) :
    ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      (∀ n, ObjectProperty.flat (P.X n)) ∧
      (∀ n, IsConstructibleEtaleModuleSheaf (P.X n)) ∧
      (∀ n, n < a ∨ b < n → IsZero (P.X n)) ∧
      Nonempty (_root_.DerivedCategory.Q.obj P ≅ K) := by
  by_cases hab : a ≤ b
  · exact (hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel A X a b hab K hK).mp ht
  · have hzero : IsZero K := by
      obtain ⟨hge, hle⟩ := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
        (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht)
      have : K.IsGE a := hge
      have : K.IsLE b := hle
      exact _root_.DerivedCategory.TStructure.t.isZero K b a (lt_of_not_ge hab)
    let P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ := 0
    have hz (n : ℤ) : IsZero (P.X n) :=
      (HomologicalComplex.eval _ (.up ℤ) n).map_isZero (isZero_zero _)
    refine ⟨P, fun n ↦ ObjectProperty.flat_of_isZero (hz n), ?_, fun n _ ↦ hz n, ?_⟩
    · intro n
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
        (Scheme.IsConstructibleSheaf.of_isZero (hz n))
    · exact ⟨(_root_.DerivedCategory.Q.map_isZero (isZero_zero _)).iso hzero⟩

/-- The coefficient square and model operations for one exceptional object. This is the
strict model-theoretic sub-result used below; its proof is the coefficient/site-square
normalization from the cited blueprint node.
(blueprint: lem-sp-etale-open-counit-flat-models). -/
private theorem coefficient_model_package
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [IsNoetherian U] [IsNoetherian X]
    (K : DerivedCategoryModule A X)
    (hK : ProEtale.exceptionalTransportEtaleObjects A X K)
    (a b : ℤ) (ht : DerivedCategory.hasTorAmplitudeIn A X a b K) :
    ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      Nonempty (_root_.DerivedCategory.Q.obj P ≅ K) ∧
      operationModels A j P K ∧ scalarSiteModels φ X a b P ∧
      scalarSiteModels φ U a b
        (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ∧
      scalarSiteModels φ X a b
        (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (.up ℤ)).obj
          (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      coefficientModelEquation φ j
        (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ∧
      sheetEquation φ j
        (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ∧
      evaluationModelEquation A j P ∧
      evaluationModelEquation B j (coefficientExtendedComplex φ X P) := by
  obtain ⟨P, hf, hc, hz, ⟨e⟩⟩ := flat_constructible_model_any_interval A X K hK.1 a b ht
  let F := upperStar (ModuleCat.{u + 1} A) j
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let JP := (J.mapHomologicalComplex (.up ℤ)).obj FP
  have hfF (n : ℤ) : ObjectProperty.flat (FP.X n) :=
    Functor.PreservesFlat.flat_obj (F := F) (hf n)
  have hcF (n : ℤ) : IsConstructibleEtaleModuleSheaf (FP.X n) := by
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc n)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.upperStar j (P.X n))
  have hzF (n : ℤ) (hn : n < a ∨ b < n) : IsZero (FP.X n) := F.map_isZero (hz n hn)
  have hfJ (n : ℤ) : ObjectProperty.flat (JP.X n) :=
    by
      let e : openImmersionLowerShriek (ModuleCat.{u + 1} A) j ≅
          etaleLowerShriek (ModuleCat.{u + 1} A) j inferInstance :=
        eqToIso (openExtension_eq_sum A j)
      exact ObjectProperty.prop_of_iso _ (e.app (FP.X n)).symm
        (Functor.PreservesFlat.flat_obj
          (F := etaleLowerShriek (ModuleCat.{u + 1} A) j inferInstance) (hfF n))
  have hcJ (n : ℤ) : IsConstructibleEtaleModuleSheaf (JP.X n) := by
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hcF n)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.openImmersionLowerShriek_of_quasiCompact j (FP.X n))
  have hzJ (n : ℤ) (hn : n < a ∨ b < n) : IsZero (JP.X n) := J.map_isZero (hzF n hn)
  refine ⟨P, ⟨e⟩, operationModels_of_iso A j P K e,
    scalarSiteModels_of_flat φ X a b P (fun n ↦ (hf n).2) hc hz,
    scalarSiteModels_of_flat φ U a b FP (fun n ↦ (hfF n).2) hcF hzF,
    scalarSiteModels_of_flat φ X a b JP (fun n ↦ (hfJ n).2) hcJ hzJ,
    coefficientModelEquation_of_flat φ j FP b (fun n hn ↦ hzF n (.inr hn)) hfF,
    sheetEquation_of_flat φ j FP ⟨a, b, hzF⟩ (fun n ↦ (hfF n).2),
    evaluationModelEquation_all A j P,
    evaluationModelEquation_all B j (coefficientExtendedComplex φ X P)⟩


/-- The identity-proper coefficient map is invertible and its counit composite is scalar
extension. This is the strict normalization sub-result used in the final theorem.
(blueprint: lem-sp-etale-open-counit-flat-models). -/
private theorem coefficient_counit_package
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L : DerivedCategoryModule A U) :
    IsIso (coefficientMap φ j L) ∧
      ∀ K : DerivedCategoryModule A X,
      coefficientMap φ j ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ j).inv.app K) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).counit.app ((scalarExtension φ X).obj K) =
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app K) := by
  constructor
  · rw [coefficientMap_eq]
    infer_instance
  · intro K
    rw [coefficientMap_eq]
    have h := (etaleOpenTensorComparisons φ j).counit K
    rw [openScalarRestriction_eq] at h
    exact h


/-- Finite-Tor open domains, their bounded flat input models, the identity-proper-factor
coefficient normalization and the actual evaluation-counit equation.

Source: blueprint main-20261015, det-sp-reduction-exceptional, Locality; Stacks 0GL6,
09AL, 03TT, 0963, 0E8I, 03DI, 06YQ and 0G7E
(blueprint: lem-sp-etale-open-counit-flat-models).

Proof:
1. Finite type over the field makes U and X Noetherian. The intrinsic constructible
comparison and fixed-coefficient Tor comparison identify the two finite-Tor domains.
Full faithfulness on bounded-below objects and essential surjectivity give the restricted
comparison equivalence.
2. Exact restriction and quasi-compact open extension preserve the etale finite-Tor
category. Their canonical site-comparison squares transport preservation to the
intrinsic pro-etale category. The finite coefficient input model theorem gives scalar
preservation on etale objects and their comparison images; essential surjectivity gives
it on all intrinsic pro-etale objects.
3. Choose a flat constructible representative in the requested Tor interval. If the
interval is empty, the object is zero and the zero complex works. Restriction and open
extension preserve flat constructible terms and zero terms. Apply the bounded-flat
coefficient/site-square theorem to all three complexes. The exact-localization factor
isomorphisms and site-comparison squares give all operation models.
4. Normalize the identity proper factor using the scalarMate identity law and
compatibility of right-derived and exact-derived natural isomorphisms. Characterize the
open inverse by its adjunction transpose and identify it with openScalarExtension.inv.
Thus the specified coefficientMap is openScalarExtension.hom.
5. The canonical constant-module realization takes each bounded flat complex to an
independent-coefficient K-flat complex. The open tensor model normalization, after
cancelling its exact-localization boundary, gives coefficientModelEquation. The open
and etale sum adjunctions agree, so the sheetwise sum formula gives sheetEquation.
6. The exact-derived counit on a localized complex is the localization of the degreewise
ordinary counit, with the two exact factor maps. This proves evaluationModelEquation
over both coefficient rings. The canonical open tensor counit law and its normalized
restriction comparison then give the final coefficient/counit equality. -/
theorem etaleOpenCounitFlatModels
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hpell : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B) :
    openDomains A j ∧ openDomains B j ∧
    (∀ L : DerivedCategoryModule A U,
      ProEtale.exceptionalTransportEtaleObjects A U L → IsIso (coefficientMap φ j L)) ∧
    (∀ T : Scheme.{u}, T ∈ [U, X] →
      (∀ K, ProEtale.exceptionalTransportEtaleObjects A T K →
        ProEtale.exceptionalTransportEtaleObjects B T ((scalarExtension φ T).obj K)) ∧
      (∀ M, ProEtale.exceptionalTransportProEtaleObjects A T M →
        ProEtale.exceptionalTransportProEtaleObjects B T
          ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).obj M))) ∧
    ∀ K : DerivedCategoryModule A X,
      ProEtale.exceptionalTransportEtaleObjects A X K →
      (∀ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K →
        ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
          Nonempty (_root_.DerivedCategory.Q.obj P ≅ K) ∧
          operationModels A j P K ∧
          scalarSiteModels φ X a b P ∧
          scalarSiteModels φ U a b
            (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ∧
          scalarSiteModels φ X a b
            (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
              (.up ℤ)).obj
              (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P)) ∧
          coefficientModelEquation φ j
            (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ∧
          sheetEquation φ j
            (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ∧
          evaluationModelEquation A j P ∧
          evaluationModelEquation B j (coefficientExtendedComplex φ X P)) ∧
      IsIso (coefficientMap φ j
        ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)) ∧
      coefficientMap φ j
          ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ j).inv.app K) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).counit.app
            ((scalarExtension φ X).obj K) =
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app K) := by
  let := isNoetherian_of_locallyOfFiniteType (U ↘ Spec (.of k))
  let := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have hdomA : openDomains A j := openDomains_of_noetherian A j
  have hdomB : openDomains B j := openDomains_of_noetherian B j
  refine ⟨hdomA, hdomB, ?_, ?_, ?_⟩
  · intro L hL
    exact (coefficient_counit_package φ j L).1
  · intro T hT
    have hT' : T = U ∨ T = X := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hT
    rcases hT' with rfl | rfl
    · exact scalar_preserves ell _hA _hB φ _
    · exact scalar_preserves ell _hA _hB φ _
  · intro K hK
    refine ⟨?_, ?_⟩
    · intro a b ht
      exact coefficient_model_package φ j K hK a b ht
    · have hcoef := coefficient_counit_package φ j
        ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)
      exact ⟨hcoef.1, hcoef.2 K⟩


end OpenCounitFlatModels
end AlgebraicGeometry.Etale
