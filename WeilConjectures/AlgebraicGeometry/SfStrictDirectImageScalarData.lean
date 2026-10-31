/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.CompletedCoefficientPushforwardComparison
public import WeilConjectures.AlgebraicGeometry.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.SfScalarExtensionComposition
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleLinear
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
/-! # Scalar comparison for the specified strict-tower direct image

Source: blueprint, sec-smooth-purity/sk-prop-sf-closed-unit,
rational-stage and algebraically closed-stage scalar comparisons; Stacks 0D6E and 0A07
(blueprint: lem-sf-strict-direct-image-scalar-comparison).

The statement retains the strict complex diagram, its quotient augmentation, the
universal derived units, and the tensor-generator normalization of the ambient comparison.
Its rational categories are the existing raw tensor-Hom localizations.

## Main definitions

* `IntegralModel` retains the strict realization and normalized reconstruction.
* `AmbientComparison` and `IntegralComparisons` retain the canonical scalar maps.
* `Comparisons` retains the raw rational direct images and comparison components.
* `HasIntegralLaws` and `HasComparisonLaws` state all normalization and coherence laws.

The existence theorem remains in `SfStrictDirectImageScalarComparison`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct
namespace WeilConjectures.SfStrictDirectImageScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Good representatives of integral constructible objects, with no chosen resolutions.
Source: blueprint strict-diagram realization, Stacks 06YS
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
def Representatives (W : Scheme.{u}) :
    ObjectProperty (CochainComplex (scalarReductionSource l E W) ℤ) :=
  fun P ↦ integralOperationsGoodComplex l E W P ∧
    sfIntegralConstructible l E W (DerivedCategory.Q.obj P)

/-- The existing localization restricted to these representatives.
Source: Stacks 06YS (blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
def representativeLocalization (W : Scheme.{u}) :
    (Representatives l E W).FullSubcategory ⥤ sfIntegralConstructibleCategory l E W :=
  ObjectProperty.lift (sfIntegralConstructible l E W)
    ((Representatives l E W).ι ⋙ DerivedCategory.Q) (fun P ↦ P.property.2)

/-- The actual strict quotient tower on a complex, including its transition maps.
This is just the existing sequence of natural reduction functors, curried.
Source: Bhatt--Scholze 3.5.2
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
abbrev strictReduction (W : Scheme.{u}) :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
    (unrestrictedIntegralTransition l E W)).flip

set_option genSizeOf false in
set_option genInjectivity false in
/-- A functorial strict-diagram realization with the normalized reconstruction map.
The diagram is specified before applying its total derived direct image and limit.
The comparison is fixed on every flat-term K-flat constructible representative by
its actual augmentation, rather than by its evaluated projections.
Source: blueprint strict-realization and reconstruction paragraphs; Stacks 0D6E, 0A07
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
structure IntegralModel {Z X : Scheme.{u}} (f : Z ⟶ X) where
  diagrams : CompletedCoefficientPushforward.ComparisonData l E f
  structureMap : diagrams.structureMap =
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (sfCompletedCoefficientMap l E f)
  ambient : diagrams.completedImage.functor ≅ sfCompletedDerivedDirectImage l E f
  ambient_unit : ∀ P : CochainComplex (scalarReductionSource l E Z) ℤ,
    HEq (diagrams.completedImage.unit.app P ≫ ambient.hom.app (DerivedCategory.Q.obj P))
      ((sfCompletedModuleDirectImage l E f).rightDerivedFunctorUnitQ P)
  image : sfIntegralConstructibleCategory l E Z ⥤ sfIntegralConstructibleCategory l E X
  strict : (Representatives l E Z).FullSubcategory ⥤
    CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Z) ℤ
  strict_identification : strict ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
    (Representatives l E Z).ι ⋙ strictReduction l E Z
  realization : representativeLocalization l E Z ⋙ image ⋙ (sfIntegralConstructible l E X).ι ≅
    strict ⋙ DerivedCategory.Q ⋙ diagrams.towerImage.functor ⋙ diagrams.target.limit.functor
  reconstruction : (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E f ≅
    image ⋙ (sfIntegralConstructible l E X).ι
  reconstruction_normalization : ∀ (P : (Representatives l E Z).FullSubcategory)
    (a : P.obj ⟶ ((CompletedCoefficientPushforward.ordinaryTowerLimit l E Z).mapHomologicalComplex
      (.up ℤ)).obj (strict.obj P)),
    (∀ (n : ℕ) (i : ℤ) (U : Z.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
      HEq (((a.f i ≫ limit.π ((strict.obj P).X i) (op n) ≫
        (((strict_identification.app P).hom.app (op n)).f i)).val.app U) x)
        (unrestrictedIntegralTensorSection l E Z n (P.obj.X i) U 1 x)) →
    reconstruction.hom.app ((representativeLocalization l E Z).obj P) ≫
        realization.hom.app P =
      ambient.inv.app (DerivedCategory.Q.obj P.obj) ≫
        diagrams.completedImage.functor.map
          (DerivedCategory.Q.map a ≫ diagrams.source.limit.unit.app (strict.obj P)) ≫
        diagrams.limitComparison.hom.app (DerivedCategory.Q.obj (strict.obj P))
  additive : image.Additive
  linear : image.Linear (Padic.coefficientExtensionIntegers l E)
  scalars : ∀ (a : Padic.coefficientExtensionIntegers l E)
    (K : sfIntegralConstructibleCategory l E Z),
    (sfCompletedDerivedDirectImage l E f).map (a • 𝟙 K.obj) ≫ reconstruction.hom.app K =
      reconstruction.hom.app K ≫ (a • 𝟙 (image.obj K).obj)
  [shift : image.CommShift ℤ]
  reconstruction_shift : NatTrans.CommShift reconstruction.hom ℤ

attribute [instance] IntegralModel.additive IntegralModel.linear IntegralModel.shift

/-- The universal unit/counit square specifying the derived ambient comparison.
Source: blueprint inverse ambient scalar comparison, Stacks 0D6E
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
def IsAmbientNormalization
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {Z X : Scheme.{u}} (f : Z ⟶ X)
    (ordinary : sfCompletedModuleDirectImage l E f ⋙
        completedOrdinaryScalarExtension l E L
          ι X ≅
      completedOrdinaryScalarExtension l E L
          ι Z ⋙
        sfCompletedModuleDirectImage l L f)
    (ambient : sfCompletedDerivedDirectImage l E f ⋙ completedDerivedScalarExtension l E L ι X ≅
      completedDerivedScalarExtension l E L ι Z ⋙ sfCompletedDerivedDirectImage l L f) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E Z) ℤ),
    (completedDerivedScalarExtension l E L ι X).map
        ((sfCompletedModuleDirectImage l E f).rightDerivedFunctorUnitQ P) ≫
        ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (sfCompletedDerivedDirectImage l L f).map
          (completedScalarCounit l E L
            ι Z P) =
      completedScalarCounit l E L
          ι X
          (((sfCompletedModuleDirectImage l E f).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) ≫
        (sfCompletedModuleDirectImage l L f).rightDerivedFunctorUnitQ
          ((completedOrdinaryScalarComplex l E L
            ι Z).obj P)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The specified integral comparisons and their raw rationalizations.
The ordinary comparison is fixed on sheafified tensor generators; the universal
unit/counit equation fixes its derived comparison. The integral conjugation equation
uses precisely the recorded quotient-completion maps, and the rational components
are their literal localized images. No idempotent splittings or fullness claims occur.
Source: blueprint scalar-comparison and rational-cocycle paragraphs; Stacks 0D6E
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
structure AmbientComparison
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {Z X : Scheme.{u}} (f : Z ⟶ X) where
  ordinary : sfCompletedModuleDirectImage l E f ⋙
        completedOrdinaryScalarExtension l E L
          ι X ≅
      completedOrdinaryScalarExtension l E L
          ι Z ⋙
        sfCompletedModuleDirectImage l L f
  ordinary_tensors : ∀ (N : scalarReductionSource l E Z) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
    (x : N.val.obj ((proEtaleBaseChange f).op.obj U)),
    (ordinary.hom.app N).val.app U
        (completedScalarTensorSection l E L
          ι X
          ((sfCompletedModuleDirectImage l E f).obj N) U s x) =
      completedScalarTensorSection l E L
        ι Z N ((proEtaleBaseChange f).op.obj U)
        ((sfCompletedCoefficientMap l L f).hom.app U s) x
  ambient : sfCompletedDerivedDirectImage l E f ⋙ completedDerivedScalarExtension l E L ι X ≅
      completedDerivedScalarExtension l E L ι Z ⋙ sfCompletedDerivedDirectImage l L f
  ambient_normalization : IsAmbientNormalization l E L ι f ordinary ambient


variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage transition integralTransition associator unitor)

/-- Ordinary completed-coefficient tensor along the specified field inclusion.
Source: blueprint scalar-comparison formula
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
abbrev scalar (W : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L) :=
  completedDerivedScalarExtension l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) W

/-- The integral scalar unit with the prescribed coefficient-identity transport.
Source: blueprint identity-extension clause
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
def integralUnit (W : Scheme.{u}) (E : Index l Ω) :
    integralTransition l Ω W E E le_rfl ≅ 𝟭 _ :=
  eqToIso (congrArg
    (fun ι ↦ sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω E) ι W)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) ≪≫
    sfIntegralScalarUnit l (Coefficient.{u} l Ω E) W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime))

/-- The existing raw localization, with its target named as the finite stage.
Source: blueprint rationalization paragraph
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
def stageLocalization (W : Scheme.{u}) (E : Index l Ω) :
    sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W ⥤ Stage l Ω W E :=
  sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) W

/-- Cache the published localization shift with the named stage as target.
Source: blueprint rationalization paragraph
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
instance stageLocalizationShift (W : Scheme.{u}) (E : Index l Ω) :
    (stageLocalization l Ω W E).CommShift ℤ :=
  sfRationalLocalizationCommShift l (Coefficient.{u} l Ω E) W

attribute [local irreducible] completedOrdinaryScalarExtension completedOrdinaryScalarComplex
attribute [local irreducible] integralUnit completedScalarChangeData
  completedScalarComparison completedDerivedScalarExtension HasDerivedCategory.standard
  sfIntegralScalarUnit sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.unitor
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The conjugation equation fixing the integral scalar comparison.
Source: blueprint scalar comparison formula
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
def IsIntegralNormalization {Z X : Scheme.{u}} (f : Z ⟶ X)
    (ambientData : ∀ (E L : Index l Ω) (h : E ≤ L),
      AmbientComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) f)
    (integral : ∀ E : Index l Ω, IntegralModel l (Coefficient.{u} l Ω E) f)
    (integralComparison : ∀ (E L : Index l Ω) (h : E ≤ L),
      integralTransition l Ω Z E L h ⋙ (integral L).image ≅
        (integral E).image ⋙ integralTransition l Ω X E L h) : Prop :=
  ∀ (E L : Index l Ω) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Z),
    (sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω L) f).map
        ((completedScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) Z).app K.obj) ≫
        (integral L).reconstruction.hom.app ((integralTransition l Ω Z E L h).obj K) ≫
        ((integralComparison E L h).hom.app K).hom =
      (ambientData E L h).ambient.inv.app K.obj ≫
        (completedScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) X).app
          ((sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω E) f).obj K.obj) ≫
        (integralScalarExtensionOfUniverses l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) X).map ((integral E).reconstruction.hom.app K)


set_option genSizeOf false in
set_option genInjectivity false in
/-- Restrict the normalized ambient comparison to the specified strict images.
Source: blueprint integral scalar comparison and identity-extension formula
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
structure IntegralComparisons {Z X : Scheme.{u}} (f : Z ⟶ X)
    where
  ambientData : ∀ (E L : Index l Ω) (h : E ≤ L),
    AmbientComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) f
  integral : ∀ E : Index l Ω, IntegralModel l (Coefficient.{u} l Ω E) f
  integralComparison : ∀ (E L : Index l Ω) (h : E ≤ L),
    integralTransition l Ω Z E L h ⋙ (integral L).image ≅
      (integral E).image ⋙ integralTransition l Ω X E L h

/-- Normalization and the prescribed integral identity-extension unit.
Source: blueprint scalar conjugation and unit clauses
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
def HasIntegralLaws {Z X : Scheme.{u}} (f : Z ⟶ X)
    (D : IntegralComparisons l Ω f) : Prop :=
  IsIntegralNormalization l Ω f D.ambientData D.integral D.integralComparison ∧
  (∀ (E : Index l Ω)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Z),
    (D.integralComparison E E le_rfl).hom.app K ≫
        (integralUnit l Ω X E).hom.app ((D.integral E).image.obj K) =
      (D.integral E).image.map ((integralUnit l Ω Z E).hom.app K))

/-- Literal pure-tensor formula for raw rational direct image.
Source: blueprint rationalization paragraph
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
def IsRationalMaps {Z X : Scheme.{u}} (f : Z ⟶ X)
    (data : IntegralComparisons l Ω f)
    (rational : ∀ E : Index l Ω, Stage l Ω Z E ⥤ Stage l Ω X E) : Prop :=
  ∀ (E : Index l Ω)
    (K K' : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Z)
    (g : K ⟶ K') (a : Localization.Away
      (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω E))),
    HEq ((rational E).map
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E)] g :
        (stageLocalization l Ω Z E).obj K ⟶
        (stageLocalization l Ω Z E).obj K'))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E)]
        (data.integral E).image.map g :
        (stageLocalization l Ω X E).obj
          ((data.integral E).image.obj K) ⟶
        (stageLocalization l Ω X E).obj
          ((data.integral E).image.obj K'))


set_option genSizeOf false in
set_option genInjectivity false in
/-- Raw rationalization of the normalized integral comparison system.
Source: blueprint rational scalar comparison, shift, unit and cocycle clauses
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
structure Comparisons {Z X : Scheme.{u}} (f : Z ⟶ X)
    (D : IntegralComparisons l Ω f) where
  rational : ∀ E : Index l Ω, Stage l Ω Z E ⥤ Stage l Ω X E
  rational_additive : ∀ E : Index l Ω, (rational E).Additive
  [rational_shift : ∀ E : Index l Ω, (rational E).CommShift ℤ]
  localization : ∀ E : Index l Ω,
    stageLocalization l Ω Z E ⋙ rational E ≅
      (D.integral E).image ⋙ stageLocalization l Ω X E
  theta : ∀ (E L : Index l Ω) (h : E ≤ L),
    transition l Ω Z E L h ⋙ rational L ≅ rational E ⋙ transition l Ω X E L h

attribute [instance] Comparisons.rational_shift

/-- The raw localized maps and their shift, unit and scalar-cocycle equalities.
Source: blueprint rationalization and scalar-coherence clauses
(blueprint: lem-sf-strict-direct-image-scalar-comparison). -/
def HasComparisonLaws {Z X : Scheme.{u}} (f : Z ⟶ X)
    (D : IntegralComparisons l Ω f) (R : Comparisons l Ω f D) : Prop :=
  (∀ (E : Index l Ω) (K : Stage l Ω Z E),
    (R.rational E).obj K = ⟨(D.integral E).image.obj K.obj⟩) ∧
  (IsRationalMaps l Ω f D R.rational) ∧
  (∀ (E : Index l Ω)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Z),
    HEq ((R.localization E).hom.app K)
      (𝟙 ((stageLocalization l Ω X E).obj
        ((D.integral E).image.obj K)))) ∧
  (∀ E : Index l Ω, NatTrans.CommShift (R.localization E).hom ℤ) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω Z E),
    HEq ((R.theta E L h).hom.app K)
      ((stageLocalization l Ω X L).map
        ((D.integralComparison E L h).hom.app K.obj))) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L), NatTrans.CommShift (R.theta E L h).hom ℤ) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω Z E),
    (R.theta E E le_rfl).hom.app K ≫ (unitor l Ω X E).hom.app ((R.rational E).obj K) =
      (R.rational E).map ((unitor l Ω Z E).hom.app K)) ∧
  (∀ (E L M : Index l Ω) (h : E ≤ L) (j : L ≤ M) (K : Stage l Ω Z E),
    (R.theta L M j).hom.app ((transition l Ω Z E L h).obj K) ≫
        (transition l Ω X L M j).map ((R.theta E L h).hom.app K) ≫
        (associator l Ω X E L M h j).hom.app ((R.rational E).obj K) =
      (R.rational M).map ((associator l Ω Z E L M h j).hom.app K) ≫
        (R.theta E M (h.trans j)).hom.app K)


attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.SfStrictDirectImageScalar
