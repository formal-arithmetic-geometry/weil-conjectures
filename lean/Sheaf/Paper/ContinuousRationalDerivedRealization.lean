/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.Paper.LocalizedTStructure
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.PbcQbarStandardCohomology
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.PbcRationalCategory
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.DerivedCountableSumsExact
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.CategoryTheory.DirectedTriangulatedImage
import Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness
import Sheaf.Paper.LisseEConstructibleIntegralLattice
import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.Paper.IntegralTStructure
import Sheaf.Paper.FiniteModelStratumFiltration
import Sheaf.Paper.SfCommonStageWeilCohomology

/-! # Continuous rational derived realization

Source: Bhatt--Scholze, Proposition 6.8.14(2), Lemma 6.8.2(1), Proposition 6.8.11(3),
Definition 6.8.8 and Remark 6.8.15
(blueprint: lem-per-continuous-rational-derived-realization).

## Main definitions and statement

* `ContinuousRational.At`: normalized equivalence at one scheme.
* `ContinuousRational.Along`: canonical derived module pullback comparison.
* `ContinuousRational.Family`: coherent scheme and coefficient comparisons.
* `ContinuousRational.continuous_rational_derived_realization`: existence of this family.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.ContinuousRational

/-- The geometric hypotheses of BS 6.8.14, including the empty scheme.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure Base (l : ℕ) where
  scheme : Scheme.{u}
  [noetherian : IsNoetherian scheme]
  dimension : ∃ n : ℕ, topologicalKrullDim scheme ≤ n
  prime_unit : ∀ x : scheme, IsUnit (l : scheme.presheaf.stalk x)

attribute [instance] Base.noetherian

/-- The recorded dimension bound as a typeclass argument.
Source: BS 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
instance baseDimension {l : ℕ} (X : Base.{u} l) :
    Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) := ⟨X.dimension⟩

/-- The recorded scheme-level invertibility hypothesis.
Source: BS 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
instance basePrimeUnit {l : ℕ} (X : Base.{u} l) :
    Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x)) := ⟨X.prime_unit⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Constant continuous functions supply the field action on rational modules.
Source: BS 6.8.1 (blueprint: lem-per-continuous-rational-derived-realization). -/
def scalarSections (X : Scheme.{u}) :
    E →+* RingCat.sectionsSubring
      ((rationalCoefficientSheaf l X E).obj ⋙ forget₂ CommRingCat RingCat) := by
  letI := coefficientExtensionNormedField l E
  exact
    { toFun := fun a ↦ ⟨fun _ ↦ ContinuousMap.const _ (ULift.up a), fun _ ↦ rfl⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The field action induced by those constant sections.
Source: BS 6.8.1 (blueprint: lem-per-continuous-rational-derived-realization). -/
instance moduleLinear (X : Scheme.{u}) :
    Linear E (pbcModules X (rationalCoefficientSheaf l X E)) :=
  letI : Linear (RingCat.sectionsSubring
      ((rationalCoefficientSheaf l X E).obj ⋙ forget₂ CommRingCat RingCat))
      (pbcModules X (rationalCoefficientSheaf l X E)) :=
    SheafOfModules.homLinear (rationalCoefficientSheaf l X E).obj
      (((adicLisseForget X).obj (rationalCoefficientSheaf l X E)).property)
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (scalarSections l E X)
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (scalarSections l E X a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (scalarSections l E X a) g }

/-- The inherited field action on the ambient derived category.
Source: BS 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
instance derivedLinear (X : Scheme.{u}) :
    Linear E (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
  inferInstance

/-- Reuse the recorded constructible continuous-module predicate via its coefficient
encoding. Over the field E its finitely presented local models are exactly finite free models.
Source: BS 6.8.6 and 6.8.10
(blueprint: lem-per-continuous-rational-derived-realization). -/
abbrev IsConstructible (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (e : AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅ rationalCoefficientSheaf l X E)
    (F : pbcModules X (rationalCoefficientSheaf l X E)) : Prop :=
  AlgebraicGeometry.ProEtale.IsContinuousConstructible X
    (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ((pbcRestrict e.hom).obj F)

/-- The full ambient bounded constructible subcategory, using the recorded sheaf predicate.
Source: BS 6.8.8 (blueprint: lem-per-continuous-rational-derived-realization). -/
def IsDerivedConstructible (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (e : AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅ rationalCoefficientSheaf l X E) :
    ObjectProperty (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
  fun K ↦ (∃ a b : ℤ, K.IsGE a ∧ K.IsLE b) ∧
    ∀ r : ℤ, IsConstructible l E X e ((DerivedCategory.homologyFunctor _ r).obj K)

/-- The localized standard t-structure supplied by the recorded dependency.
Its two classes are uniquely specified as the strictly full images of integral bounds.
Source: BS 6.8.11 and 6.8.14
(blueprint: lem-per-continuous-rational-derived-realization). -/
def localizedT (X : Base.{u} l) :=
  (pbc_localized_tstructure X.scheme l E).choose

/-- Cohomology placed in degree zero, using the actual localized truncations and shift.
Source: BS 6.8.11 (blueprint: lem-per-continuous-rational-derived-realization). -/
def localizedCohomology (X : Base.{u} l) (r : ℤ) :=
  (localizedT l E X).truncLE r ⋙ (localizedT l E X).truncGE r ⋙
    shiftFunctor (PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) r

/-- A normalized realization at one scheme. Bijectivity on Homs and the exact essential-image
condition express an equivalence onto the full ambient subcategory. The natural integral
comparison and fraction equation fix this functor on representatives and all arrows.
Source: BS 6.8.2, 6.8.11, 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure At (X : Base.{u} l) where
  [topNoetherian : TopologicalSpace.NoetherianSpace X.scheme]
  encoding : AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X.scheme
    (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
      rationalCoefficientSheaf l X.scheme E
  encoding_normalization : ∀ (U : X.scheme.ProEtᵒᵖ)
      (f : C(U.unop.left, WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
      (x : U.unop.left),
    rationalCoefficientValue l E X.scheme U (encoding.hom.hom.app U (ULift.up f)) x =
      WithAbs.ofAbs (f x)
  strata_criterion : ∀ F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E),
    IsConstructible l E X.scheme encoding F ↔
      ∃ s : FiniteLocallyClosedStratification X.scheme, ∀ i : Fin s.n,
        ((proEtaleModuleInverseImage (s.immersion i)
          (rationalCoefficientSheaf l X.scheme E)).obj F).IsFiniteLocallyFree
  integralIso : pbcAdicCompletion X.scheme (pbcIntegralDatum l E) ≅
    integralCoefficientSheaf l X.scheme E
  finiteIso : ∀ n : ℕ,
    (pbcAdicRings X.scheme (pbcIntegralDatum l E)).obj (op n) ≅
      finiteContinuousCoefficientSheaf l X.scheme E n
  finite_normalization : ∀ (n : ℕ) (U : X.scheme.ProEtᵒᵖ)
      (a : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1)) (x : U.unop.left),
    finiteContinuousCoefficientValue l E X.scheme n U
      ((finiteIso n).hom.hom.app U
        (pbcFunctionScalars X.scheme (pbcIntegralDatum l E) n |>.app U |>.hom <| a)) x =
      integralCoefficientULift l E n a
  integral_normalization : ∀ (n : ℕ) (U : X.scheme.ProEtᵒᵖ)
      (s : (integralCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X.scheme n U
      ((integralIso.inv ≫ pbcAdicProjection X.scheme (pbcIntegralDatum l E) n ≫
        (finiteIso n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E X.scheme U s x)
  localizationIso : integralCoefficientLocalization l X.scheme E ≅
    rationalCoefficientSheaf l X.scheme E
  localization_normalization :
    integralCoefficientLocalizationNormalized l E X.scheme localizationIso.hom
  inclusion : integralCoefficientSheaf l X.scheme E ⟶ rationalCoefficientSheaf l X.scheme E
  inclusion_normalization : integralRationalCoefficientNormalized l E X.scheme inclusion
  J : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
    DerivedCategory (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
  [additive : J.Additive]
  [linear : J.Linear E]
  [shift : J.CommShift ℤ]
  triangulated : J.IsTriangulated
  fully_faithful : ∀ K L, Function.Bijective (J.map : (K ⟶ L) → (J.obj K ⟶ J.obj L))
  image : ∀ C, IsDerivedConstructible l E X.scheme encoding C ↔ ∃ K, Nonempty (J.obj K ≅ C)
  integral : pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙ J ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) ⋙
      pbcDerivedExtend (integralIso.hom ≫ inclusion)
  fractions : ∀ (K L : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))
      (f : K ⟶ L) (a : Localization.Away (pbcUniformizer l E)),
    J.map (a •
      (pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      pbcRationalCoefficientEquiv l E a •
        J.map ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map f)
  t_bounds : ∀ K (r : ℤ),
    ((localizedT l E X).le r K ↔ (J.obj K).IsLE r) ∧
      ((localizedT l E X).ge r K ↔ (J.obj K).IsGE r)
  heart : ∀ K, (localizedT l E X).heart K ↔
    ∃ F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E),
      IsConstructible l E X.scheme encoding F ∧
        Nonempty (J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F)
  cohomology : ∀ r : ℤ,
    pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        localizedCohomology l E X r ⋙ J ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) ⋙
        DerivedCategory.homologyFunctor _ r ⋙ pbcExtend (integralIso.hom ≫ inclusion) ⋙
          DerivedCategory.singleFunctor _ 0

attribute [instance] At.additive At.linear At.shift

/-- Ordinary ringed module inverse image for an arbitrary coefficient structure map.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
def modulePull {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage g).obj R ⟶ S) :=
  proEtaleModuleInverseImage g R ⋙ pbcExtend c

attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModelUp_isContinuous in
/-- The actual tensor unit over a base-changed site object, for arbitrary coefficients.
Source: BS 6.8.15; Stacks 03EL
(blueprint: lem-per-continuous-rational-derived-realization). -/
def moduleUnit {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage g).obj R ⟶ S)
    (M : pbcModules Y R) (U : Y.ProEt) (m : M.val.obj (op U)) :
    ((modulePull g c).obj M).val.obj (op ((proEtaleBaseChange g).obj U)) :=
  pbcTensorSection c ((proEtaleModuleInverseImage g R).obj M)
    (op ((proEtaleBaseChange g).obj U)) 1
    (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1} (proEtaleModelRingUnit g R)).unit.app
      ((proEtaleModuleToModel ((adicLisseForget Y).obj R)).obj M)).val.app
        (op (AsSmall.up.obj U)) m)

/-- Actual derived module inverse image: exact ring inverse image followed by derived tensor.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
def derivedPull {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage g).obj R ⟶ S) :=
  adicTowerPullback g R ⋙ pbcDerivedExtend c

/-- The canonical counit for derived module inverse image. The exact inverse-image
API inserts scalar extension along the identity ring map. The first two comparisons
remove precisely that identity tensor factor. Their section equation is multiplication,
and the final equation fixes the derived counit on every complex.
Source: BS 6.8.15; Stacks 03EL, 03EK
(blueprint: lem-per-continuous-rational-derived-realization). -/
def IsNormalizedPullCounit {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage g).obj R ⟶ S) [(modulePull g c).Additive]
    (δ : DerivedCategory.Q ⋙ derivedPull g c ⟶
      (modulePull g c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) : Prop :=
  ∃ (e : proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _) ⋙
        pbcExtend c ≅ modulePull g c)
    (eC : (proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R)
        (Iso.refl _)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcExtend c).mapHomologicalComplex (.up ℤ) ≅
      (modulePull g c).mapHomologicalComplex (.up ℤ)),
    (∀ P (n : ℤ), (eC.hom.app P).f n = e.hom.app (P.X n)) ∧
    (∀ (M : pbcModules Y R) (W : X.ProEtᵒᵖ) (s : S.obj.obj W)
        (m : ((proEtaleModuleInverseImage g R).obj M).val.obj W),
      (e.hom.app M).val.app W
        (pbcTensorSection c
          ((proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R)
            (Iso.refl _)).obj M) W s
          ((eqToHom ((completedAdicChangeData
            X (𝟙 ((adicTowerInverseImage g).obj R))).choose_spec.choose
              ((proEtaleModuleInverseImage g R).obj M))).val.app W
              (pbcTensorSection (𝟙 ((adicTowerInverseImage g).obj R))
                ((proEtaleModuleInverseImage g R).obj M) W 1 m))) =
        pbcTensorSection c ((proEtaleModuleInverseImage g R).obj M) W s m) ∧
    ∀ P, δ.app P =
      (pbcDerivedExtend c).map
          ((proEtaleRingDerivedPullbackFactors g R ((adicTowerInverseImage g).obj R)
            (Iso.refl _)).hom.app P) ≫
        pbcComplexCounit c
          (((proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R)
            (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (eC.hom.app P)

/-- The literal restriction of actual completed pullback, with its preservation certificate.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
abbrev integralPull {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (h : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj)) :=
  pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualCompletedPull g (pbcIntegralDatum l E)) h

/-- Raw rational pullback is tensor extension on the existing Hom modules.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
abbrev rawPull {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (h : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj)) :=
  pbcConditionalRational (pbcIntegralDatum l E)
    (pbcActualCompletedPull g (pbcIntegralDatum l E)) h (pbcUniformizer l E)

/-- Pullback comparison, normalized before completion by the ordinary balanced tensor map.
The coefficient map has its continuous-function adjunct. Its square with the integral
coefficient structure map ensures that it is also induced by all finite quotient maps.
Source: BS 6.8.2 and 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure Along {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aX : At l E X) (aY : At l E Y) where
  coefficient : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l Y.scheme E) ⟶
    rationalCoefficientSheaf l X.scheme E
  normalized : rationalCoefficientRestrictionNormalized l E g coefficient
  square : (adicTowerInverseImage g).map (aY.integralIso.hom ≫ aY.inclusion) ≫ coefficient =
    completedCoefficientMap g (pbcIntegralDatum l E) ≫ aX.integralIso.hom ≫ aX.inclusion
  [ordinaryAdditive : (modulePull g coefficient).Additive]
  counit : DerivedCategory.Q ⋙ derivedPull g coefficient ⟶
    (modulePull g coefficient).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  normalized_counit : IsNormalizedPullCounit g coefficient counit
  universal : (derivedPull g coefficient).IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso _ (.up ℤ))
  computes : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E)
      P → IsIso (counit.app P)
  balance : pbcExtend (aY.integralIso.hom ≫ aY.inclusion) ⋙ modulePull g coefficient ≅
    pbcActualModulePull g (pbcIntegralDatum l E) ⋙
      pbcExtend (aX.integralIso.hom ≫ aX.inclusion)
  balance_sections : ∀ (M : pbcModules Y.scheme (pbcAdicCompletion Y.scheme
      (pbcIntegralDatum l E))) (U : Y.scheme.ProEt)
      (a : (rationalCoefficientSheaf l Y.scheme E).obj.obj (op U)) (m : M.val.obj (op U)),
    (balance.hom.app M).val.app (op ((proEtaleBaseChange g).obj U))
      (moduleUnit g coefficient ((pbcExtend (aY.integralIso.hom ≫ aY.inclusion)).obj M) U
        (pbcTensorSection (aY.integralIso.hom ≫ aY.inclusion) M (op U) a m)) =
      pbcTensorSection (aX.integralIso.hom ≫ aX.inclusion)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj U))
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _ coefficient).hom.app
          (op U) a) (pbcActualModuleUnitSection g (pbcIntegralDatum l E) M U m)
  ambient : pbcDerivedExtend (aY.integralIso.hom ≫ aY.inclusion) ⋙
      derivedPull g coefficient ≅
    pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
      pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)
  balanceComplex :
    (pbcExtend (aY.integralIso.hom ≫ aY.inclusion)).mapHomologicalComplex (.up ℤ) ⋙
        (modulePull g coefficient).mapHomologicalComplex (.up ℤ) ≅
      (pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcExtend (aX.integralIso.hom ≫ aX.inclusion)).mapHomologicalComplex (.up ℤ)
  balanceComplex_components : ∀ P (n : ℤ),
    (balanceComplex.hom.app P).f n = balance.hom.app (P.X n)
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (pbcAdicCompletion Y.scheme (pbcIntegralDatum l E))) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := pbcAdicCompletion Y.scheme (pbcIntegralDatum l E)) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y.scheme)
      (R := pbcAdicCompletion Y.scheme (pbcIntegralDatum l E)) (P.X n)) →
    (derivedPull g coefficient).map
        (pbcComplexCounit (aY.integralIso.hom ≫ aY.inclusion) P) ≫
        counit.app (((pbcExtend (aY.integralIso.hom ≫ aY.inclusion)).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ DerivedCategory.Q.map (balanceComplex.hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)).map
          (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
        pbcComplexCounit (aX.integralIso.hom ≫ aX.inclusion)
          (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex
            (.up ℤ)).obj P)
  integral_mem : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)
      ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj)
  comparison : rawPull l E g integral_mem ⋙ aX.J ≅ aY.J ⋙ derivedPull g coefficient
  completion_unit : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
    (ambient.hom.app K.obj) ≫
        (pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)).map
          ((pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K.obj) ≫
        (aX.integral.inv.app ((integralPull l E g integral_mem).obj K)) =
      (derivedPull g coefficient).map (aY.integral.inv.app K) ≫
        (comparison.inv.app
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K))
  special : Etale g ∨ IsImmersion g →
    IsIso coefficient ∧ PreservesFiniteLimits (modulePull g coefficient) ∧
      PreservesFiniteColimits (modulePull g coefficient)

attribute [instance] Along.ordinaryAdditive

/-- The published raw pullback with its preservation certificate.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
def Along.raw {X Y : Base.{u} l} {g : X.scheme ⟶ Y.scheme}
    {aX : At l E X} {aY : At l E Y} (a : Along l E g aX aY) :=
  rawPull l E g a.integral_mem

/-- Canonical ambient composition, fixed by the insertion of tensor units and the
universal derived counits. The last equation states compatibility of J with precisely
this ambient comparison, rather than a new choice of triangulated composition.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-continuous-rational-derived-realization). -/
structure Composition {X Y Z : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (h : Z.scheme ⟶ X.scheme) (aX : At l E X) (aY : At l E Y) (aZ : At l E Z)
    (ag : Along l E g aX aY) (ah : Along l E h aZ aX)
    (ahg : Along l E (h ≫ g) aZ aY) where
  coefficient : ahg.coefficient =
    (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l Y.scheme E) ≫
      (adicTowerInverseImage h).map ag.coefficient ≫ ah.coefficient
  ordinary : modulePull (h ≫ g) ahg.coefficient ≅
    modulePull g ag.coefficient ⋙ modulePull h ah.coefficient
  ordinary_units : ∀ (M : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E))
      (U : Y.scheme.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (h ≫ g)).obj U))
        (moduleUnit (h ≫ g) ahg.coefficient M U m) =
      (((modulePull h ah.coefficient).obj ((modulePull g ag.coefficient).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp h g).hom.app U).op)
          (moduleUnit h ah.coefficient ((modulePull g ag.coefficient).obj M)
            ((proEtaleBaseChange g).obj U) (moduleUnit g ag.coefficient M U m))
  complex : (modulePull (h ≫ g) ahg.coefficient).mapHomologicalComplex (.up ℤ) ≅
    (modulePull g ag.coefficient).mapHomologicalComplex (.up ℤ) ⋙
      (modulePull h ah.coefficient).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  ambient : derivedPull (h ≫ g) ahg.coefficient ≅
    derivedPull g ag.coefficient ⋙ derivedPull h ah.coefficient
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) (P.X n)) →
    ahg.counit.app P ≫ DerivedCategory.Q.map (complex.hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (derivedPull h ah.coefficient).map (ag.counit.app P) ≫
        ah.counit.app (((modulePull g ag.coefficient).mapHomologicalComplex (.up ℤ)).obj P)
  raw : ahg.raw l E ≅
    ag.raw l E ⋙ ah.raw l E
  compatibility : ∀ K,
    ahg.comparison.hom.app K ≫
        ambient.hom.app (aY.J.obj K) =
      aZ.J.map (raw.hom.app K) ≫
        ah.comparison.hom.app ((ag.raw l E).obj K) ≫
        (derivedPull h ah.coefficient).map (ag.comparison.hom.app K)

/-- Identity pullback comparison, normalized by the identity fibre product and tensor unit.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure Identity (X : Base.{u} l) (a : At l E X)
    (ai : Along l E (𝟙 X.scheme) a a) where
  site : proEtaleBaseChange (𝟙 X.scheme) ≅ 𝟭 X.scheme.ProEt
  site_normalization : ∀ U,
    (site.hom.app U).left = pullback.fst U.hom (𝟙 X.scheme)
  ordinary : modulePull (𝟙 X.scheme) ai.coefficient ≅ 𝟭 _
  ordinary_units : ∀ (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
      (U : X.scheme.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X.scheme)).obj U))
        (moduleUnit (𝟙 X.scheme) ai.coefficient M U m) =
      M.val.map (site.hom.app U).op m
  ambient : derivedPull (𝟙 X.scheme) ai.coefficient ≅ 𝟭 _
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X.scheme)
      (R := rationalCoefficientSheaf l X.scheme E) P →
    ai.counit.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P)
  raw : ai.raw l E ≅ 𝟭 _
  compatibility : ∀ K,
    ai.comparison.hom.app K ≫ ambient.hom.app (a.J.obj K) = a.J.map (raw.hom.app K)

variable (F G : Type u) [Field F] [Field G] [Algebra ℚ_[l] F] [Algebra ℚ_[l] G]
  [FiniteDimensional ℚ_[l] F] [FiniteDimensional ℚ_[l] G]

/-- Finite coefficient extension, with its sectionwise field map, finite-integral square,
and comparison normalized by the existing derived balancing maps on integral models.
Source: BS 6.8.14 and 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure FieldChange (i : E →ₐ[ℚ_[l]] F) (X : Base.{u} l)
    (aE : At l E X) (aF : At l F X) where
  coefficient : rationalCoefficientSheaf l X.scheme E ⟶ rationalCoefficientSheaf l X.scheme F
  normalized : ∀ (U : X.scheme.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l F X.scheme U (coefficient.hom.app U s) x =
      i (rationalCoefficientValue l E X.scheme U s x)
  square : pbcScalarCoefficientMap l E F i X.scheme ≫ aF.integralIso.hom ≫ aF.inclusion =
    aE.integralIso.hom ≫ aE.inclusion ≫ coefficient
  comparison : pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit ⋙ aF.J ≅
    aE.J ⋙ pbcDerivedExtend coefficient
  integral_normalization : ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E),
    comparison.hom.app
        ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
        (pbcDerivedExtend coefficient).map (aE.integral.hom.app K) ≫
        (pbcReductionNormalization (aE.integralIso.hom ≫ aE.inclusion) coefficient
          (aE.integralIso.hom ≫ aE.inclusion ≫ coefficient) rfl K.obj).hom =
      aF.integral.hom.app
          ((pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj K) ≫
        (pbcReductionNormalization (pbcScalarCoefficientMap l E F i X.scheme)
          (aF.integralIso.hom ≫ aF.inclusion)
          (aE.integralIso.hom ≫ aE.inclusion ≫ coefficient) square K.obj).hom

/-- The coefficient associator is the prescribed raw associator and the ambient balanced
tensor associator. This includes repeated fields and identity field embeddings.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure FieldComposition (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G) (X : Base.{u} l)
    (aE : At l E X) (aF : At l F X) (aG : At l G X)
    (bEF : FieldChange l E F i X aE aF) (bFG : FieldChange l F G j X aF aG)
    (bEG : FieldChange l E G (j.comp i) X aE aG) where
  coefficient : bEF.coefficient ≫ bFG.coefficient = bEG.coefficient
  compatibility : ∀ K,
    aG.J.map (pbcRationalScalarCompComponent l E F G i j X.scheme
        X.dimension X.prime_unit K).hom ≫ bEG.comparison.hom.app K =
      bFG.comparison.hom.app
          ((pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit).obj K) ≫
        (pbcDerivedExtend bFG.coefficient).map (bEF.comparison.hom.app K) ≫
        (pbcReductionNormalization bEF.coefficient bFG.coefficient bEG.coefficient
          coefficient (aE.J.obj K)).hom

/-- The mixed coefficient/pullback square, using the actual raw scalar/completed-pull
comparison and the ordinary balanced tensor map. Source: BS 6.8.14--6.8.15
(blueprint: lem-per-continuous-rational-derived-realization). -/
structure Mixed (i : E →ₐ[ℚ_[l]] F) {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aXE : At l E X) (aYE : At l E Y) (aXF : At l F X) (aYF : At l F Y)
    (agE : Along l E g aXE aYE) (agF : Along l F g aXF aYF)
    (bX : FieldChange l E F i X aXE aXF) (bY : FieldChange l E F i Y aYE aYF) where
  coefficient : (adicTowerInverseImage g).map bY.coefficient ≫ agF.coefficient =
    agE.coefficient ≫ bX.coefficient
  ordinary : pbcExtend bY.coefficient ⋙ modulePull g agF.coefficient ≅
    modulePull g agE.coefficient ⋙ pbcExtend bX.coefficient
  ordinary_sections : ∀ (M : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E))
      (U : Y.scheme.ProEt)
      (a : (rationalCoefficientSheaf l Y.scheme F).obj.obj (op U)) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj U))
      (moduleUnit g agF.coefficient ((pbcExtend bY.coefficient).obj M) U
        (pbcTensorSection bY.coefficient M (op U) a m)) =
      pbcTensorSection bX.coefficient ((modulePull g agE.coefficient).obj M)
        (op ((proEtaleBaseChange g).obj U))
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
          agF.coefficient).hom.app (op U) a)
        (moduleUnit g agE.coefficient M U m)
  complex : (pbcExtend bY.coefficient).mapHomologicalComplex (.up ℤ) ⋙
      (modulePull g agF.coefficient).mapHomologicalComplex (.up ℤ) ≅
    (modulePull g agE.coefficient).mapHomologicalComplex (.up ℤ) ⋙
      (pbcExtend bX.coefficient).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  ambient : pbcDerivedExtend bY.coefficient ⋙ derivedPull g agF.coefficient ≅
    derivedPull g agE.coefficient ⋙ pbcDerivedExtend bX.coefficient
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) (P.X n)) →
    (derivedPull g agF.coefficient).map (pbcComplexCounit bY.coefficient P) ≫
        agF.counit.app (((pbcExtend bY.coefficient).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (complex.hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend bX.coefficient).map (agE.counit.app P) ≫
        pbcComplexCounit bX.coefficient
          (((modulePull g agE.coefficient).mapHomologicalComplex (.up ℤ)).obj P)
  raw : pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit ⋙
      agF.raw l F ≅ agE.raw l E ⋙
        pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit
  raw_normalization : ∀ K,
    HEq (raw.hom.app K)
      ((pbcRationalization X.scheme (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        (ObjectProperty.homMk
          (X := (integralPull l F g agF.integral_mem).obj
            ((pbcEmbeddingIntegralTensor l E F i Y.scheme Y.dimension Y.prime_unit).obj K.obj))
          (Y := (pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj
            ((integralPull l E g agE.integral_mem).obj K.obj))
          ((pbcScalarCompletedPullIso l E F i g).hom.app K.obj.obj)))
  compatibility : ∀ K,
    aXF.J.map (raw.hom.app K) ≫
        bX.comparison.hom.app ((agE.raw l E).obj K) ≫
        (pbcDerivedExtend bX.coefficient).map (agE.comparison.hom.app K) =
      agF.comparison.hom.app
          ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj K) ≫
        (derivedPull g agF.coefficient).map (bY.comparison.hom.app K) ≫
        ambient.hom.app (aYE.J.obj K)

/-- The site inclusion attached to a weakly étale object, with no finiteness hypothesis
on its source. Source: BS 6.8.14; Stacks 03EL
(blueprint: lem-per-continuous-rational-derived-realization). -/
def siteInclude {X : Scheme.{u}} (U : X.ProEt) : U.left.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ U.prop

/-- Projection from the base-changed object, viewed in the original small site.
Source: BS 6.8.15; Stacks 03EL
(blueprint: lem-per-continuous-rational-derived-realization). -/
def siteCounit {X : Scheme.{u}} (U : X.ProEt) (V : X.ProEt) :
    (siteInclude U).obj ((proEtaleBaseChange U.hom).obj V) ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom U.hom) pullback.condition

/-- Restriction to an arbitrary object of the site. The slice equivalence and ring map
are fixed by the actual inclusion and evaluation of continuous functions. The last
comparison identifies ordinary module inverse image with literal site restriction.
Source: BS 6.8.14 and 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure SiteRestriction (X : Scheme.{u}) (U : X.ProEt) where
  slice : U.left.ProEt ≌ Over U
  slice_normalization : slice.functor ⋙ Over.forget U = siteInclude U
  [continuous : slice.functor.IsContinuous (ProEt.topology U.left) ((ProEt.topology X).over U)]
  ring : ((adicLisseForget U.left).obj (rationalCoefficientSheaf l U.left E)) ≅
    (slice.functor.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U.left) ((ProEt.topology X).over U)).obj
        (((adicLisseForget X).obj (rationalCoefficientSheaf l X E)).over U)
  ring_normalization : ∀ (V : U.left.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l U.left E).obj.obj V),
    HEq (ring.hom.hom.app V s) s
  coefficient : (adicTowerInverseImage U.hom).obj (rationalCoefficientSheaf l X E) ⟶
    rationalCoefficientSheaf l U.left E
  normalized : rationalCoefficientRestrictionNormalized l E U.hom coefficient
  coefficient_iso : IsIso coefficient
  comparison : modulePull U.hom coefficient ≅
    SheafOfModules.overFunctor
      ((adicLisseForget X).obj (rationalCoefficientSheaf l X E)) U ⋙
        SheafOfModules.pushforward (F := slice.functor) (J := ProEt.topology U.left)
          (K := (ProEt.topology X).over U) ring.hom
  comparison_units : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E))
      (V : X.ProEt) (m : M.val.obj (op V)),
    HEq ((comparison.hom.app M).val.app (op ((proEtaleBaseChange U.hom).obj V))
      (moduleUnit U.hom coefficient M V m)) (M.val.map (siteCounit U V).op m)
  [ordinaryAdditive : (modulePull U.hom coefficient).Additive]
  [exact_limits : PreservesFiniteLimits (modulePull U.hom coefficient)]
  [exact_colimits : PreservesFiniteColimits (modulePull U.hom coefficient)]
  counit : DerivedCategory.Q ⋙ derivedPull U.hom coefficient ⟶
    (modulePull U.hom coefficient).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  normalized_counit : IsNormalizedPullCounit U.hom coefficient counit
  universal : (derivedPull U.hom coefficient).IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso _ (.up ℤ))
  derived : derivedPull U.hom coefficient ≅ (modulePull U.hom coefficient).mapDerivedCategory
  derived_normalization : ∀ P,
    derived.hom.app (DerivedCategory.Q.obj P) ≫
        (modulePull U.hom coefficient).mapDerivedCategoryFactors.hom.app P = counit.app P

/-- A compatible family of realizations. All fields, embeddings, schemes and morphisms
are quantified, so the identity, composition and mixed comparison clauses refer to
one family rather than unrelated existence witnesses.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure Family (l : ℕ) [Fact l.Prime] where
  realization : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : Base.{u} l), At l A X
  along : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme), Along l A g (realization A X) (realization A Y)
  composition : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y Z : Base.{u} l} (g : X.scheme ⟶ Y.scheme) (h : Z.scheme ⟶ X.scheme),
    Composition l A g h (realization A X) (realization A Y) (realization A Z)
      (along A g) (along A h) (along A (h ≫ g))
  identity : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : Base.{u} l), Identity l A X (realization A X) (along A (𝟙 X.scheme))
  fieldChange : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : Base.{u} l), FieldChange l A B i X (realization A X) (realization B X)
  fieldComposition : ∀ (A B C : Type u) [Field A] [Field B] [Field C]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    [FiniteDimensional ℚ_[l] C]
    (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C) (X : Base.{u} l),
    FieldComposition l A B C i j X (realization A X) (realization B X) (realization C X)
      (fieldChange A B i X) (fieldChange B C j X) (fieldChange A C (j.comp i) X)
  mixed : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme),
    Mixed l A B i g (realization A X) (realization A Y) (realization B X) (realization B Y)
      (along A g) (along B g) (fieldChange A B i X) (fieldChange A B i Y)
  siteRestriction : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X : Base.{u} l) (U : X.scheme.ProEt),
    SiteRestriction l A X.scheme U

/-- Continuous rational derived realization, simultaneously with its normalized
pullback, coefficient-extension and site-restriction compatibilities.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Lemma 6.8.2(1), Proposition 6.8.11(3),
Definition 6.8.8, Remark 6.8.15
(blueprint: lem-per-continuous-rational-derived-realization).

Proof plan (the node’s complete steps):

1. Write $\mathcal C_X=D^b_c(X,A)$ for the completed-coefficient category, including its
compatible etale-origin witnesses. The coefficient datum defines
$B_X=\varprojlim_n(A/\varpi^n)_X$ as a ring sheaf with its specified projections. The
continuous-coefficient restriction lemma identifies this ring with $V\mapsto C(|V|,A)$, and
identifies its sheafified localization at $\varpi$ with $V\mapsto C(|V|,E)$. The identifications
preserve constant sections and quotient projections and commute with locally closed restriction.
All categories below are categories of module sheaves over these actual ring sheaves.
Uses: def-weil-pbc-bounded-constructible-complete, def-weil-pbc-adic-coefficient-datum,
lem-weil-pbc-continuous-coefficients-immersion-restriction.

2. The integral stratified-perfect characterization applies to $X$: it assumes exactly a finite
coefficient field, a noetherian finite-dimensional scheme, and invertibility of $\ell$. It says
that $K\in\mathcal C_X$ if and only if $K$ is bounded and its cohomology, on a finite
stratification, is locally $B_S\otimes_A N$ for finitely presented $A$-modules $N$. Equivalently
its local models are $B_S\otimes_A^L P$ with $P$ perfect. In particular it puts such integral
sheaves in degree zero in $\mathcal C_X$, and supplies closure under shifts, cones, truncations
and cohomology. This step concerns the integral category only; it does not yet identify its
rationalization with the target category.
Uses: lem-weil-pbc-integral-stratified-perfect-characterization.

3. Scalar localization of module sheaves is exact by the localization/inverse-image coherence
lemma, applied to the identity geometric morphism with $R=B_X,t=\varpi$. Its termwise derived
functor is $F_X(K)=E_X\otimes^L_{B_X}K$, as also given by derived change of rings. Exactness
implies $\mathcal H^r(F_XK)=E_X\otimes_{B_X}\mathcal H^r(K)$: an exact functor preserves the
kernels, images and quotients defining cohomology. On a stratum $h:S\to X$ the
continuous-coefficient restriction lemma gives $h^{-1}B_X\cong B_S$ and $h^{-1}E_X\cong E_S$,
and the coherence lemma (for $h$) commutes $h^{-1}$ with localization; so on an integral local
model this sheaf is $E_S\otimes_A N$. A finitely presented module over the DVR $A$ has a finite
presentation; after tensoring the presentation with the field $E$, its cokernel is a
finite-dimensional vector space, so the last sheaf is locally finite free. Thus $F_XK$ lies in
$D_{\mathrm{cons}}(X,E_X)$. Since $\varpi$ acts invertibly after $F_X$, the fraction relation
defines $J_X(f/\varpi^n)=\varpi^{-n}F_X(f)$, respecting addition, identities and composition.
Raw scalar localization is triangulated with distinguished triangles isomorphic to integral
image triangles; hence the triangulated functor $F_X$ induces a triangulated $E$-linear functor
$J_X$ into the ambient $D(\operatorname{Mod}(E_X))$.
Uses: lem-weil-pbc-localization-inverse-image-coherence,
lem-weil-pbc-continuous-coefficients-immersion-restriction, lem-pur-derived-change-of-rings,
def-weil-derived-cohomology-sheaves, def-weil-pbc-rational-category,
lem-weil-linear-scalar-localization-triangulated.

4. For $K,L\in\mathcal C_X$, verify the Hom-continuity hypothesis of the scalar-localization Hom
lemma. Integral bounded-below compactness gives the global-derived-Hom coproduct comparison for
every countable family with a common lower bound, including its shift by any integer $q$. Take
$H^0$ and use the global-sections/internal-Hom comparison to identify
$H^0R\operatorname{Hom}(K,M)$ with $\operatorname{Hom}_{D(B_X)}(K,M)$. Countable sums of
$A$-modules are exact, since finite-support coordinates preserve kernels and surjections; their
termwise sums represent derived sums by the countable-sums lemma. Thus $H^0$ of their sum is the
sum of their $H^0$'s. These observations give precisely the Hom/coproduct hypothesis, and
boundedness makes $L$ bounded below. The scalar-localization Hom lemma, with $R=B_X,t=\varpi$,
now gives
$$\operatorname{Hom}_{D(B_X)}(K,L[q])[1/\varpi]\cong\operatorname{Hom}_{D(E_X)}(F_XK,F_XL[q]),\quad
f/\varpi^n\longmapsto\varpi^{-n}F_X(f).$$ At $q=0$ the left side is the raw category's Hom
group. The lemma's identity and composition clauses prove full faithfulness of $J_X$. The target
here is $D(E_X)$, not $D(B_X)$.
Uses: lem-weil-pbc-integral-constructible-bounded-below-compactness,
lem-pur-rhom-global-sections, lem-kun-derived-countable-sums-exact,
lem-weil-pbc-scalar-localization-derived-hom, def-weil-pbc-rational-category.

5. Apply the directed-triangulated-image lemma with the singleton preorder, source the raw
rationalized category, identity transition, and functor $J_X$ to the ambient $D(E_X)$. Step 3
gives a triangulated functor and Step 4 gives every arrow between its image objects an actual
lift; these are the lemma's hypotheses at the unique common stage. Its conclusion makes the
essential image closed under zero, shifts and distinguished triangles. If $L$ is a lisse
$E_X$-sheaf, the lisse-lattice lemma produces a constructible $B_X$-module $N$ with
$E_X\otimes_{B_X}N\cong L$. Step 2 puts $N[0]$ in $\mathcal C_X$, with completeness and
compatible etale origins. Hence all lisse sheaves in degree zero belong to the essential image.
Uses: lem-weil-pbc-directed-triangulated-image,
lem-weil-pbc-lisse-e-constructible-integral-lattice,
lem-weil-pbc-integral-stratified-perfect-characterization.

6. Let $F$ be a constructible $E_X$-module sheaf. To use the finite-model stratum-filtration
tool, take the condensed ring $C(-,E)$. The continuous-coefficient realization identifies its
pulled ring on every scheme with the continuous ring sheaf, naturally for coefficient maps. The
internal/sectionwise module equivalence preserves underlying sheaves and actions. Thus a finite
free model $E_S^r$ is exactly the tool's finite constant local model $E_S\otimes_E E^r$. This
identification is used only for the sheaf filtration, never to infer membership in the completed
integral category. Choose the finite noetherian affine cover of $X$. The affine-noetherian-space
lemma makes each member noetherian. A descending closed chain stabilizes on each of these
finitely many members, hence stabilizes globally. Thus $|X|$ is noetherian, and the filtration
lemma applies and gives a finite filtration of $F$ with quotients $v_{k!}(t_k)_*L_k$, where
$v_k:V_k\hookrightarrow X$ is qcqs open and $t_k:S_k\hookrightarrow V_k$ is reduced closed. Each
local model of $L_k$ is a finitely presented $E$-module, hence a finite-dimensional vector
space; therefore $L_k$ is lisse.
Uses: lem-sfb-finite-model-stratum-filtration, lem-weil-pbc-continuous-coefficient-realizations,
def-weil-pbc-internal-abelian-sheaf-module-equivalence,
lem-sc-affine-noetherian-underlying-space.

7. Each $S_k$ is noetherian, finite-dimensional and $\ell$-coprime: it is closed in the
noetherian open $V_k$, affine rings are quotients of noetherian rings, irreducible closed chains
have the dimension bound from $X$, and the inverse of $\ell$ survives in the quotient local
rings. Choose a constructible integral lattice $N_k$ for $L_k$ by the lisse-lattice lemma. The
ringed open-closed lemma supplies exact $v_{k!}$ and $(t_k)_*$, and their restrictions are $N_k$
on the supporting pieces and zero on the complements. Extending the finite stratification of
$N_k$ by those zero pieces proves $M_k=v_{k!}(t_k)_*N_k$ is an integral constructible sheaf;
Step 2 certifies $M_k[0]\in\mathcal C_X$, including the etale witnesses. Locally closed
coefficient restrictions are the maps of Step 1. Localization is the sequential sheaf colimit of
multiplication by $\varpi$, with fractions as transition classes. It commutes with $v_{k!}$
since that functor is a left adjoint, and with $(t_k)_*$ by the filtered-colimit clause of the
open-closed lemma on the qcqs $V_k$. Module colimits are the underlying abelian sheaf colimits.
Therefore $J_X(QM_k)\cong v_{k!}(t_k)_*L_k$.
Uses: lem-weil-pbc-noetherian-open-subscheme-noetherian,
lem-weil-pbc-lisse-e-constructible-integral-lattice, lem-weil-pbc-proetale-ringed-open-closed,
lem-weil-pbc-integral-stratified-perfect-characterization,
lem-weil-pbc-continuous-coefficients-immersion-restriction,
lem-weil-pbc-module-sheaves-colimits-forgetful, lem-weil-pbc-left-adjoint-preserves-colimits.

8. Induct over the finite filtration of Step 6, beginning with its zero term. Its short exact
sequence $0\to F_{k-1}\to F_k\to v_{k!}(t_k)_*L_k\to0$ is a distinguished triangle in $D(E_X)$
by the short-exact-sequence clause of the heart-triangle lemma for the ambient standard
t-structure. Step 7 and the induction hypothesis put its outer terms in the essential image. The
connecting morphism lifts by full faithfulness, and the cone closure in Step 5 puts $F_k$ in the
image. This proves that every constructible $E_X$-sheaf in degree zero has an integral derived
model; it does not assert a globally lisse integral lattice.
Uses: lem-weil-heart-short-exact-triangles, def-sbc-standard-tstructure-derived-category.

9. For $C\in D_{\mathrm{cons}}(X,E_X)$ choose a finite cohomological interval $[a,b]$ and induct
on its length. An object with zero cohomology is zero in the derived category. Otherwise its
standard truncation triangle has terms $\tau^{\leq b-1}C,C,\mathcal H^b(C)[-b]$. The first has a
shorter interval and the third lies in the image by Step 8 and shift closure. Step 5 gives
extension closure, or equivalently lifts the connecting arrow and takes its cone. Thus $C$ is in
the image. Together with Steps 3 and 4 this proves the asserted $E$-linear triangulated
equivalence. In particular the full target subcategory inherits the ambient distinguished
triangles; no idempotent envelope is introduced.
Uses: def-sbc-standard-tstructure-derived-category, lem-weil-heart-short-exact-triangles,
def-weil-abstract-derived-category.

10. The integral t-structure proposition identifies integral truncations and cohomology with the
ambient ones and keeps them in $\mathcal C_X$. The localized t-structure proposition gives
$\tau_E^{\leq m}QK\cong Q\tau_A^{\leq m}K$ and the analogous upper formula. Exact scalar
localization gives the cohomology formula of Step 3, so $J_X$ sends the two localized
degree-bound classes into the corresponding ambient degree-bound classes. In particular it is
t-exact in this direction, and $J_X(\mathcal H^r(QK))$ is $E_X\otimes_{B_X}\mathcal H^r(K)$
placed in degree zero.
Uses: prop-weil-pbc-integral-tstructure, prop-weil-localized-tstructure,
lem-weil-pbc-localization-inverse-image-coherence, def-weil-derived-cohomology-sheaves.

11. Conversely, if $J_X(QK)$ has no cohomology above $m$, then Step 3 and the integral
truncation formula show $J_X(Q\tau_A^{\geq m+1}K)$ has zero cohomology in every degree. It is
zero in the derived category, so full faithfulness implies $Q\tau_A^{\geq m+1}K=0$ (its identity
is zero). The localized truncation triangle then gives $Q\tau_A^{\leq m}K\cong QK$, putting $QK$
in the localized nonpositive class at $m$. The same argument with $\tau_A^{\leq m-1}K$ proves
the converse nonnegative bound. Hence both t-structures agree under $J_X$. Uniqueness of
truncation triangles, with their canonical units and counits, makes the truncation comparisons
natural. Intersecting the two degree bounds identifies the heart with all constructible
$E_X$-sheaves in degree zero, using Step 8 for their essential surjectivity.
Uses: prop-weil-pbc-integral-tstructure, prop-weil-localized-tstructure,
lem-weil-heart-short-exact-triangles, def-weil-abstract-derived-category.

12. Fix $g:X'\to X$ as in the statement. Use the actual structural map $c_g:g^{-1}B_X\to B_{X'}$
defined by its finite quotient components, not an assumed isomorphism. Pull back a supporting
stratification of $K\in\mathcal C_X$; its base changes form a stratification of $X'$. The
trivializing pro-etale covers pull back to covers by weakly etale base change and fpqc covering
stability. On each pulled-back cover, ordinary derived module pullback sends $B_S\otimes_A^L P$
to $B_{S'}\otimes_A^L P$: on the finite projective terms the balancing map is
$b'\otimes(b\otimes p)\mapsto b'c_g(b)\otimes p$, with inverse $b'\otimes p\mapsto
b'\otimes(1\otimes p)$. These maps commute with differentials. Derived pullback is computed on
K-flat flat-term resolutions; its tensor and composition comparisons identify this local
computation with the restriction of $Lg^*_{B}K$. Every new stratum is locally closed in the
noetherian finite-dimensional $X'$, so has the same scheme hypotheses. The stratified-perfect
characterization therefore gives $Lg^*_{B}K\in\mathcal C_{X'}$, including derived completeness
and compatible etale-origin witnesses.
Uses: def-weil-pbc-completed-pullback, lemma-constructible-pullback-stratification,
lem-weil-pbc-weakly-etale-composition-base-change, lem-galois-fpqc-covering-base-change,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-ringed-derived-monoidal-comparisons,
lem-weil-pbc-integral-stratified-perfect-characterization.

13. The specified comparison $\gamma_{g,K}:Lg^*_{B}K\to Lg^*_{\mathrm{comp}}K$ is the
quotient-tower completion unit by the completed-pullback definition and the constant/completed
comparison. Step 12 makes its source complete. Intrinsic completeness says its Koszul completion
unit is invertible, and the constant-completion equivalence identifies that unit with this
quotient-tower unit, including transitions. Thus $\gamma_{g,K}$ is invertible, naturally in $K$.
Apply localization/inverse-image coherence to $R=B_X,t=\varpi$. It identifies $g^{-1}E_X$ with
$(g^{-1}B_X)[1/\varpi]$, preserving the localization unit. The map $c_g$ sends $\varpi$ to
$\varpi$, so it extends to the structural map into $E_{X'}$. The ringed-topos derived pullback
composition comparison now gives $$J_{X'}(Q Lg^*_{B}K)\cong
E_{X'}\otimes^L_{g^{-1}E_X}g^{-1}(E_X\otimes^L_{B_X}K).$$ Both sides flatten to
$E_{X'}\otimes^L_{g^{-1}B_X}g^{-1}K$ by balancing. Composing this comparison with
$J_{X'}(Q\gamma_{g,K}^{-1})$ proves the displayed completed-pullback comparison. Its naturality
and the fraction rule let it descend to raw rationalizations.
Uses: def-weil-pbc-completed-pullback, def-weil-pbc-intrinsic-completion,
lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-localization-inverse-image-coherence,
lem-sfb-ringed-derived-monoidal-comparisons, def-weil-pbc-rational-category.

14. For composable scheme maps $X''\xrightarrow h X'\xrightarrow g X$, the structural maps
satisfy $c_{gh}=c_h\,h^{-1}c_g$ after the inverse-image composition comparison: composing with
each finite quotient projection gives the same finite constant-coefficient map, and the limit
universal property gives equality. The ambient derived pullback composition and identity
comparisons are those of the ringed-derived monoidal-comparison lemma.
Localization/inverse-image coherence identifies the comparison for $gh$ with the composite
comparisons for $g,h$, as an equation of natural transformations. On K-flat complexes the tensor
maps send a balanced representative $e''\otimes e'\otimes k$ to $e''h^{-1}(e')\otimes k$ in
either order; the identity sends $1\otimes k$ to $k$. These maps give the comparisons in Step
13. Under the natural completion units $\gamma$, completed pullback on this category is ordinary
pullback; conjugating by those isomorphisms gives exactly the same equations. The
finite-reduction and completion-unit comparisons used here preserve the quotient maps, so the
conjugation uses the specified units, not arbitrary identifications. This proves naturality,
identity and composition with the ambient composition comparisons stated in the item.
Uses: def-weil-pbc-completed-pullback, lem-weil-pbc-localization-inverse-image-coherence,
lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-constant-completion-equivalence.

15. For a finite extension $E\subset L$, put $A_L=\mathcal O_L$ and
$B_{L,X}=\varprojlim_n(A_L/\varpi_L^n)_X$. The raw scalar-extension proposition defines
$T_{L/E}$ by the actual integral change $C_{L/E,X}K=B_{L,X}\otimes^L_{B_{E,X}}K$ followed by
rationalization, and puts this object in the integral category under our scheme hypotheses.
Continuous-coefficient realization is natural for $A_E\to A_L$ and $E\to L$, so these are the
stated continuous ring maps. Apply the ambient derived pullback composition comparison to the
same-site coefficient maps. It gives
$$J_{L,X}(T_{L/E}QK)=L_X\otimes^L_{B_{L,X}}(B_{L,X}\otimes^L_{B_{E,X}}K)\cong
L_X\otimes^L_{B_{E,X}}K\cong L_X\otimes^L_{E_X}J_{E,X}(QK).$$ The maps flatten $(l\otimes
b)\otimes k$ to $lb\otimes k$, with inverses inserting $1$. They are canonical on K-flat
representatives, and the comparison lemma descends them to derived categories. The image of
every nonzero scalar of $E$ is invertible in $L$, so the equations also hold for the raw
morphisms $f/\varpi_E^n$.
Uses: prop-weil-pbc-scalar-extension, lem-weil-pbc-continuous-coefficient-realizations,
lem-sfb-ringed-derived-monoidal-comparisons.

16. For $E\subset L\subset M$ both routes in the coefficient associator comparison flatten
$m\otimes l\otimes k$ to $ml\otimes k$. For four fields the pentagon flattens all factors to
their ordered product; the unit inserts and removes $1$. The ringed-derived comparison lemma
makes these equations valid on derived complexes; the raw scalar-extension proposition
identifies these associators with its specified ones. To combine with $g:X'\to X$, the square of
the integral structural maps $c_g$ and coefficient change commutes, since on each quotient the
two composites are postcomposition of the same coefficient map and inverse image of the same
section. The continuous realization's coefficient naturality gives the localized square as well.
The last clause of the ringed-derived comparison lemma for isomorphic underlying geometric
composites identifies the two derived tensor routes. Its balanced map sends $l'\otimes b'\otimes
k$ to $l'b'\otimes g^{-1}k$ in either order. The completion-unit comparisons of Step 13 and the
scalar-extension/pullback comparison in the raw scalar-extension proposition preserve this
equation. Thus the realization comparison commutes with finite coefficient extension, successive
extensions, and their pullback and composition associators. No pair-category descent is used.
Uses: lem-sfb-ringed-derived-monoidal-comparisons, prop-weil-pbc-scalar-extension,
lem-weil-pbc-continuous-coefficient-realizations, lem-weil-pbc-constant-completion-equivalence.

17. For a locally closed immersion the coefficient isomorphism is precisely the
continuous-coefficient immersion restriction lemma. For an etale map $g:X'\to X$, use the weakly
etale localization equivalence $X'_{\mathrm{proet}}\simeq X_{\mathrm{proet}}/X'$. The inverse
image $g^{-1}$ of the pro-etale inverse-image definition is this slice restriction: for $U\to
X'$ in $X'_{\mathrm{proet}}$ with structure map $s$, the pair $(U\to X,(s,\mathrm{id}_U))$ is
initial in the indexing category $\mathcal I_U$, since any $(V,\phi)$ has $\phi=(s,a)$ with
$a=\mathrm{pr}_2\phi$ the unique $X$-morphism satisfying $u_g(a)(s,\mathrm{id})=\phi$; hence
$(u_{g,p}F)(U)=F(U\to X)$, already a sheaf on the slice, and no sheafification changes it.
Restriction to this slice evaluates a coefficient sheaf on the same underlying scheme $V$, so
sends $C(|V|,A)$ and $C(|V|,E)$ identically to the corresponding coefficient sheaves on $X'$. In
the finite-quotient description it restricts each constant quotient to the same quotient and
preserves the sectionwise limit, so the resulting coefficient map is exactly $c_g$, with the
constant-section normalizations. The same evaluation argument works for any site object $U\to
X$, without requiring $U$ itself to be noetherian. Inverse image with an identified coefficient
ring is exact by localization/inverse-image coherence; its termwise derived functor is ordinary
inverse image. Hence for the etale and locally closed morphisms the displayed module pullback is
exact inverse image, and on an arbitrary site object it restricts to exact site restriction. All
identifications preserve coefficient maps by their section formulas and Step 1.
Uses: lem-weil-pbc-continuous-coefficients-immersion-restriction,
lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-localization-inverse-image-coherence,
def-weil-pbc-completed-pullback, def-weil-proetale-inverse-image. -/
theorem continuous_rational_derived_realization (l : ℕ) [Fact l.Prime] :
    Nonempty (Family.{u} l) := by
  sorry

end AlgebraicGeometry.Scheme.ContinuousRational
