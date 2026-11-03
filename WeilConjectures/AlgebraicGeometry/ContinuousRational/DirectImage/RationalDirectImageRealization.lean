/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalDerivedRealization
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
public import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardComparison
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage

/-! # Continuous rational realization and derived direct image

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15;
the localization, adjunction and coefficient normalizations are the comparison obligation
(blueprint: lem-a1-rational-direct-image-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational.DirectImage

/-- Separated finite-type schemes over the specified field, with the redundant consequences
packaged in the realization dependency's base type. Source: BS 6.7.2 and 6.8.15
(blueprint: lem-a1-rational-direct-image-realization). -/
structure Space (k : Type u) [Field k] (l : ℕ) extends Base.{u} l where
  [«over» : scheme.Over (Spec (.of k))]
  [finiteType : LocallyOfFiniteType (scheme ↘ Spec (.of k))]
  [quasiCompact : QuasiCompact (scheme ↘ Spec (.of k))]
  [separated : IsSeparated (scheme ↘ Spec (.of k))]

attribute [instance] Space.«over» Space.finiteType Space.quasiCompact Space.separated

/-- Ordinary direct image uses the adjunct of the given continuous coefficient map.
Source: BS 6.8.15 (blueprint: lem-a1-rational-direct-image-realization). -/
def modulePush {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage f).obj R ⟶ S) : pbcModules X S ⥤ pbcModules Y R :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    ((adicLisseForget Y).map ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R S c))

/-- Sectionwise direct image preserves addition. Source: BS 6.8.15
(blueprint: lem-a1-rational-direct-image-realization).
Proof: pushforward precomposes the underlying section maps and restricts their scalar
actions. Addition is sectionwise, so the two additive maps have identical components. -/
@[instance] theorem modulePush_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage f).obj R ⟶ S) : (modulePush f c).Additive := by
  exact ⟨fun {_ _} {_ _} ↦ rfl⟩

/-- The ordinary unbounded right derived direct image, computed on K-injectives in all
continuous modules. Source: BS 6.8.15
(blueprint: lem-a1-rational-direct-image-realization). -/
abbrev derivedPush {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage f).obj R ⟶ S) :=
  (modulePush f c).rightDerivedFunctor

/-- The canonical right-derived unit on cochain representatives. Source: BS 6.8.15;
Stacks 07A5 (blueprint: lem-a1-rational-direct-image-realization). -/
def pushUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage f).obj R ⟶ S)
    (I : CochainComplex (pbcModules X S) ℤ) :
    DerivedCategory.Q.obj (((modulePush f c).mapHomologicalComplex (.up ℤ)).obj I) ⟶
      (derivedPush f c).obj (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (modulePush f c).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) ≫
      (derivedPush f c).map ((DerivedCategory.quotientCompQhIso _).hom.app I)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual continuous module adjunction and its derived adjunction. The section equation
fixes the tensor unit; the transpose equation fixes the derived adjunction using the published
pullback counit and the actual right-derived unit. Source: BS 6.8.15; Stacks 07A6
(blueprint: lem-a1-rational-direct-image-realization). -/
structure Ordinary {X Y : Base.{u} l} (f : X.scheme ⟶ Y.scheme)
    (aX : At l E X) (aY : At l E Y) (a : Along l E f aX aY) where
  moduleAdjunction : modulePull f a.coefficient ⊣ modulePush f a.coefficient
  unit_sections : ∀ (M : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E))
      (U : Y.scheme.ProEt) (m : M.val.obj (op U)),
    (moduleAdjunction.unit.app M).val.app (op U) m = moduleUnit f a.coefficient M U m
  adjunction : derivedPull f a.coefficient ⊣ derivedPush f a.coefficient
  transpose : ∀ (P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ)
      (I : CochainComplex (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) ℤ)
      (t : ((modulePull f a.coefficient).mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv _ _ (a.counit.app P ≫ DerivedCategory.Q.map t) =
      DerivedCategory.Q.map
          ((moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I t) ≫
        pushUnit f a.coefficient I

/-- The localization projection is the mate of the specified balanced pullback comparison,
using the actual integral and continuous adjunctions. It is defined on every ambient object;
invertibility is asserted only on integral constructible objects. Source: BS 6.8.15
(blueprint: lem-a1-rational-direct-image-realization). -/
def projection {X Y : Base.{u} l} (f : X.scheme ⟶ Y.scheme)
    (aX : At l E X) (aY : At l E Y) (a : Along l E f aX aY)
    (o : Ordinary l E f aX aY a) (K : PbcCompletedDerived X.scheme (pbcIntegralDatum l E)) :
    (pbcDerivedExtend (aY.integralIso.hom ≫ aY.inclusion)).obj
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K) ⟶
      (derivedPush f a.coefficient).obj
        ((pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)).obj K) :=
  o.adjunction.homEquiv _ _
    (a.ambient.hom.app ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K) ≫
      (pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)).map
        ((pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).counit.app K))

/-- Restriction of the given ordinary completed-ring direct image, changing no objects or
maps. Source: BS 6.7.2 (blueprint: lem-a1-rational-direct-image-realization). -/
abbrev integralPush {X Y : Base.{u} l} (f : X.scheme ⟶ Y.scheme)
    (h : ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E)
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj)) :=
  pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualDerivedPush f (pbcIntegralDatum l E)) h

/-- Raw scalar localization of that restriction, using the published tensor map on Homs.
Source: BS 6.8.14(2) (blueprint: lem-a1-rational-direct-image-realization). -/
abbrev rawPush {X Y : Base.{u} l} (f : X.scheme ⟶ Y.scheme)
    (h : ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E)
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj)) :=
  pbcConditionalRational (pbcIntegralDatum l E)
    (pbcActualDerivedPush f (pbcIntegralDatum l E)) h (pbcUniformizer l E)

/-- The normalized direct-image comparison for one morphism. The integral Hom equation
specifies the completed adjunction, and localization retains its actual unit and counit.
The last two equations express their images under the two specified realization comparisons.
Source: BS 6.7.2, 6.8.14(2), 6.8.15
(blueprint: lem-a1-rational-direct-image-realization). -/
structure Comparison {X Y : Base.{u} l} (f : X.scheme ⟶ Y.scheme)
    (aX : At l E X) (aY : At l E Y) (a : Along l E f aX aY) where
  ordinary : Ordinary l E f aX aY a
  preserves : ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E)
      ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj)
  projection_iso : ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E),
    IsIso (projection l E f aX aY a ordinary K.obj)
  integralAdjunction : integralPull l E f a.integral_mem ⊣ integralPush l E f preserves
  integral_transpose : ∀ (M : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))
      (K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))
      (w : (integralPull l E f a.integral_mem).obj M ⟶ K),
    (integralAdjunction.homEquiv M K w).hom =
      (pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).homEquiv M.obj K.obj
        ((pbcActualCompletedPullUnit f (pbcIntegralDatum l E)).app M.obj ≫ w.hom)
  rawAdjunction : a.raw l E ⊣ rawPush l E f preserves
  localized_unit : ∀ M : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
    HEq (rawAdjunction.unit.app
        ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj M))
      ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (integralAdjunction.unit.app M))
  localized_counit : ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E),
    HEq (rawAdjunction.counit.app
        ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K))
      ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (integralAdjunction.counit.app K))
  comparison : rawPush l E f preserves ⋙ aY.J ≅ aX.J ⋙ derivedPush f a.coefficient
  integral_normalization : ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E),
    aY.integral.hom.app ((integralPush l E f preserves).obj K) ≫
        projection l E f aX aY a ordinary K.obj =
      comparison.hom.app
          ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
        (derivedPush f a.coefficient).map (aX.integral.hom.app K)
  unit : ∀ M,
    aY.J.map (rawAdjunction.unit.app M) ≫
        comparison.hom.app ((a.raw l E).obj M) =
      ordinary.adjunction.unit.app (aY.J.obj M) ≫
        (derivedPush f a.coefficient).map (a.comparison.inv.app M)
  counit : ∀ K,
    (derivedPull f a.coefficient).map (comparison.hom.app K) ≫
        ordinary.adjunction.counit.app (aX.J.obj K) =
      a.comparison.inv.app ((rawPush l E f preserves).obj K) ≫
        aX.J.map (rawAdjunction.counit.app K)

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]

/-- Compatibility with a finite coefficient extension. The raw comparison is normalized by
precisely the published integral coefficient mate. The ambient comparison is the mate of the
published mixed pullback comparison, so neither comparison is an arbitrary isomorphism.
Source: BS 6.8.15; scalar extension proposition
(blueprint: lem-a1-rational-direct-image-realization). -/
structure FieldChange (i : E →ₐ[ℚ_[l]] F) {X Y : Base.{u} l} (f : X.scheme ⟶ Y.scheme)
    (r : Family.{u} l)
    (dE : Comparison l E f (r.realization E X) (r.realization E Y) (r.along E f))
    (dF : Comparison l F f (r.realization F X) (r.realization F Y) (r.along F f)) where
  raw : rawPush l E f dE.preserves ⋙
      pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit ≅
    pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit ⋙
      rawPush l F f dF.preserves
  raw_normalization : ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E),
    HEq (raw.hom.app
        ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K))
      ((pbcRationalization Y.scheme (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        (ObjectProperty.homMk
          (X := (pbcEmbeddingIntegralTensor l E F i Y.scheme Y.dimension Y.prime_unit).obj
            ((integralPush l E f dE.preserves).obj K))
          (Y := (integralPush l F f dF.preserves).obj
            ((pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj K))
          ((pbcScalarDirectImageIso l E F i f).hom.app K.obj)))
  ambient : derivedPush f (r.along E f).coefficient ⋙
      pbcDerivedExtend (r.fieldChange E F i Y).coefficient ≅
    pbcDerivedExtend (r.fieldChange E F i X).coefficient ⋙
      derivedPush f (r.along F f).coefficient
  ambient_mate : ∀ N,
    ambient.hom.app N = dF.ordinary.adjunction.homEquiv _ _
      ((r.mixed E F i f).ambient.hom.app
          ((derivedPush f (r.along E f).coefficient).obj N) ≫
        (pbcDerivedExtend (r.fieldChange E F i X).coefficient).map
          (dE.ordinary.adjunction.counit.app N))
  compatibility : ∀ K,
    (r.fieldChange E F i Y).comparison.hom.app ((rawPush l E f dE.preserves).obj K) ≫
        (pbcDerivedExtend (r.fieldChange E F i Y).coefficient).map
          (dE.comparison.hom.app K) ≫ ambient.hom.app ((r.realization E X).J.obj K) =
      (r.realization F Y).J.map (raw.hom.app K) ≫
        dF.comparison.hom.app
          ((pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit).obj K) ≫
        (derivedPush f (r.along F f).coefficient).map
          ((r.fieldChange E F i X).comparison.hom.app K)

/-- Identity normalization uses the actual pullback identity comparisons and their right
adjunction transposes. Source: BS 6.8.15
(blueprint: lem-a1-rational-direct-image-realization). -/
structure Identity (X : Base.{u} l) (r : Family.{u} l)
    (d : Comparison l E (𝟙 X.scheme) (r.realization E X) (r.realization E X)
      (r.along E (𝟙 X.scheme))) where
  raw : rawPush l E (𝟙 X.scheme) d.preserves ≅ 𝟭 _
  raw_mate : ∀ K,
    raw.inv.app K = d.rawAdjunction.homEquiv _ _ ((r.identity E X).raw.hom.app K)
  ambient : derivedPush (𝟙 X.scheme) (r.along E (𝟙 X.scheme)).coefficient ≅ 𝟭 _
  ambient_mate : ∀ N,
    ambient.inv.app N =
      d.ordinary.adjunction.homEquiv _ _ ((r.identity E X).ambient.hom.app N)
  compatibility : ∀ K,
    d.comparison.hom.app K ≫ ambient.hom.app ((r.realization E X).J.obj K) =
      (r.realization E X).J.map (raw.hom.app K)

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]

/-- Successive finite extensions commute with both prescribed associators. The equations
include repeated fields and identity embeddings. Source: BS 6.8.15; scalar extension proposition
(blueprint: lem-a1-rational-direct-image-realization). -/
structure FieldComposition (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G)
    {X Y : Base.{u} l} (f : X.scheme ⟶ Y.scheme) (r : Family.{u} l)
    (dE : Comparison l E f (r.realization E X) (r.realization E Y) (r.along E f))
    (dF : Comparison l F f (r.realization F X) (r.realization F Y) (r.along F f))
    (dG : Comparison l G f (r.realization G X) (r.realization G Y) (r.along G f))
    (bEF : FieldChange l E F i f r dE dF) (bFG : FieldChange l F G j f r dF dG)
    (bEG : FieldChange l E G (j.comp i) f r dE dG) : Prop where
  raw : ∀ K,
    (pbcRationalScalarExtension l F G j Y.scheme Y.dimension Y.prime_unit).map
        (bEF.raw.hom.app K) ≫
        bFG.raw.hom.app
          ((pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit).obj K) ≫
        (rawPush l G f dG.preserves).map
          (pbcRationalScalarCompComponent l E F G i j X.scheme
            X.dimension X.prime_unit K).hom =
      (pbcRationalScalarCompComponent l E F G i j Y.scheme Y.dimension Y.prime_unit
          ((rawPush l E f dE.preserves).obj K)).hom ≫ bEG.raw.hom.app K
  ambient : ∀ N,
    (pbcDerivedExtend (r.fieldChange F G j Y).coefficient).map (bEF.ambient.hom.app N) ≫
        bFG.ambient.hom.app
          ((pbcDerivedExtend (r.fieldChange E F i X).coefficient).obj N) ≫
        (derivedPush f (r.along G f).coefficient).map
          (pbcReductionNormalization (r.fieldChange E F i X).coefficient
            (r.fieldChange F G j X).coefficient (r.fieldChange E G (j.comp i) X).coefficient
            (r.fieldComposition E F G i j X).coefficient N).hom =
      (pbcReductionNormalization (r.fieldChange E F i Y).coefficient
          (r.fieldChange F G j Y).coefficient (r.fieldChange E G (j.comp i) Y).coefficient
          (r.fieldComposition E F G i j Y).coefficient
          ((derivedPush f (r.along E f).coefficient).obj N)).hom ≫ bEG.ambient.hom.app N

/-- One family of direct-image comparisons on all separated finite-type k-schemes, for
all finite coefficient fields at once. Its coefficient and identity fields express coherence
of these very comparisons, rather than existence of unrelated isomorphisms.
Source: BS 6.7.2, 6.8.14(2), 6.8.15
(blueprint: lem-a1-rational-direct-image-realization). -/
structure Package (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (r : Family.{u} l) where
  along : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Space.{u} k l} (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))],
    Comparison l E f (r.realization E X.toBase) (r.realization E Y.toBase) (r.along E f)
  fieldChange : ∀ (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    {X Y : Space.{u} k l} (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))],
    FieldChange l E F i f r (along E f) (along F f)
  fieldComposition : ∀ (E F G : Type u) [Field E] [Field F] [Field G]
    [Algebra ℚ_[l] E] [Algebra ℚ_[l] F] [Algebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] [FiniteDimensional ℚ_[l] G]
    (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G)
    {X Y : Space.{u} k l} (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))],
    FieldComposition l E F G i j f r (along E f) (along F f) (along G f)
      (fieldChange E F i f) (fieldChange F G j f) (fieldChange E G (j.comp i) f)
  identity : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Space.{u} k l), Identity l E X.toBase r (along E (𝟙 X.scheme))

end AlgebraicGeometry.Scheme.ContinuousRational.DirectImage
