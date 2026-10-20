/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.SfIntegralDirectImageConstructible
public import Sheaf.Paper.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.OrdinaryCompletedIntegralPullback
import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.Paper.PbcScalarExtension
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.SfCommonStageDirectImage

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
  [over : scheme.Over (Spec (.of k))]
  [finiteType : LocallyOfFiniteType (scheme ↘ Spec (.of k))]
  [quasiCompact : QuasiCompact (scheme ↘ Spec (.of k))]
  [separated : IsSeparated (scheme ↘ Spec (.of k))]

attribute [instance] Space.over Space.finiteType Space.quasiCompact Space.separated

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
  sorry

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

/-- Continuous rational realization commutes with ordinary derived direct image, with its
localization projection, actual adjunction units and counits, finite-extension associators,
and identity normalization.

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15.
The normalizations are the agent-formulated comparison obligation
(blueprint: lem-a1-rational-direct-image-realization).

Proof plan (the complete node proof):

1. The separated finite-type $k$-schemes $X$ and $Y$ are noetherian by
[lem-weil-pbc-finite-type-over-noetherian] (the field $k$ is noetherian) and finite-dimensional
by [lem-kun-dimension-finite-type], and the hypothesis that $\ell$ is invertible supplies the
coefficient hypotheses for the completed adic datum. The definitions of $B_T$ and $E_T$, the
module categories, and their ambient derived categories are therefore the ones fixed by the
cited coefficient and category nodes. The realization functor is the specified
$J_T(Q_TK)=E_T\otimes^L_{B_T}K$.
Uses: def-weil-scheme-morphism-properties, def-weil-l-adic-coefficient-extension,
def-weil-pbc-adic-coefficient-datum, def-weil-sheaf-of-modules-category,
def-weil-abstract-derived-category, lem-per-continuous-rational-derived-realization,
lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type.

2. For an integral constructible $K$, the direct image used in the statement is the ordinary
ringed-topos derived direct image on $B$-modules, and its restriction to the complete integral
category is the strict tower
$R\varprojlim_n\operatorname{Res}_nRf_{*,n}(K\otimes^L_{B_X}(A/\varpi^n)_X)$. The identification
of the ordinary derived direct image with this tower, its reduction maps, and derived
completeness are exactly the conclusions of [prop-weil-pbc-direct-image-limits] together with
the definition [def-weil-derived-direct-image].
Uses: prop-weil-pbc-direct-image-limits, def-weil-derived-direct-image.

3. The output $Rf_*^BK$ is again in the integral bounded constructible category: the
stratified-perfect characterization identifies that category with the completed integral
objects, while the finite-type integral direct-image theorem gives constructibility of every
reduction, a uniform cohomological bound, and the canonical reduction isomorphisms. The
hypotheses needed there hold because $f$ is a morphism of finite-type $k$-schemes and $\ell$ is
invertible in $k$.
Uses: lem-weil-pbc-integral-stratified-perfect-characterization,
lem-sf-integral-direct-image-constructible, def-weil-pbc-bounded-constructible-complete,
def-weil-scheme-morphism-properties.

4. The finiteness needed for localization is qcqs. By
[lem-weil-pbc-finite-type-over-noetherian], $X$ is noetherian (the field $k$ is noetherian). For
both $f$ and its diagonal $\Delta_f$, the inverse image of an affine open of the target is an
open subset of the noetherian space $X$, hence quasi-compact. Thus $f$ is quasi-compact and
quasi-separated. Here quasi-separated means that the diagonal is quasi-compact. These are
precisely the geometric hypotheses in [det-pe-bounded-continuity-direct-image], which will be
applied to the sequence of complexes with transition $\varpi$.
Uses: lem-weil-pbc-finite-type-over-noetherian, def-weil-finite-type-morphism,
def-weil-quasi-separated-morphism, det-pe-bounded-continuity-direct-image.

5. Write $S_T=E_T$ and $C_T=S_T\otimes^L_{B_T}-$, and let $V_T$ restrict $S_T$-modules to
$B_T$-modules. By the localization presentation in
[lem-per-continuous-rational-derived-realization],
$S_T=\varinjlim(B_T\xrightarrow{\varpi}B_T\to\cdots)$. Tensor commutation in
[lem-pc-module-filtered-colimits-tensor] gives, for any module sheaf $M$,
$S_T\otimes_{B_T}M=\varinjlim(M\xrightarrow{\varpi}M\to\cdots)$. That node also states exactness
of filtered colimits. Applying it to a short exact sequence shows that $S_T$ is flat over $B_T$.
Consequently $C_T$ is computed termwise, and
$H^q(C_TN)=\varinjlim(H^qN\xrightarrow{\varpi}H^qN\to\cdots)$. The stage-$n$ map $j_{T,n}:N\to
V_TC_TN$ sends $x$ to $x/\varpi^n$; $j_{T,n+1}\varpi=j_{T,n}$.
Uses: lem-per-continuous-rational-derived-realization, lem-pc-module-filtered-colimits-tensor.

6. The canonical isomorphism $f^{-1}B_Y\cong B_X$ is
[lem-weil-pbc-profinite-coefficient-inverse-image], applied to the finite rings $A/\varpi^n$.
Inverse image, being a left adjoint, preserves the localization colimit, so $f^{-1}S_Y\cong S_X$
as well, compatibly with $B\to S$. Put $P_B=Lf_B^*$, $R_B=Rf_*^B$, $P_S=Lf_S^*$, $R_S=Rf_*^E$.
Their ordinary adjunctions are [def-weil-pbc-proetale-operations]. The commuting coefficient
square satisfies all hypotheses of [lem-weil-pbc-ring-sheaf-change-adjunction]. It supplies
$d:V_YR_S\xrightarrow{\sim}R_BV_X$, the restriction/pullback comparison
$b:V_XP_S\xrightarrow{\sim}P_BV_Y$, and compatibility of these comparisons with adjuncts; $V_T$
reflects isomorphisms.
Uses: lem-weil-pbc-profinite-coefficient-inverse-image, def-weil-pbc-proetale-operations,
lem-weil-pbc-ring-sheaf-change-adjunction.

7. Give $C_T\dashv V_T$ its normalized coefficient adjunction
[lem-pur-sheaf-ring-derived-coefficient-adjunction], with unit $u_T:N\to V_TC_TN$, $x\mapsto
x\otimes1=j_{T,0}(x)$. Define $\beta_K:C_YR_BK\to R_SC_XK$ to be the coefficient adjunct of
$$R_BK\xrightarrow{R_Bu_{X,K}}R_BV_XC_XK\xrightarrow{d^{-1}}V_YR_SC_XK.$$ This is the canonical
localization projection: the coefficient adjunct extends the displayed map by $s\otimes x\mapsto
s\,x$, and $d$ is the canonical comparison of the two factorizations of direct image. In
particular $$d\,V_Y(\beta_K)j_{Y,n}=R_B(j_{X,n}).$$ For $n=0$ this is the defining
coefficient-adjunction equation. For general $n$ it follows by multiplying that equation by
$\varpi^{-n}$; the action on both localized targets is through the same coefficient map. All
maps used here are natural in $K$.
Uses: lem-pur-sheaf-ring-derived-coefficient-adjunction,
lem-weil-pbc-ring-sheaf-change-adjunction.

8. By [lem-weil-pbc-integral-stratified-perfect-characterization], $K$ is bounded as an ambient
$B_X$-complex, so choose a representative zero below some $a$ (standard truncation). Apply
[det-pe-bounded-continuity-direct-image] to its sequence $K\xrightarrow{\varpi}K\to\cdots$. Its
ring sheaf is $B_X$; every complex has the same lower bound $a$, and step 4 established qcqs. It
gives $$\varinjlim_nH^q(R_BK)\xrightarrow{\sim}H^q\bigl(R_B(\varinjlim_nK)\bigr)$$ for every
$q$, with the repeated-$\varpi$ transitions. Step 5 identifies the source with $H^q(V_YC_YR_BK)$
and the target with $H^q(R_BV_XC_XK)$. By the stage equation of step 7 this is exactly
$H^q(d\,V_Y\beta_K)$, rather than an unspecified isomorphism. Hence $V_Y\beta_K$, and therefore
$\beta_K$, is an isomorphism. No assertion that a localized $B_X$-injective is $f_*^E$-acyclic
is used.
Uses: lem-weil-pbc-integral-stratified-perfect-characterization,
det-pe-bounded-continuity-direct-image, lem-weil-pbc-ring-sheaf-change-adjunction.

9. Step 3 makes $R_B$ an exact integral constructible functor, so
[prop-weil-pbc-rational-transport] gives its raw rationalization $Rf_*^{\mathrm{rat}}$. On an
integral representative $Q_XK$ take the comparison to be $\beta_K$ from steps 7--8. The formula
for $J_T$ in [lem-per-continuous-rational-derived-realization] identifies its source with
$J_YRf_*^{\mathrm{rat}}(Q_XK)$ and its target with $Rf_*^EJ_X(Q_XK)$. Naturality extends to a
rational morphism $v/\varpi^n$ by multiplying the integral naturality equation by $\varpi^{-n}$;
changing a fraction representative does not change its value because $\varpi$ is invertible on
the ambient $S$-modules. Thus these components define the required natural isomorphism on the
whole raw rational category.
Uses: prop-weil-pbc-rational-transport, def-weil-pbc-rational-category,
lem-per-continuous-rational-derived-realization.

10. [lem-sp-completed-pullback-adjunction] gives completed pullback left adjoint to direct image
for complete constant $A$-coefficients, with Hom bijection: precompose with the completion unit,
then the ordinary adjunction. Transport it through
[lem-weil-pbc-constant-completion-equivalence]. By [def-weil-pbc-completed-pullback] the
transported left functor is the completed $B$-pullback $\widehat P_B$, and its comparison
$q_M:P_BM\to\widehat P_BM$ (components the finite quotient maps) is, after restriction, the
constant completion unit. [lem-pur-completed-coefficient-pushforward-comparison] identifies the
right functor with $R_B$ (its auxiliary prime $p\ne\ell$ is arbitrary; no characteristic
hypothesis on the schemes). Thus $\widehat P_B\dashv R_B$ on complete objects. For constructible
$M$, $P_BM$ is complete constructible by [lem-tw-ordinary-completed-integral-pullback] and
[lem-weil-pbc-integral-stratified-perfect-characterization], so $q_M$ is invertible. To compare
Hom bijections, apply [lem-weil-pbc-ring-sheaf-change-adjunction] to $\underline A_T\to B_T$;
both inverse-image identifications are isomorphisms
([lem-weil-pbc-profinite-coefficient-inverse-image]). Its $d$ compares the same two ringed-topos
factorizations as $U_YF_R\cong F_AU_X$, and its $b^{-1}$ is the scalar-extension comparison of
the constant-completion lemma. Its adjunct equation and full faithfulness of restriction on
complete objects give the normalized completed bijection $$\operatorname{Hom}(\widehat
P_BM,K)\xrightarrow{-\circ
q_M}\operatorname{Hom}(P_BM,K)\xrightarrow{h_B}\operatorname{Hom}(M,R_BK).$$ Consequently its
counit $\widehat\varepsilon_K$ obeys $\widehat\varepsilon_Kq_{R_BK}=\varepsilon^B_K$, and its
unit is $R_B(q_M)\eta^B_M$.
Uses: lem-sp-completed-pullback-adjunction, lem-weil-pbc-constant-completion-equivalence,
lem-pur-completed-coefficient-pushforward-comparison,
lem-tw-ordinary-completed-integral-pullback,
lem-weil-pbc-integral-stratified-perfect-characterization, def-weil-pbc-completed-pullback,
lem-weil-pbc-ring-sheaf-change-adjunction, lem-weil-pbc-profinite-coefficient-inverse-image.

11. Let $c:P_SC_Y\xrightarrow{\sim}C_XP_B$ be the balanced-tensor pullback comparison, with the
derived comparisons normalized by [lem-sfb-ringed-derived-monoidal-comparisons]. Prove the mate
equation explicitly. For $v:P_BM\to K$, put $t=C_X(v)c_M$. The normalized coefficient unit and
tensor balancing give $$V_X(t)\,b_{C_YM}^{-1}P_B(u_{Y,M})=u_{X,K}v.$$ Both sides send a
representative $x$ to $v(x)\otimes1$; this equality is preserved by the canonical derived
comparisons. By the adjunct compatibility in [lem-weil-pbc-ring-sheaf-change-adjunction], if
$t^\sharp:C_YM\to R_SC_XK$ is its $S$-adjunct, the $B$-adjunct of the left side is
$d\,V_Y(t^\sharp)u_{Y,M}$. The adjunct of the right side is $R_B(u_{X,K})h_B(v)$. The defining
equation for $\beta_K$ in step 7 and naturality of $u_Y$ now imply, by the
coefficient-adjunction bijection, $$h_S(C_X(v)c_M)=\beta_K C_Y(h_B(v)).$$ This proves that the
specified localization projection is the mate of the specified ordinary pullback comparison,
using actual maps.
Uses: lem-sfb-ringed-derived-monoidal-comparisons,
lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-weil-pbc-ring-sheaf-change-adjunction.

12. On constructible objects put $\widehat c_M=C_X(q_M)c_M:P_SC_YM\to C_X\widehat P_BM$. This is
the pullback comparison in [lem-per-continuous-rational-derived-realization], whose completed
pullback is that of [def-weil-pbc-completed-pullback]: both are the balanced coefficient map
followed by the comparison $q_M$ of that definition, whose components are the finite quotient
maps and which is invertible on constructible objects (step 10). If $w:\widehat P_BM\to K$,
apply step 11 with $v=wq_M$. Step 10 identifies $h_B(wq_M)$ with the completed adjunct $\widehat
h_B(w)$. Hence $$h_S(C_X(w)\widehat c_M)=\beta_K C_Y(\widehat h_B(w)).$$ For $w=1_{\widehat
P_BM}$ this gives the unit equation $$\beta_{\widehat P_BM}C_Y(\widehat\eta_M)=R_S(\widehat
c_M)\eta^S_{C_YM}.$$ For $w=\widehat\varepsilon_K$, its completed adjunct is $1_{R_BK}$, giving
the counit equation $$\varepsilon^S_{C_XK}P_S(\beta_K)=C_X(\widehat\varepsilon_K)\widehat
c_{R_BK}.$$ The second equality is the transpose formula of [def-weil-pbc-adjunction-mate]. Thus
the comparison identifies the specified integral adjunction maps after realization.
Uses: lem-per-continuous-rational-derived-realization,
lem-tw-ordinary-completed-integral-pullback, def-weil-pbc-adjunction-mate,
def-weil-pbc-completed-pullback.

13. Apply [lem-sfb-adjunction-localization] to $\widehat P_B\dashv R_B$ on the full integral
constructible categories, with the raw scalar localizations $Q_T$. Each $Q_T$ is a localization
in the sense of [lem-weil-pbc-localization-universal-property] at $W_T=\{\varpi^n1_K\}$: it is
the identity on objects and inverts $\varpi$. A functor $G$ inverting $W_T$ factors uniquely by
$G'(v/\varpi^n)=G(\varpi1_K)^{-n}G(v)$. This is well defined because
$\operatorname{Hom}\otimes_{\mathcal O_E}E$ is the colimit of $\operatorname{Hom}$ along
$\varpi$. Natural transformations extend with the same components, so $G\mapsto G'$ is an
equivalence. Preservation of these categories is step 3 for $R_B$ and
[lem-tw-ordinary-completed-integral-pullback] for pullback. The supplied functor extensions are
[prop-weil-pbc-rational-transport]. The cited adjunction-localization theorem identifies the
rational unit and counit with the images of the integral unit and counit, under the functor
comparisons. Applying $J$ and using the two equations in step 12 proves precisely the claimed
identification with the ambient $S$-module adjunction. This uses the actual localized
adjunction, rather than choosing an adjunction after obtaining a functor isomorphism.
Uses: lem-sfb-adjunction-localization, def-weil-pbc-rational-category,
prop-weil-pbc-rational-transport, lem-tw-ordinary-completed-integral-pullback,
lem-weil-pbc-localization-universal-property.

14. For a finite extension $E\subset L$, [prop-weil-pbc-scalar-extension] supplies the coherent
integral coefficient comparisons for completed pullback and ordinary direct image. Under
realization, coefficient and pullback comparisons are the balanced tensor maps and associators
of [lem-per-continuous-rational-derived-realization]. Step 11 identifies $\beta$ with their
direct-image mate. The integral direct-image comparison for $B_E\to B_L$ and the ambient one for
$E_E\to E_L$ are the canonical ring-change projection maps. The construction of step 7 and the
calculation of step 11, applied to these ring maps instead of $B\to S$
[lem-weil-pbc-ring-sheaf-change-adjunction, lem-pur-sheaf-ring-derived-coefficient-adjunction],
identify each with the mate of its balanced pullback comparison. The coefficient-pasting
identity in [lem-weil-pbc-mate-pasting](1) says that the mate of the composite
coefficient/pullback square is the composite of its two mates. Apply it to the two
factorizations of $B_E\to E_L$, through $B_L$ and through $E_E$: after the given scalar
comparisons, both left squares are the same balanced tensor reassociation. Their right mates
therefore agree. This is the finite-extension compatibility square for $\beta$, including
successive extensions and associators. The same equality passes to raw rationalizations by the
fraction formula of step 9 and [prop-weil-pbc-rational-transport].
Uses: prop-weil-pbc-scalar-extension, lem-per-continuous-rational-derived-realization,
lem-weil-pbc-mate-pasting, prop-weil-pbc-rational-transport,
lem-weil-pbc-ring-sheaf-change-adjunction, lem-pur-sheaf-ring-derived-coefficient-adjunction.

15. When $f$ is an identity morphism, the finite-level direct-image functors and the ambient
right-derived direct image are identities, and every comparison map is the identity by the
normalization of the tower projections and tensor associators. The construction uses continuous
$E_T$-modules throughout; no step identifies these with discrete non-torsion coefficients on the
small étale site.
Uses: def-weil-derived-direct-image, prop-weil-pbc-direct-image-limits,
lem-per-continuous-rational-derived-realization.
-/
theorem rational_direct_image_realization (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k)) :
    ∃ r : Family.{u} l, Nonempty (Package k l r) := by
  sorry

end AlgebraicGeometry.Scheme.ContinuousRational.DirectImage
