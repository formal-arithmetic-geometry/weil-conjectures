/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.PbcQbarStandardCohomology
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.PbcDescentFunctors
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.FieldTheory.Perfect
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.Abelian.DerivedBottomUnitNormalization
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Sheaf.Paper.RationalDirectImageRealization
import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.PbcAutomorphismTransport
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.IntrinsicQbarCategory

/-! # Ordinary constructible cohomology and open--closed restriction on a curve

Source: Bhatt--Scholze, Sections 6.7--6.8, especially Lemmas 6.7.2, 6.7.11,
6.8.7 and Remark 6.8.15; blueprint thm-a1-curve-perverse-heart, Steps 1 and 3
(blueprint: lem-a1-qbar-open-closed-cohomology).

The categories are the recorded PBC finite-stage pair categories. The auxiliary
records below specify the canonical operations and comparison maps in the assertion;
they introduce neither a replacement coefficient category nor arbitrary operation data.

## Main definitions

* `StandardAssertions`: the recorded standard structure, heart and scalar comparisons.
* `ContinuousRealization`: normalized continuous coefficient module representatives.
* `OpenClosed`: actual operations, adjunctions, bottom cohomology and unit comparison.
* `AutomorphismCompatibility`: explicit reindexing equations for all displayed maps.

## Main statements

* `qbar_open_closed_cohomology`: the assertion for a smooth pure-dimensional curve.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w uA vA uB vB uD vD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.A1Cohomology

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]

/-- Cache the existing field-algebra torsion-freeness instance during elaboration.
Source: the coefficient field convention, BS 6.8
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
local instance (priority := 4000) coefficientTorsionFree : Module.IsTorsionFree ℚ_[l] Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

variable [IsAlgClosure ℚ_[l] Ω]

/-- Cache the actual scalar-localization category instance, with identical data.
Source: blueprint finite-stage conventions
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev stageCategory (X : PerAdic.Base k) (E : Padic.FiniteCoefficientFields l Ω) :
    Category (pbcStageCategory l Ω X.scheme E) := inferInstance

attribute [instance 4000] stageCategory

/-- Cache the existing scalar-localization addition; no new Hom laws are chosen.
Source: blueprint finite-stage conventions
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev stagePreadditive (X : PerAdic.Base k) (E : Padic.FiniteCoefficientFields l Ω) :
    Preadditive (pbcStageCategory l Ω X.scheme E) := inferInstance

attribute [instance 4000] stagePreadditive

/-- Cache the existing common-stage addition on the same category.
Source: blueprint common-stage conventions
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev pairPreadditive (X : PerAdic.Base k) :
    Preadditive (pbcQbarCategory l Ω X.scheme) := inferInstance

attribute [instance 4000] pairPreadditive

/-- Cache the original normalized common-stage shift, without changing its data.
Source: blueprint common-stage conventions
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev pairShift (X : PerAdic.Base k) : HasShift (pbcQbarCategory l Ω X.scheme) ℤ :=
  inferInstance

attribute [instance 4000] pairShift

/-- Cache the existing canonical pair-shift additivity instance.
Source: the recorded pair triangulation, blueprint order 1311
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
local instance (priority := 4000) pairShiftAdditive (X : PerAdic.Base k) (n : ℤ) :
    (shiftFunctor (pbcQbarCategory l Ω X.scheme) n).Additive := inferInstance

/-- Cache the existing zero-object instance, without selecting a new zero object.
Source: the recorded pair triangulation, blueprint order 1311
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
local instance (priority := 4000) pairHasZero (X : PerAdic.Base k) :
    HasZeroObject (pbcQbarCategory l Ω X.scheme) := inferInstance

/-- The existing common-stage standard t-structure, with a separated finite-type base.
Source: BS 6.8.14 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev standard (X : PerAdic.Base k) := PerAdic.commonT l Ω X

/-- The existing standard upper aisle, cached without repeating its categorical instances.
Source: BBD 1.3.1 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev upper (X : PerAdic.Base k) (m : ℤ) : ObjectProperty (pbcQbarCategory l Ω X.scheme) :=
  (standard l Ω X).le m

/-- The existing standard lower aisle, with exactly the same membership predicate.
Source: BBD 1.3.1 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev lower (X : PerAdic.Base k) (m : ℤ) : ObjectProperty (pbcQbarCategory l Ω X.scheme) :=
  (standard l Ω X).ge m

/-- The existing heart predicate; this alias fixes its canonical categorical instances.
Source: BBD 1.3.6 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev heartProperty (X : PerAdic.Base k) : ObjectProperty (pbcQbarCategory l Ω X.scheme) :=
  (standard l Ω X).heart

/-- The existing upper truncation functor, with its original objects and maps.
Source: BBD 1.3.3 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev truncLE (X : PerAdic.Base k) (m : ℤ) := (standard l Ω X).truncLE m

/-- The existing lower truncation functor, with its original objects and maps.
Source: BBD 1.3.3 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev truncGE (X : PerAdic.Base k) (m : ℤ) := (standard l Ω X).truncGE m

/-- The existing upper-truncation counit, unchanged.
Source: BBD 1.3.3 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev truncLECounit (X : PerAdic.Base k) (m : ℤ) := (standard l Ω X).truncLEι m

/-- The existing lower-truncation unit, unchanged.
Source: BBD 1.3.3 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev truncGEUnit (X : PerAdic.Base k) (m : ℤ) := (standard l Ω X).truncGEπ m

/-- The existing heart-valued zeroth cohomology functor.
Source: BBD 1.3.6 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev zeroth (X : PerAdic.Base k) := (standard l Ω X).homology₀

/-- The full standard heart, with the original underlying Hom sets.
Source: BS 6.8.14 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev Heart (X : PerAdic.Base k) := (heartProperty l Ω X).FullSubcategory

/-- The actual full inclusion of constructible sheaves into the pair category.
Source: BS 6.8.14 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev inclusion (X : PerAdic.Base k) := ObjectProperty.ι (heartProperty l Ω X)

/-- Ordinary degree-m cohomology with values in the heart: H^0(K[m]).
Source: BS 6.8.11, 6.8.14 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def cohomology (X : PerAdic.Base k) (m : ℤ) :
    pbcQbarCategory l Ω X.scheme ⥤ Heart l Ω X :=
  shiftFunctor _ m ⋙ (zeroth l Ω X)

/-- Exact inverse image is the existing normalized common-stage completed pullback.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev pull {X Y : PerAdic.Base k} (f : X.scheme ⟶ Y.scheme) :=
  PerAdic.commonPull l Ω f

/-- The heart restriction is the full-subcategory lift of that same inverse image.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def heartPull {X Y : PerAdic.Base k} (f : X.scheme ⟶ Y.scheme)
    (h : ∀ K : Heart l Ω Y, (heartProperty l Ω X) ((pull l Ω f).obj K.obj)) :
    Heart l Ω Y ⥤ Heart l Ω X :=
  (heartProperty l Ω X).lift (inclusion l Ω Y ⋙ pull l Ω f) h

/-- H^0(K) to K, the standard truncation counit whenever K is nonnegative.
Source: BBD 1.3.3, ordinary truncations
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def degreeZeroCounit (X : PerAdic.Base k) (K : pbcQbarCategory l Ω X.scheme)
    (h : (lower l Ω X) 0 K) :
    ((zeroth l Ω X).obj K).obj ⟶ K :=
  letI : (standard l Ω X).IsGE K 0 := ⟨h⟩
  (standard l Ω X).homology₀ε K

/-- Canonical finite-stage direct image and its coherent scalar comparisons. All object
and morphism maps are the actual completed direct image, rationalized on tensor Homs;
the beta components are fixed by PbcDirectImageBetaSpec, including repeated fields.
Source: BS 6.7.2, 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure DirectImage {X Y : PerAdic.Base k} (f : X.scheme ⟶ Y.scheme) where
  preserves : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X.scheme E),
    PbcIsBoundedConstructibleComplete Y.scheme (pbcStageDatum.{u} l Ω E)
      ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj)
  family : StageSystem.Morphism (PerAdic.stages l Ω X) (PerAdic.stages l Ω Y)
  stage : ∀ E : Padic.FiniteCoefficientFields l Ω,
    family.Φ E = pbcDescentDirectImage l Ω f preserves E
  scalar : PbcDirectImageBetaSpec l Ω f preserves family

/-- The canonical right derived image on the pair category, with its existing
representative-map formula. Source: BS 6.8.15
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev DirectImage.functor {X Y : PerAdic.Base k} {f : X.scheme ⟶ Y.scheme}
    (R : DirectImage l Ω f) := R.family.functor

/-- Its degree-zero restriction on sheaves is H^0 Rf_* applied to the actual inclusion.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def DirectImage.onHeart {X Y : PerAdic.Base k} {f : X.scheme ⟶ Y.scheme}
    (R : DirectImage l Ω f) : Heart l Ω X ⥤ Heart l Ω Y :=
  inclusion l Ω X ⋙ R.functor ⋙ (zeroth l Ω Y)

/-- The canonical completed-unit map on an integral representative. Completion is
inserted after ordinary derived inverse image, before rationalization.
Source: BS 6.8.15; the recorded ringed derived adjunction
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def integralUnit {X Y : PerAdic.Base k} (f : X.scheme ⟶ Y.scheme)
    (R : DirectImage l Ω f) (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω Y.scheme E) :
    K ⟶ ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (R.preserves E)).obj
        ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
          (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E))
          (PerAdic.integralPull_mem l (pbcFiniteField.{u} l Ω E) f)).obj K)) :=
  ObjectProperty.homMk
    ((pbcActualDerivedAdjunction f (pbcStageDatum.{u} l Ω E)).unit.app K.obj ≫
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).map
        ((pbcActualCompletedPullUnit f (pbcStageDatum.{u} l Ω E)).app K.obj))

/-- The normalized identification of pullback with its finite-stage computation.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def pullStage {X Y : PerAdic.Base k} (f : X.scheme ⟶ Y.scheme)
    (E : Padic.FiniteCoefficientFields l Ω) :
    PerAdic.inclusion l Ω Y E ⋙ pull l Ω f ≅
      PerAdic.rationalPull l (pbcFiniteField.{u} l Ω E) f ⋙ PerAdic.inclusion l Ω X E :=
  PerAdic.pullInclusionIso l Ω f E

/-- The normalized finite-stage computation of direct image.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def DirectImage.stageIso {X Y : PerAdic.Base k} {f : X.scheme ⟶ Y.scheme}
    (R : DirectImage l Ω f) (E : Padic.FiniteCoefficientFields l Ω) :
    PerAdic.inclusion l Ω X E ⋙ R.functor ≅
      pbcDescentDirectImage l Ω f R.preserves E ⋙ PerAdic.inclusion l Ω Y E :=
  R.family.ιCompFunctorIso E ≪≫ Functor.isoWhiskerRight (eqToIso (R.stage E)) _

/-- A derived adjunction has the actual integral unit, rather than a scalar-twisted
unit. The displayed comparisons are fixed by the recorded finite-stage families.
Source: BS 6.8.15 and the actual-unit normalization in blueprint Step 3
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def UnitNormalization {X Y : PerAdic.Base k} {f : X.scheme ⟶ Y.scheme}
    (R : DirectImage l Ω f) (A : pull l Ω f ⊣ R.functor) : Prop :=
  ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y.scheme E),
    HEq (A.unit.app ((PerAdic.inclusion l Ω Y E).obj
        ((pbcStageLocalization l Ω Y.scheme E).obj K)) ≫
      R.functor.map ((pullStage l Ω f E).hom.app
        ((pbcStageLocalization l Ω Y.scheme E).obj K)) ≫
      (R.stageIso l Ω E).hom.app
        ((PerAdic.rationalPull l (pbcFiniteField.{u} l Ω E) f).obj
          ((pbcStageLocalization l Ω Y.scheme E).obj K)))
      ((PerAdic.inclusion l Ω Y E).map
        ((pbcStageLocalization l Ω Y.scheme E).map (integralUnit l Ω f R E K)))

/-- The ordinary sheaf adjunction is induced by the actual derived adjunction. Its Hom
transpose is fixed after the standard H^0-to-K counit, so units and counits are canonical.
Source: blueprint Step 3; ordinary inverse/direct-image adjunction
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def HeartAdjunctionNormalization {X Y : PerAdic.Base k} {f : X.scheme ⟶ Y.scheme}
    (R : DirectImage l Ω f) (A : pull l Ω f ⊣ R.functor)
    (h : ∀ F : Heart l Ω Y, (heartProperty l Ω X) ((pull l Ω f).obj F.obj))
    (B : heartPull l Ω f h ⊣ R.onHeart l Ω)
    (lower : ∀ G : Heart l Ω X, (lower l Ω Y) 0 (R.functor.obj G.obj)) : Prop :=
  ∀ (F : Heart l Ω Y) (G : Heart l Ω X) (a : (heartPull l Ω f h).obj F ⟶ G),
    (B.homEquiv F G a).hom ≫ degreeZeroCounit l Ω Y (R.functor.obj G.obj) (lower G) =
      A.homEquiv F.obj G.obj a.hom


/-- The standard structure agrees with the recorded cohomology, ordinary ambient
cohomology on integral representatives, finite scalar extension and lisse stratifications.
Source: BS 6.8.3, 6.8.6, 6.8.11, 6.8.14
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def StandardAssertions (X : PerAdic.Base k) : Prop :=
  standard l Ω X = pbcQbarStandardT l Ω X.scheme ∧
  (standard l Ω X).bounded = ⊤ ∧
  (∀ n : ℤ, Nonempty (cohomology l Ω X n ⋙ inclusion l Ω X ≅
    pbcQbarCohomology l Ω X.scheme n)) ∧
  (∀ E : Padic.FiniteCoefficientFields l Ω,
    PerAdic.RationalStandardAssertions l (pbcFiniteField.{u} l Ω E) X ∧
    (∀ M : pbcStageCategory l Ω X.scheme E,
      (PerAdic.rationalLE l (pbcFiniteField.{u} l Ω E) X 0 M ∧
        PerAdic.rationalGE l (pbcFiniteField.{u} l Ω E) X 0 M) ↔
        ∃ S : FiniteLocallyClosedStratification X.scheme,
          PerAdic.LisseStrata l (pbcFiniteField.{u} l Ω E) X.scheme M S)) ∧
  (∀ K : pbcQbarCategory l Ω X.scheme,
    (heartProperty l Ω X) K ↔
      ∃ (E : Padic.FiniteCoefficientFields l Ω) (M : PerAdic.Heart l
        (pbcFiniteField.{u} l Ω E) X),
        Nonempty (K ≅ (PerAdic.inclusion l Ω X E).obj M.obj)) ∧
  (∀ (E F : Padic.FiniteCoefficientFields l Ω) (a : E ≤ F) (n : ℤ),
    Nonempty (PerAdic.rationalTruncLE l (pbcFiniteField.{u} l Ω E) X n ⋙
      (PerAdic.stages l Ω X).T a ≅ (PerAdic.stages l Ω X).T a ⋙
        PerAdic.rationalTruncLE l (pbcFiniteField.{u} l Ω F) X n) ∧
    Nonempty (PerAdic.rationalTruncGE l (pbcFiniteField.{u} l Ω E) X n ⋙
      (PerAdic.stages l Ω X).T a ≅ (PerAdic.stages l Ω X).T a ⋙
        PerAdic.rationalTruncGE l (pbcFiniteField.{u} l Ω F) X n) ∧
    Nonempty (PerAdic.rationalCohomology l (pbcFiniteField.{u} l Ω E) X n ⋙
      (PerAdic.stages l Ω X).T a ≅ (PerAdic.stages l Ω X).T a ⋙
        PerAdic.rationalCohomology l (pbcFiniteField.{u} l Ω F) X n)) ∧
  (∀ (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ),
    Nonempty (PerAdic.inclusion l Ω X E ⋙ (truncLE l Ω X) n ≅
      PerAdic.rationalTruncLE l (pbcFiniteField.{u} l Ω E) X n ⋙
        PerAdic.inclusion l Ω X E) ∧
    Nonempty (PerAdic.inclusion l Ω X E ⋙ (truncGE l Ω X) n ≅
      PerAdic.rationalTruncGE l (pbcFiniteField.{u} l Ω E) X n ⋙
        PerAdic.inclusion l Ω X E) ∧
    Nonempty (PerAdic.inclusion l Ω X E ⋙ cohomology l Ω X n ⋙ inclusion l Ω X ≅
      PerAdic.rationalCohomology l (pbcFiniteField.{u} l Ω E) X n ⋙
        PerAdic.inclusion l Ω X E))

/-- Composition of two specified reindexing comparisons; all associators are retained.
Source: blueprint Frobenius reindexing argument
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def composeExchange {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {D : Type uD} [Category.{vD} D] {α : A ⥤ A} {β : B ⥤ B} {γ : D ⥤ D}
    {F : A ⥤ B} {G : B ⥤ D} (eF : F ⋙ β ≅ α ⋙ F) (eG : G ⋙ γ ≅ β ⋙ G) :
    (F ⋙ G) ⋙ γ ≅ α ⋙ (F ⋙ G) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eG ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eF _ ≪≫
      Functor.associator _ _ _

/-- Same-category composition of the canonical truncation exchanges.
Source: BBD 1.3.3 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def composeExchangeSelf {A : Type uA} [Category.{vA} A]
    {α β γ F G : A ⥤ A} (eF : F ⋙ β ≅ α ⋙ F) (eG : G ⋙ γ ≅ β ⋙ G) :
    (F ⋙ G) ⋙ γ ≅ α ⋙ (F ⋙ G) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eG ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eF _ ≪≫
      Functor.associator _ _ _

/-- The continuous finite-field realization used by the cohomology assertion. The
coefficient ring is the sheaf localization of the actual completion: its universal
property, not a choice of a map, fixes it. Inverting l and inverting a uniformizer
are equivalent. The integral comparison fixes the functor on objects and integral
maps, hence also on fractions, since a functor preserves inverses.
Source: BS 6.8.3, 6.8.6--6.8.8
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure ContinuousStage (X : PerAdic.Base k) (E : Padic.FiniteCoefficientFields l Ω) where
  ring : Sheaf (ProEt.topology X.scheme) CommRingCat.{u + 1}
  scalar : pbcAdicCompletion X.scheme (pbcStageDatum.{u} l Ω E) ⟶ ring
  invertible : ∀ V : X.scheme.ProEtᵒᵖ, IsUnit (l : ring.obj.obj V)
  universal : ∀ S : Sheaf (ProEt.topology X.scheme) CommRingCat.{u + 1},
    (∀ V : X.scheme.ProEtᵒᵖ, IsUnit (l : S.obj.obj V)) →
    Function.Bijective (fun f : ring ⟶ S ↦ scalar ≫ f)
  realization : pbcStageCategory l Ω X.scheme E ⥤ DerivedCategory (pbcModules X.scheme ring)
  integral : pbcStageLocalization l Ω X.scheme E ⋙ realization ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcStageDatum.{u} l Ω E)) ⋙
      pbcDerivedExtend scalar
  cohomology : ∀ n : ℤ,
    PerAdic.rationalCohomology l (pbcFiniteField.{u} l Ω E) X n ⋙ realization ≅
      realization ⋙ DerivedCategory.homologyFunctor (pbcModules X.scheme ring) n ⋙
        DerivedCategory.singleFunctor (pbcModules X.scheme ring) 0

/-- Continuous finite coefficient rings and their canonical transition maps. The
normalization against completed coefficient inclusion uniquely determines each map.
Source: BS 6.8.15 and the continuous-ring colimit in blueprint Step 1
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure ContinuousCoefficients (X : PerAdic.Base k) where
  stage : ∀ E : Padic.FiniteCoefficientFields l Ω, ContinuousStage l Ω X E
  transition : ∀ {E F : Padic.FiniteCoefficientFields l Ω}, E ≤ F →
    ((stage E).ring ⟶ (stage F).ring)
  normalized : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
    (stage E).scalar ≫ transition h = pbcCompletedScalarMap l Ω X.scheme h ≫ (stage F).scalar
  identity : ∀ E : Padic.FiniteCoefficientFields l Ω, transition (le_refl E) = 𝟙 _
  composition : ∀ {E F G : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (h' : F ≤ G),
    transition (h.trans h') = transition h ≫ transition h'

/-- The actual filtered diagram of continuous finite coefficient rings.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def ContinuousCoefficients.diagram {X : PerAdic.Base k} (R : ContinuousCoefficients l Ω X) :
    Padic.FiniteCoefficientFields l Ω ⥤ Sheaf (ProEt.topology X.scheme) CommRingCat.{u + 1} where
  obj E := (R.stage E).ring
  map h := R.transition (leOfHom h)
  map_id E := R.identity E
  map_comp h h' := R.composition (leOfHom h) (leOfHom h')

/-- The continuous algebraic-closure coefficient sheaf, specified by its filtered
colimit universal property. This also works when the presentation index has a larger
universe than the ring sheaves: no equality of those universes is imposed.
Source: blueprint sk-prop-sfb-qlbar-colimit-x; BS 6.8.15
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure ContinuousRealization (X : PerAdic.Base k) where
  coefficients : ContinuousCoefficients l Ω X
  cocone : Cocone (coefficients.diagram l Ω)
  isColimit : IsColimit cocone

/-- The actual continuous algebraic-closure coefficient ring in the universal cocone.
Source: blueprint sk-prop-sfb-qlbar-colimit-x
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev ContinuousRealization.qbarRing {X : PerAdic.Base k}
    (R : ContinuousRealization l Ω X) := R.cocone.pt

/-- The module representative at algebraic-closure coefficients is actual derived
extension from its finite continuous coefficient field.
Source: blueprint Step 1 and sk-prop-sfb-qlbar-colimit-x
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev ContinuousRealization.qbarRealization {X : PerAdic.Base k}
    (R : ContinuousRealization l Ω X) (E : Padic.FiniteCoefficientFields l Ω) :=
  (R.coefficients.stage E).realization ⋙ pbcDerivedExtend (R.cocone.ι.app E)

/-- Cohomology, viewed as a degree-zero object of the ambient derived category.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev ordinaryCohomology (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory A] (n : ℤ) :=
  DerivedCategory.homologyFunctor A n ⋙ DerivedCategory.singleFunctor A 0

/-- The canonical homology/exact-functor comparison, followed by the canonical
single-degree comparison. Neither comparison is a field that can be twisted.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def exactCohomologyExchange {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasDerivedCategory A] {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    ordinaryCohomology A n ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ ordinaryCohomology B n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (F.mapDerivedCategorySingleFunctor 0) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapDerivedCategoryHomologyFunctorIso n) _ ≪≫
    Functor.associator _ _ _

/-- Exactness of extension to the continuous colimit ring, and the comparison
with termwise extension fixed by the actual derived extension counit. This
normalization uniquely determines `comparison` on the localization.
Source: BS 6.8.15 and blueprint Step 1
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure ContinuousExactExtension {X : PerAdic.Base k}
    {A B : Sheaf (ProEt.topology X.scheme) CommRingCat.{u + 1}} (φ : A ⟶ B) where
  limits : PreservesFiniteLimits (pbcExtend φ)
  colimits : PreservesFiniteColimits (pbcExtend φ)
  comparison : letI := limits
    letI := colimits
    pbcDerivedExtend φ ≅ (pbcExtend φ).mapDerivedCategory
  normalized : letI := limits
    letI := colimits
    Functor.whiskerLeft DerivedCategory.Qh comparison.hom ≫
      (pbcExtend φ).mapDerivedCategoryFactorsh.hom = pbcExtensionCounit φ

/-- Scalar-extension/cohomology commutation obtained from the normalized
extension comparison and the canonical exact-functor homology comparison.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def ContinuousExactExtension.cohomology {X : PerAdic.Base k}
    {A B : Sheaf (ProEt.topology X.scheme) CommRingCat.{u + 1}} {φ : A ⟶ B}
    (e : ContinuousExactExtension φ) (n : ℤ) :
    ordinaryCohomology (pbcModules X.scheme A) n ⋙ pbcDerivedExtend φ ≅
      pbcDerivedExtend φ ⋙ ordinaryCohomology (pbcModules X.scheme B) n :=
  letI := e.limits
  letI := e.colimits
  Functor.isoWhiskerLeft _ e.comparison ≪≫ exactCohomologyExchange (pbcExtend φ) n ≪≫
    Functor.isoWhiskerRight e.comparison.symm _

/-- Specified continuous cohomology comparison, normalized by the finite-stage
comparison and extension along the actual cocone injection. It is data, so the
Frobenius assertion below refers to this comparison, rather than to any iso.
Source: blueprint Step 1; BS 6.8.15
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure ContinuousRealization.Cohomology {X : PerAdic.Base k}
    (R : ContinuousRealization l Ω X) where
  extension : ∀ E : Padic.FiniteCoefficientFields l Ω,
    ContinuousExactExtension (R.cocone.ι.app E)

/-- The specified continuous comparison is the composite of finite-stage
cohomology and the normalized exact extension along the cocone injection.
Its normalization is by construction, with no independent comparison field.
Source: blueprint Step 1; BS 6.8.15
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def ContinuousRealization.Cohomology.comparison {X : PerAdic.Base k}
    {R : ContinuousRealization l Ω X} (H : R.Cohomology l Ω)
    (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ) :
    PerAdic.rationalCohomology l (pbcFiniteField.{u} l Ω E) X n ⋙
      R.qbarRealization l Ω E ≅ R.qbarRealization l Ω E ⋙
        ordinaryCohomology (pbcModules X.scheme (R.qbarRing l Ω)) n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((R.coefficients.stage E).cohomology n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((H.extension E).cohomology n) ≪≫
    (Functor.associator _ _ _).symm

/-- The restriction/cohomology comparison uses the existing canonical truncation
comparisons for a t-exact triangulated functor. Only the functor structures
are supplied; the comparison maps themselves are constructed below.
Source: BS 6.8.15, BBD 1.3.3
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure CohomologyRestriction {A : Type uA} [Category.{vA} A] [Preadditive A]
    [HasZeroObject A] [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive]
    [Pretriangulated A] [IsTriangulated A]
    (t : Triangulated.TStructure A) (P : A ⥤ A) where
  shift : P.CommShift ℤ
  triangulated : letI := shift
    P.IsTriangulated
  t_exact : P.IsTExact t t

/-- Restriction/cohomology comparison built from canonical upper and lower truncation
comparisons, followed by the functor's shift comparison. There is no comparison field.
Source: BBD 1.3.3; BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def CohomologyRestriction.cohomology {A : Type uA} [Category.{vA} A] [Preadditive A]
    [HasZeroObject A] [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive]
    [Pretriangulated A] [IsTriangulated A]
    {t : Triangulated.TStructure A} {P : A ⥤ A}
    (e : CohomologyRestriction t P) (n : ℤ) :
    PerAdic.cohomology t n ⋙ P ≅ P ⋙ PerAdic.cohomology t n := by
  letI := e.shift
  letI := e.triangulated
  letI := e.t_exact
  unfold PerAdic.cohomology
  exact composeExchangeSelf (α := P) (β := P) (γ := P)
    (F := t.truncLE n) (G := t.truncGE n ⋙ shiftFunctor A n)
    (P.eTruncLTIso t t (n + 1 : ℤ))
    (composeExchangeSelf (α := P) (β := P) (γ := P)
      (F := t.truncGE n) (G := shiftFunctor A n)
      (P.eTruncGEIso t t (n : ℤ)) (P.commShiftIso n))

/-- Specialize the canonical t-exact restriction data to the recorded finite
coefficient standard structure, retaining its own localized shift instance.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev RationalCohomologyRestriction (X : PerAdic.Base k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (P : pbcStageCategory l Ω X.scheme E ⥤ pbcStageCategory l Ω X.scheme E) :=
  letI : HasShift (pbcStageCategory l Ω X.scheme E) ℤ :=
    pbcScalarRationalHasShift l (pbcFiniteField.{u} l Ω E) X.scheme
  letI : ∀ n : ℤ, (shiftFunctor (pbcStageCategory l Ω X.scheme E) n).Additive :=
    pbcScalarRationalShiftAdditive l (pbcFiniteField.{u} l Ω E) X.scheme
  letI : Pretriangulated (pbcStageCategory l Ω X.scheme E) :=
    pbcScalarRationalPretriangulated l (pbcFiniteField.{u} l Ω E) X.scheme
  letI : IsTriangulated (pbcStageCategory l Ω X.scheme E) :=
    pbcScalarRationalIsTriangulated l (pbcFiniteField.{u} l Ω E) X.scheme
  CohomologyRestriction (PerAdic.rationalT l (pbcFiniteField.{u} l Ω E) X) P

/-- Canonical coefficient and module pullback, realization exchange, and the
finite-stage restriction data used for continuous Frobenius transport.
Source: BS 6.8.15; blueprint Weil-pair convention
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure ContinuousFrobeniusTransport {X : PerAdic.Base k}
    (R : ContinuousRealization l Ω X) (E : Padic.FiniteCoefficientFields l Ω)
    (g : Aut X.scheme) where
  coefficientPull :
    (proEtaleSheafInverseImage g.hom CommRingCat.{u + 1}).obj
        (R.qbarRing l Ω) ≅ R.qbarRing l Ω
  stagePull : ∀ E : Padic.FiniteCoefficientFields l Ω,
    (proEtaleSheafInverseImage g.hom CommRingCat.{u + 1}).obj
        ((R.coefficients.stage E).ring) ≅ (R.coefficients.stage E).ring
  stagePull_normalized : ∀ E : Padic.FiniteCoefficientFields l Ω,
    (proEtaleSheafInverseImage g.hom CommRingCat.{u + 1}).map
        ((R.coefficients.stage E).scalar) ≫ (stagePull E).hom =
      completedCoefficientMap g.hom (pbcStageDatum.{u} l Ω E) ≫
        (R.coefficients.stage E).scalar
  coefficientPull_normalized : ∀ E : Padic.FiniteCoefficientFields l Ω,
    (proEtaleSheafInverseImage g.hom CommRingCat.{u + 1}).map
        (R.cocone.ι.app E) ≫ coefficientPull.hom =
      (stagePull E).hom ≫ R.cocone.ι.app E
  exchange :
    R.qbarRealization l Ω E ⋙
      (proEtaleRingModulePullback g.hom (R.qbarRing l Ω) (R.qbarRing l Ω)
        coefficientPull).mapDerivedCategory ≅
      pbcRationalIsoPullback g (pbcStageDatum.{u} l Ω E)
        (pbcStageUniformizer.{u} l Ω E) ⋙ R.qbarRealization l Ω E
  restriction : RationalCohomologyRestriction l Ω X E
    (pbcRationalIsoPullback g (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E))

/-- The recorded rational automorphism pullback, without freely chosen replacement data.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev ContinuousFrobeniusTransport.sourcePull {X : PerAdic.Base k}
    {R : ContinuousRealization l Ω X} {E : Padic.FiniteCoefficientFields l Ω}
    {g : Aut X.scheme} (_e : ContinuousFrobeniusTransport l Ω R E g) :=
  pbcRationalIsoPullback g (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)

/-- The actual ringed module pullback, derived by exact termwise transport.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev ContinuousFrobeniusTransport.modulePull {X : PerAdic.Base k}
    {R : ContinuousRealization l Ω X} {E : Padic.FiniteCoefficientFields l Ω}
    {g : Aut X.scheme} (e : ContinuousFrobeniusTransport l Ω R E g) :=
  (proEtaleRingModulePullback g.hom (R.qbarRing l Ω) (R.qbarRing l Ω)
    e.coefficientPull).mapDerivedCategory

/-- The canonical transport to the existing endofunctor-fixed pair category.
Source: blueprint Weil-pair convention
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def ContinuousFrobeniusTransport.pairTransport {X : PerAdic.Base k}
    {R : ContinuousRealization l Ω X} {E : Padic.FiniteCoefficientFields l Ω}
    {g : Aut X.scheme} (e : ContinuousFrobeniusTransport l Ω R E g) :=
  Endofunctor.IsoAlgebra.mapOfNatIso e.exchange

/-- Left exchange derived from realization exchange and the normalized rational
restriction/cohomology comparison.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def ContinuousFrobeniusTransport.leftExchange {X : PerAdic.Base k}
    {R : ContinuousRealization l Ω X} {E : Padic.FiniteCoefficientFields l Ω}
    {g : Aut X.scheme} (e : ContinuousFrobeniusTransport l Ω R E g) (n : ℤ) :
    (PerAdic.rationalCohomology l (pbcFiniteField.{u} l Ω E) X n ⋙
      R.qbarRealization l Ω E) ⋙ e.modulePull l Ω ≅
      e.sourcePull l Ω ⋙ (PerAdic.rationalCohomology l
        (pbcFiniteField.{u} l Ω E) X n ⋙ R.qbarRealization l Ω E) :=
  letI : HasShift (pbcStageCategory l Ω X.scheme E) ℤ :=
    pbcScalarRationalHasShift l (pbcFiniteField.{u} l Ω E) X.scheme
  letI : ∀ n : ℤ, (shiftFunctor (pbcStageCategory l Ω X.scheme E) n).Additive :=
    pbcScalarRationalShiftAdditive l (pbcFiniteField.{u} l Ω E) X.scheme
  letI : Pretriangulated (pbcStageCategory l Ω X.scheme E) :=
    pbcScalarRationalPretriangulated l (pbcFiniteField.{u} l Ω E) X.scheme
  letI : IsTriangulated (pbcStageCategory l Ω X.scheme E) :=
    pbcScalarRationalIsTriangulated l (pbcFiniteField.{u} l Ω E) X.scheme
  composeExchange (e.restriction.cohomology n) e.exchange

/-- Right exchange derived from realization exchange and the canonical
homology/exact-pullback comparison, rather than an independent record field.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def ContinuousFrobeniusTransport.rightExchange {X : PerAdic.Base k}
    {R : ContinuousRealization l Ω X} {E : Padic.FiniteCoefficientFields l Ω}
    {g : Aut X.scheme} (e : ContinuousFrobeniusTransport l Ω R E g) (n : ℤ) :
    (R.qbarRealization l Ω E ⋙
      ordinaryCohomology (pbcModules X.scheme (R.qbarRing l Ω)) n) ⋙
        e.modulePull l Ω ≅ e.sourcePull l Ω ⋙ (R.qbarRealization l Ω E ⋙
          ordinaryCohomology (pbcModules X.scheme (R.qbarRing l Ω)) n) :=
  composeExchange e.exchange
    (exactCohomologyExchange (proEtaleRingModulePullback g.hom
      (R.qbarRing l Ω) (R.qbarRing l Ω) e.coefficientPull) n)

/-- Equivariance only for the specified normalized continuous comparison.
The outer theorem chooses this data together with its transport; arbitrary
componentwise scalar twists are not asserted to be equivariant.
Source: BS 6.8.15; blueprint Weil-pair convention
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure ContinuousCohomologyFrobenius {X : PerAdic.Base k}
    (R : ContinuousRealization l Ω X) (H : R.Cohomology l Ω)
    (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ) (g : Aut X.scheme) where
  transport : ContinuousFrobeniusTransport l Ω R E g
  equivariant :
    Functor.whiskerRight (H.comparison l Ω E n).hom (transport.modulePull l Ω) ≫
        (transport.rightExchange l Ω n).hom =
      (transport.leftExchange l Ω n).hom ≫
        Functor.whiskerLeft (transport.sourcePull l Ω) (H.comparison l Ω E n).hom

/-- T-exact restriction, its sheaf restriction, and its ordinary cohomology and
truncation identifications. Truncation comparisons retain their unit/counit equations.
Source: BS 6.8.15; BBD 1.3.3
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure Restriction {X Y : PerAdic.Base k} (f : X.scheme ⟶ Y.scheme) where
  shift : (pull l Ω f).CommShift ℤ
  triangulated : letI : (pull l Ω f).CommShift ℤ := shift
    (pull l Ω f).IsTriangulated
  t_exact : ∀ (n : ℤ) (K : pbcQbarCategory l Ω Y.scheme),
    ((upper l Ω Y) n K → (upper l Ω X) n ((pull l Ω f).obj K)) ∧
    ((lower l Ω Y) n K → (lower l Ω X) n ((pull l Ω f).obj K))
  heart_mem : ∀ F : Heart l Ω Y, (heartProperty l Ω X) ((pull l Ω f).obj F.obj)
  cohomologyIso : ∀ n : ℤ, pull l Ω f ⋙ cohomology l Ω X n ≅
    cohomology l Ω Y n ⋙ heartPull l Ω f heart_mem
  truncLEIso : ∀ n : ℤ, (truncLE l Ω Y) n ⋙ pull l Ω f ≅
    pull l Ω f ⋙ (truncLE l Ω X) n
  truncGEIso : ∀ n : ℤ, (truncGE l Ω Y) n ⋙ pull l Ω f ≅
    pull l Ω f ⋙ (truncGE l Ω X) n
  truncLE_unit : ∀ (n : ℤ) (K : pbcQbarCategory l Ω Y.scheme),
    (truncLEIso n).hom.app K ≫ ((truncLECounit l Ω X) n).app ((pull l Ω f).obj K) =
      (pull l Ω f).map (((truncLECounit l Ω Y) n).app K)
  truncGE_unit : ∀ (n : ℤ) (K : pbcQbarCategory l Ω Y.scheme),
    (pull l Ω f).map (((truncGEUnit l Ω Y) n).app K) ≫
      (truncGEIso n).hom.app K = ((truncGEUnit l Ω X) n).app ((pull l Ω f).obj K)
  cohomology_normalized : ∀ (m : ℤ) (K : pbcQbarCategory l Ω Y.scheme),
    letI : (pull l Ω f).CommShift ℤ := shift
    ((cohomologyIso m).hom.app K).hom =
      ((zeroth l Ω X).map (((pull l Ω f).commShiftIso m).inv.app K)).hom ≫
        ((truncGE l Ω X) 0).map ((truncLEIso 0).inv.app (K⟦m⟧)) ≫
          (truncGEIso 0).inv.app (((truncLE l Ω Y) 0).obj (K⟦m⟧))

/-- The sheaf restriction belonging to the specified derived restriction.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev Restriction.onHeart {X Y : PerAdic.Base k} {f : X.scheme ⟶ Y.scheme}
    (P : Restriction l Ω f) := heartPull l Ω f P.heart_mem

/-- The core open--closed operations and normalized adjunction data.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure OpenClosedCore {C U Z : PerAdic.Base k}
    (j : U.scheme ⟶ C.scheme) (i : Z.scheme ⟶ C.scheme) where
  openRestriction : Restriction l Ω j
  closedRestriction : Restriction l Ω i
  openImage : DirectImage l Ω j
  closedImage : DirectImage l Ω i
  openAdjunction : pull l Ω j ⊣ openImage.functor
  closedAdjunction : pull l Ω i ⊣ closedImage.functor
  openUnit : UnitNormalization l Ω openImage openAdjunction
  closedUnit : UnitNormalization l Ω closedImage closedAdjunction
  openSheafAdjunction : openRestriction.onHeart l Ω ⊣ openImage.onHeart l Ω
  closedSheafAdjunction : closedRestriction.onHeart l Ω ⊣ closedImage.onHeart l Ω
  lower_bound : ∀ (m : ℤ) (M : pbcQbarCategory l Ω U.scheme),
    (lower l Ω U) m M → (lower l Ω C) m (openImage.functor.obj M)
  closed_lower_bound : ∀ (m : ℤ) (M : pbcQbarCategory l Ω Z.scheme),
    (lower l Ω Z) m M → (lower l Ω C) m (closedImage.functor.obj M)
  bottom : ∀ (m : ℤ) (M : pbcQbarCategory l Ω U.scheme)
    (_h : (lower l Ω U) m M),
    (cohomology l Ω C m).obj (openImage.functor.obj M) ≅
      (openImage.onHeart l Ω).obj ((cohomology l Ω U m).obj M)

/-- Remaining open--closed cohomology clauses, attached to the actual core data.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def OpenClosedAssertions {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme}
    (P : OpenClosedCore l Ω j i) : Prop :=
  HeartAdjunctionNormalization l Ω P.openImage P.openAdjunction
    P.openRestriction.heart_mem P.openSheafAdjunction
      (fun G ↦ P.lower_bound 0 G.obj G.property.2) ∧
  HeartAdjunctionNormalization l Ω P.closedImage P.closedAdjunction
    P.closedRestriction.heart_mem P.closedSheafAdjunction
      (fun G ↦ P.closed_lower_bound 0 G.obj G.property.2) ∧
  (∀ F : Heart l Ω C,
    IsZero ((P.openRestriction.onHeart l Ω).obj F) →
    IsZero ((P.closedRestriction.onHeart l Ω).obj F) → IsZero F) ∧
  (PreservesFiniteLimits (P.closedImage.onHeart l Ω) ∧
    PreservesFiniteColimits (P.closedImage.onHeart l Ω)) ∧
  ((P.closedImage.onHeart l Ω).Full ∧ (P.closedImage.onHeart l Ω).Faithful) ∧
  IsIso P.closedSheafAdjunction.counit ∧
  (∀ F : Heart l Ω C,
    (P.closedImage.onHeart l Ω).essImage F ↔ IsZero ((P.openRestriction.onHeart l Ω).obj F)) ∧
  IsIso P.openSheafAdjunction.counit ∧
  (∀ (m : ℤ) (M : pbcQbarCategory l Ω U.scheme)
    (h : (lower l Ω U) m M),
    (P.openSheafAdjunction.homEquiv _ _).symm (P.bottom m M h).hom =
      (P.openRestriction.cohomologyIso m).inv.app (P.openImage.functor.obj M) ≫
        (cohomology l Ω U m).map (P.openAdjunction.counit.app M)) ∧
  (∀ (m : ℤ) (M N : pbcQbarCategory l Ω U.scheme)
    (hM : (lower l Ω U) m M) (hN : (lower l Ω U) m N) (f : M ⟶ N),
    (cohomology l Ω C m).map (P.openImage.functor.map f) ≫
        (P.bottom m N hN).hom =
      (P.bottom m M hM).hom ≫
        (P.openImage.onHeart l Ω).map ((cohomology l Ω U m).map f)) ∧
  (∀ (m : ℤ) (K : pbcQbarCategory l Ω C.scheme)
    (h : (lower l Ω U) m ((pull l Ω j).obj K)),
    (cohomology l Ω C m).map (P.openAdjunction.unit.app K) ≫
      (P.bottom m ((pull l Ω j).obj K) h).hom ≫
      (P.openImage.onHeart l Ω).map ((P.openRestriction.cohomologyIso m).hom.app K) =
        P.openSheafAdjunction.unit.app ((cohomology l Ω C m).obj K))

/-- The full open--closed cohomology assertion, including the unit at every integer m.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure OpenClosed {C U Z : PerAdic.Base k}
    (j : U.scheme ⟶ C.scheme) (i : Z.scheme ⟶ C.scheme) where
  core : OpenClosedCore l Ω j i
  assertions : OpenClosedAssertions l Ω core

/-- The original `openRestriction` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.openRestriction {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.openRestriction

/-- The original `closedRestriction` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.closedRestriction {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.closedRestriction

/-- The original `openImage` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.openImage {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.openImage

/-- The original `closedImage` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.closedImage {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.closedImage

/-- The original `openAdjunction` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.openAdjunction {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.openAdjunction

/-- The original `closedAdjunction` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.closedAdjunction {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.closedAdjunction

/-- The original `openUnit` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.openUnit {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.openUnit

/-- The original `closedUnit` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.closedUnit {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.closedUnit

/-- The original `openSheafAdjunction` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.openSheafAdjunction {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.openSheafAdjunction

/-- The original `closedSheafAdjunction` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.closedSheafAdjunction {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.closedSheafAdjunction

/-- The original `bottom` of the selected open--closed operations.
Source: BS 6.8.15 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev OpenClosed.bottom {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme} (O : OpenClosed l Ω j i) :=
  O.core.bottom

/-- Reindexing commutes with the identity functor by its two unitors.
Source: blueprint Frobenius reindexing argument
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def identityExchange {A : Type uA} [Category.{vA} A] (α : A ⥤ A) : 𝟭 A ⋙ α ≅ α ⋙ 𝟭 A :=
  Functor.leftUnitor α ≪≫ (Functor.rightUnitor α).symm

/-- A comparison map commutes with reindexing by the displayed square. This is the
morphism condition in the existing category of endofunctor-fixed pairs.
Source: Weil II 1.1.7--1.1.8, blueprint Weil-pair convention
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def Commutes {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (α : A ⥤ A) (β : B ⥤ B) {F G : A ⥤ B} (η : F ⟶ G)
    (eF : F ⋙ β ≅ α ⋙ F) (eG : G ⋙ β ≅ α ⋙ G) : Prop :=
  Functor.whiskerRight η β ≫ eG.hom = eF.hom ≫ Functor.whiskerLeft α η

/-- The actual natural transformation on the recorded endofunctor-fixed pair categories.
Its underlying map is eta; `mapOfNatIsoHom` supplies exactly the Frobenius morphism
condition. This uses the same IsoAlgebra interface as sfWeilComplex, without any
triangulated structure on fixed pairs.
Source: Weil II 1.1.7--1.1.8; blueprint Weil-pair convention
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def pairTransformation {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (α : A ⥤ A) (β : B ⥤ B) {F G : A ⥤ B} (η : F ⟶ G)
    (eF : F ⋙ β ≅ α ⋙ F) (eG : G ⋙ β ≅ α ⋙ G) (h : Commutes α β η eF eG) :
    Endofunctor.IsoAlgebra.mapOfNatIso eF ⟶ Endofunctor.IsoAlgebra.mapOfNatIso eG :=
  Endofunctor.IsoAlgebra.mapOfNatIsoHom η h

/-- The direct-image reindexing comparison is the descent of the canonical ambient
ringed exchange, specified on each integral representative, rather than an arbitrary
isomorphism. The mate fixes the corresponding pullback comparison through the unit
and counit equations below.
Source: BS 6.8.15; blueprint explicit sectionwise Frobenius comparison
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def ExchangeNormalization {X Y : PerAdic.Base k} {f : X.scheme ⟶ Y.scheme}
    (R : DirectImage l Ω f) (gX : Aut X.scheme) (gY : Aut Y.scheme)
    (sq : ChosenCartesianSquare gX.hom f f gY.hom)
    (e : R.functor ⋙ pull l Ω gY.hom ≅ pull l Ω gX.hom ⋙ R.functor) : Prop :=
  ∃ τ : StageSystem.Morphism.Hom
      (R.family.comp (PerAdic.pullFamily l Ω gY.hom))
      ((PerAdic.pullFamily l Ω gX.hom).comp R.family),
    HEq e.hom ((StageSystem.Morphism.functorCompIso R.family
      (PerAdic.pullFamily l Ω gY.hom)).inv ≫ StageSystem.Morphism.descNatTrans τ ≫
        (StageSystem.Morphism.functorCompIso (PerAdic.pullFamily l Ω gX.hom) R.family).hom) ∧
    ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X.scheme E),
      HEq ((τ.τ E).app ((pbcStageLocalization l Ω X.scheme E).obj K))
        ((pbcStageLocalization l Ω Y.scheme E).map
          (ObjectProperty.homMk
            (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
              (pbcActualCompletedPull gY.hom (pbcStageDatum.{u} l Ω E))
              (PerAdic.integralPull_mem l (pbcFiniteField.{u} l Ω E) gY.hom)).obj
                ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (R.preserves E)).obj K))
            (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
              (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (R.preserves E)).obj
                ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualCompletedPull gX.hom (pbcStageDatum.{u} l Ω E))
                  (PerAdic.integralPull_mem l (pbcFiniteField.{u} l Ω E) gX.hom)).obj K))
            ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app K.obj)))

/-- All ordinary and derived units and counits intertwine the same reindexing maps.
Source: Weil II 1.1.7--1.1.8; blueprint Frobenius square calculation
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
def AdjunctionCommutes {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (α : A ⥤ A) (β : B ⥤ B) {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (eF : F ⋙ β ≅ α ⋙ F) (eG : G ⋙ α ≅ β ⋙ G) : Prop :=
  Commutes α α adj.unit (identityExchange α) (composeExchange eF eG) ∧
    Commutes β β adj.counit (composeExchange eG eF) (identityExchange β)

/-- A restriction/direct-image adjunction and its bottom comparison commute with an
isomorphism square. In particular this applies to the actual geometric Frobenius square.
The truncation maps commute by the unit/counit equations in each `Restriction`.
Source: Weil II 1.1.7--1.1.8; BS 6.8.15; blueprint Steps 1 and 3
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
structure AutomorphismCompatibility {C U Z : PerAdic.Base k}
    {j : U.scheme ⟶ C.scheme} {i : Z.scheme ⟶ C.scheme}
    (O : OpenClosed l Ω j i) (R : ContinuousRealization l Ω C)
    (H : R.Cohomology l Ω) (gC : Aut C.scheme) (gU : Aut U.scheme) (gZ : Aut Z.scheme)
    (sqj : ChosenCartesianSquare gU.hom j j gC.hom)
    (sqi : ChosenCartesianSquare gZ.hom i i gC.hom) where
  curve : Restriction l Ω gC.hom
  continuousCohomology : ∀ (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ),
    Nonempty (ContinuousCohomologyFrobenius l Ω R H E n gC)
  openPart : Restriction l Ω gU.hom
  closedPart : Restriction l Ω gZ.hom
  openPull : pull l Ω j ⋙ pull l Ω gU.hom ≅ pull l Ω gC.hom ⋙ pull l Ω j
  closedPull : pull l Ω i ⋙ pull l Ω gZ.hom ≅ pull l Ω gC.hom ⋙ pull l Ω i
  openPush : O.openImage.functor ⋙ pull l Ω gC.hom ≅ pull l Ω gU.hom ⋙ O.openImage.functor
  closedPush : O.closedImage.functor ⋙ pull l Ω gC.hom ≅
    pull l Ω gZ.hom ⋙ O.closedImage.functor
  openPush_normalized : ExchangeNormalization l Ω O.openImage gU gC sqj openPush
  closedPush_normalized : ExchangeNormalization l Ω O.closedImage gZ gC sqi closedPush
  openSheafPull : O.openRestriction.onHeart l Ω ⋙ openPart.onHeart l Ω ≅
    curve.onHeart l Ω ⋙ O.openRestriction.onHeart l Ω
  closedSheafPull : O.closedRestriction.onHeart l Ω ⋙ closedPart.onHeart l Ω ≅
    curve.onHeart l Ω ⋙ O.closedRestriction.onHeart l Ω
  openSheafPush : O.openImage.onHeart l Ω ⋙ curve.onHeart l Ω ≅
    openPart.onHeart l Ω ⋙ O.openImage.onHeart l Ω
  closedSheafPush : O.closedImage.onHeart l Ω ⋙ curve.onHeart l Ω ≅
    closedPart.onHeart l Ω ⋙ O.closedImage.onHeart l Ω
  openAdjunction : AdjunctionCommutes (pull l Ω gC.hom) (pull l Ω gU.hom)
    O.openAdjunction openPull openPush
  closedAdjunction : AdjunctionCommutes (pull l Ω gC.hom) (pull l Ω gZ.hom)
    O.closedAdjunction closedPull closedPush
  openSheafAdjunction : AdjunctionCommutes (curve.onHeart l Ω) (openPart.onHeart l Ω)
    O.openSheafAdjunction openSheafPull openSheafPush
  closedSheafAdjunction : AdjunctionCommutes (curve.onHeart l Ω) (closedPart.onHeart l Ω)
    O.closedSheafAdjunction closedSheafPull closedSheafPush
  openCohomology : ∀ m : ℤ,
    Commutes (pull l Ω gC.hom) (openPart.onHeart l Ω)
      (O.openRestriction.cohomologyIso m).hom
      (composeExchange openPull (openPart.cohomologyIso m).symm)
      (composeExchange (curve.cohomologyIso m).symm openSheafPull)
  closedCohomology : ∀ m : ℤ,
    Commutes (pull l Ω gC.hom) (closedPart.onHeart l Ω)
      (O.closedRestriction.cohomologyIso m).hom
      (composeExchange closedPull (closedPart.cohomologyIso m).symm)
      (composeExchange (curve.cohomologyIso m).symm closedSheafPull)
  bottom : ∀ (m : ℤ) (M : pbcQbarCategory l Ω U.scheme)
    (h : (lower l Ω U) m M),
    (curve.onHeart l Ω).map (O.bottom l Ω m M h).hom ≫
        openSheafPush.hom.app ((cohomology l Ω U m).obj M) ≫
        (O.openImage.onHeart l Ω).map ((openPart.cohomologyIso m).inv.app M) =
      (curve.cohomologyIso m).inv.app (O.openImage.functor.obj M) ≫
        (cohomology l Ω C m).map (openPush.hom.app M) ≫
        (O.bottom l Ω m ((pull l Ω gU.hom).obj M) ((openPart.t_exact m M).2 h)).hom

/-- Standard constructible cohomology and open--closed restriction for a smooth curve.
The automorphism clause applies to geometric Frobenius by the recorded Cartesian-square
lemma; `Commutes` is the actual morphism equation of the recorded Frobenius-pair category.
No triangulated structure is put on that category.

Source: Bhatt--Scholze Sections 6.7--6.8; blueprint thm-a1-curve-perverse-heart,
Steps 1 and 3 (blueprint: lem-a1-qbar-open-closed-cohomology).

Proof plan (the DAG proof, with its cited dependencies):
1. Work first over a finite coefficient field $E$. Every locally closed $T$ under consideration
is noetherian and finite-dimensional, with $\ell$ invertible. Apply
[lem-per-continuous-rational-derived-realization]: the raw category is equivalent, by $J_T$, to
the full ambient derived category of bounded complexes with constructible continuous
$E_T$-module cohomology, and its localized standard t-structure is the restriction of the
ambient one. Thus its heart is precisely the constructible $E_T$-module sheaves, not an
unspecified rational heart. The bounded t-structure and common-stage truncations at $\Lambda$
are supplied by [lem-per-adic-heart-pullback-fibres] (take its morphism to be $\mathrm{id}_T$).
The realization comparison commutes with finite coefficient extension, so its cohomology is
ordinary pro-etale module cohomology at each representative field. For a scheme isomorphism, the
same realization identifies pullback with exact ordinary inverse image. Exact inverse image
preserves the two cohomological bounds, and hence commutes with the truncations and their
canonical maps by their adjunction characterizations. This proves the first paragraph, including
invariance under isomorphisms. Dependencies: lem-per-continuous-rational-derived-realization,
lem-per-adic-heart-pullback-fibres.

2. For $f=j$ or $i$, use [lem-weil-pbc-integral-stratified-perfect-characterization] to identify
the full integral category used for PBC with the completed integral category in
[lem-sf-integral-direct-image-constructible]; its statement explicitly identifies both
categories and their reduction functors. The finiteness theorem applies over the given field
$k$, including characteristic zero: source and target are finite-type $k$-schemes and $\ell$ is
invertible. Their integral direct images are therefore bounded constructible. The canonical
comparison [lem-a1-rational-direct-image-realization] identifies the localized integral direct
image and its adjunction maps with ambient $Rf_*^E$ under $J$. Consequently ambient $Rj_*$ and
$Ri_*$ on these realizations are constructible and are the intended rational operations. In
particular the computation below takes place in an actual derived category of continuous
$E_T$-modules. Dependencies: lem-weil-pbc-integral-stratified-perfect-characterization,
lem-sf-integral-direct-image-constructible, lem-a1-rational-direct-image-realization.

3. For each locally closed immersion $a$, [lem-per-continuous-rational-derived-realization]
gives $a^{-1}E_T\cong E_S$ and identifies the completed rational pullback with exact ordinary
inverse image of module sheaves. In particular $j^*$ and $i^*$ are t-exact and $\mathcal
H^r(a^*K)=a^*\mathcal H^rK$. They preserve constructibility by pulling back the finite lisse
stratification. For joint detection one can work intrinsically in these hearts:
[lem-per-adic-heart-pullback-fibres] states exactness and joint conservativity of their adic
geometric fibres and the formula $(a^*F)_{\bar s}=F_{a\bar s}$. Every geometric point of $C$
factors through either $U$ or $Z$; if both restrictions of $F$ vanish, every one of its fibres
vanishes, so $F=0$. No etale abelian-sheaf conservativity is being applied to an unrelated
heart. Dependencies: lem-per-continuous-rational-derived-realization,
lem-per-adic-heart-pullback-fibres.

4. Set the ring sheaf $A$ of [lem-weil-pbc-proetale-ringed-open-closed] equal to the continuous
ring $E_C$; the preceding step identifies its inverse images with $E_Z,E_U$. The open is
quasi-compact since $C$ is noetherian. That ringed statement gives exact $i_*$,
$i^*i_*\cong\mathrm{id}$, $j^*i_*=0$ and $0\to j_!j^*F\to F\to i_*i^*F\to0$. The module
adjunction [lem-weil-pbc-ringed-topoi-module-adjunction] and its invertible counit show full
faithfulness:
$\operatorname{Hom}(i_*G,i_*H)=\operatorname{Hom}(i^*i_*G,H)=\operatorname{Hom}(G,H)$. If
$j^*F=0$, the displayed sequence identifies $F$ with $i_*i^*F$; conversely $j^*i_*=0$. Direct
image is constructible here: extend a finite lisse stratification of $Z$ by the stratum $U$
carrying the zero sheaf. This proves the exactness, full faithfulness and essential-image
assertions on constructible sheaves. Dependencies: lem-weil-pbc-proetale-ringed-open-closed,
lem-weil-pbc-ringed-topoi-module-adjunction.

5. By [lem-weil-pbc-ringed-topoi-module-adjunction], ordinary module $j_*$ is right adjoint to
the exact restriction $j^*$. It is additive and left exact: a right adjoint preserves finite
limits, hence kernels. The site localization [lem-weil-proetale-weakly-etale-localization]
identifies restriction with evaluation on objects over $U$. By the direct-image definition
[def-weil-proetale-inverse-image], for an object $V\to U$, direct image followed by restriction
has value $F(V\times_CU)=F(V)$, since $V\to C$ already factors through the open monomorphism
$U$. These equalities are natural and identify the counit $j^*j_*F\to F$ with the identity. Thus
$j^*j_*\cong\mathrm{id}$ for continuous module sheaves. Constructibility of $j_*$ on lisse
sheaves follows in Step 7 from constructibility of $Rj_*$ and the bottom-degree formula.
Dependencies: lem-weil-pbc-ringed-topoi-module-adjunction,
lem-weil-proetale-weakly-etale-localization, def-weil-proetale-inverse-image.

6. Choose small sites in the fixed universe. Applied to the ring sheaves $E_U,E_C$,
[prop-pur-kinjective-resolutions-exist] gives Grothendieck abelian module categories and
K-injective resolutions. Under the realization in Step 1, a bounded constructible $M$ is an
object of their $D^+$, and Step 2 identifies the intended $Rj_*$ with the ambient right derived
functor of the left exact $j_*$. Therefore [lem-weil-pbc-derived-functor-negative-vanishing],
with $v=j_*$ and $b=m$, gives $\mathcal H^a(Rj_*M)=0$ for $a<m$. The hypothesis is the rational
ambient bound on $J_U(M)$; no lower bound on a chosen integral lattice is assumed. Dependencies:
prop-pur-kinjective-resolutions-exist, lem-weil-pbc-derived-functor-negative-vanishing.

7. Apply [lem-pc-derived-bottom-unit-normalization] to the abelian module categories above,
$S=j_*$ and $n=m$. Its natural isomorphism is $\mathcal H^m(Rj_*\tau^{\ge m}M)\cong j_*\mathcal
H^mM$. Since $M\in D^{\ge m}$, its lower-truncation projection $M\to\tau^{\ge m}M$ is an
isomorphism, giving $\mathcal H^m(Rj_*M)\cong j_*\mathcal H^mM$. For a lisse sheaf $L[0]$, take
$m=0$: $j_*L$ is $\mathcal H^0(Rj_*L)$, which is constructible by Step 2 and the ambient heart
comparison in Step 1. Hence the sheaf adjunction and the counit in Step 5 restrict to the
constructible hearts. Dependencies: lem-pc-derived-bottom-unit-normalization.

8. For the unit claim, represent $K$ by a bounded-below complex $P$ of $E_C$-modules.
Restriction is exact, so $j^*K$ is represented by $j^*P$. The normalization in
[lem-trf-bounded-below-derived-adjunction], with $L=j^*$ and $R=j_*$, identifies the actual
derived adjunction unit with $P\to j_*j^*P\to Rj_*j^*P$, the termwise ordinary unit followed by
the right-derived comparison. Apply the actual-unit formula of
[lem-pc-derived-bottom-unit-normalization] in degree $m$, to the cycles and homology data of
$j^*P$, and the induced map on cycles into $j_*j^*P$. It says that, after the lower-truncation
projection and its bottom isomorphism, the latter comparison induces the canonical map to
$j_*\mathcal H^m(j^*P)$. Composing with the termwise unit therefore gives precisely the ordinary
sheaf unit $\mathcal H^mK\to j_*j^*\mathcal H^mK$. Here exact restriction identifies $\mathcal
H^m(j^*P)=j^*\mathcal H^mP$, and $j^*K\in D^{\ge m}$ makes the lower-truncation projection
invertible. No lower bound on $K$ relative to $m$ is used. Dependencies:
lem-trf-bounded-below-derived-adjunction, lem-pc-derived-bottom-unit-normalization.

9. Now suppose the immersion pair descends to $k_0$. For $f=j,i$,
[lem-weil-frobenius-square-cartesian] gives isomorphisms $g_C,g_Y$ with $fg_Y=g_Cf$, where
$Y=U,Z$. The site equivalence in [lem-weil-proetale-isomorphism-inverse-image] computes $g^{-1}$
by reindexing. Using [def-weil-proetale-inverse-image] for direct image, for $V\to C$ compare
the $Y$-objects $V_g\times_CY$ and $V\times_CY$ with the latter structure map followed by $g_Y$,
where $V_g$ means $V\xrightarrow{v}C\xrightarrow{g_C}C$. They are isomorphic by
$(v,y)\mapsto(v,g_Yy)$. Evaluating a sheaf $F$ on this isomorphism gives a natural isomorphism
$b_f:g_C^*f_*F\xrightarrow{\sim}f_*g_Y^*F$. The coefficient actions agree because the continuous
coefficient pullback identifications are those of
[lem-per-continuous-rational-derived-realization]. The units and counits are
restriction/evaluation of sections; the displayed isomorphism preserves these maps. More
explicitly, after the square pullback identification, $b_{f,f^*H}\,g_C^*(\eta_H)=\eta_{g_C^*H}$
and $g_Y^*(\varepsilon_F)=\varepsilon_{g_Y^*F}\,f^*(b_{f,F})$. These are equalities on each
section, not an inference from t-exactness alone. Dependencies:
lem-weil-frobenius-square-cartesian, lem-weil-proetale-isomorphism-inverse-image,
lem-per-continuous-rational-derived-realization, def-weil-proetale-inverse-image.

10. The reindexing equivalences of Step 9 preserve K-injectives: maps from an acyclic complex
into the reindexed resolution are identified with maps from its exact inverse image into the
original K-injective complex, and hence are null-homotopic. Apply the sectionwise $b_f$ to an
injective resolution, using [prop-pur-kinjective-resolutions-exist]. This constructs
$g_C^*Rf_*\cong Rf_*g_Y^*$; for $i$ it is already $g_C^*i_*\cong i_*g_Z^*$ since $i_*$ is exact.
The unit/counit equations of Step 9 remain equalities of maps of complexes and hence in the
derived category, with the actual derived maps normalized by
[lem-trf-bounded-below-derived-adjunction]. The comparison
[lem-a1-rational-direct-image-realization] identifies these with the specified rational
operations and their adjunction maps. Since reindexing is exact, it commutes with kernels,
cokernels, truncations and their maps. The natural bottom comparison in
[lem-pc-derived-bottom-unit-normalization] is built from those truncations and the right-derived
comparison, so it commutes with the same reindexing. Given a Weil isomorphism $g_Y^*M\to M$, its
direct-image isomorphism is $Rf_*(g_Y^*M\to M)\circ b_f$; the displayed unit/counit equations
and cohomology comparison give precisely the required equivariance. Dependencies:
prop-pur-kinjective-resolutions-exist, lem-trf-bounded-below-derived-adjunction,
lem-a1-rational-direct-image-realization, lem-pc-derived-bottom-unit-normalization.

11. Finally pass from finite fields of coefficients to $\Lambda$. The scalar comparisons of
[prop-weil-pbc-scalar-extension], the realization comparisons of
[lem-per-continuous-rational-derived-realization] and [lem-a1-rational-direct-image-realization]
identify the preceding constructions after each finite extension. At the ambient rational stage
finite coefficient extension is exact: locally a basis of the finite field extension identifies
it with a finite direct sum, so it commutes with kernels, cokernels and ordinary direct image.
This also makes the sheaf units/counits and the section-reindexing maps scalar compatible. The
canonical derived and truncation comparisons have the same compatibility by the cited
comparisons and their adjunction normalization. Therefore [prop-weil-pbc-descent-functors]
descends the functors, units, counits and all displayed equations to the pair categories of
[def-weil-pbc-qbar-category]. Isomorphisms, the cohomological bounds and the t-exactness
assertions hold at common finite stages by [lem-per-adic-heart-pullback-fibres]. Exactness on
hearts follows from preservation of kernels and cokernels there; a sheaf with zero restrictions
is zero by their conservative fibres. This proves every clause at $\Lambda$, and equips the maps
with Frobenius when present. All constructions were in the geometric triangulated categories;
the Weil assertion uses only the given Frobenius pairs. Finally [sk-prop-sfb-qlbar-colimit-x]
identifies the continuous ring sheaf $\Lambda_T$ with $\varinjlim_E E_T$, with the same
completed/localized finite rings. A finite-stage representative is thus realized by
$\Lambda_T\otimes_{E_T}J_TK$. This extension is an exact filtered colimit of finite scalar
extensions, by the Grothendieck assertion of [prop-pur-kinjective-resolutions-exist]; its
cohomology is $\Lambda_T\otimes_{E_T}\mathcal H^r(J_TK)$, proving the claimed agreement also for
the pro-etale $\Lambda_T$-module representatives. Dependencies: prop-weil-pbc-scalar-extension,
lem-per-continuous-rational-derived-realization, lem-a1-rational-direct-image-realization,
prop-weil-pbc-descent-functors, def-weil-pbc-qbar-category, lem-per-adic-heart-pullback-fibres,
sk-prop-sfb-qlbar-colimit-x, prop-pur-kinjective-resolutions-exist.
-/
theorem qbar_open_closed_cohomology [PerfectField k] (C U Z : PerAdic.Base k)
    [Smooth (C.scheme ↘ Spec (.of k))] (hPure : C.scheme.IsPureDimension 1)
    (j : U.scheme ⟶ C.scheme) (i : Z.scheme ⟶ C.scheme)
    [IsOpenImmersion j] [IsClosedImmersion i] [IsReduced Z.scheme]
    [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    (dense : DenseRange j) (complement : Set.range i = (Set.range j)ᶜ) :
    ∃ (R : ContinuousRealization l Ω C) (H : R.Cohomology l Ω),
    StandardAssertions l Ω C ∧
    (∀ (T : PerAdic.Base k) (a : T.scheme ⟶ C.scheme), IsImmersion a →
      StandardAssertions l Ω T ∧
        ∃ R : ContinuousRealization l Ω T, Nonempty (R.Cohomology l Ω)) ∧
    (∀ (T S : PerAdic.Base k) (a : T.scheme ⟶ C.scheme) (g : S.scheme ⟶ T.scheme),
      IsImmersion a → IsIso g → Nonempty (Restriction l Ω g)) ∧
    ∃ O : OpenClosed l Ω j i,
      ∀ (gC : Aut C.scheme) (gU : Aut U.scheme) (gZ : Aut Z.scheme)
        (sqj : ChosenCartesianSquare gU.hom j j gC.hom)
        (sqi : ChosenCartesianSquare gZ.hom i i gC.hom),
        Nonempty (AutomorphismCompatibility l Ω O R H gC gU gZ sqj sqi) := by
  sorry

end AlgebraicGeometry.Scheme.A1Cohomology
