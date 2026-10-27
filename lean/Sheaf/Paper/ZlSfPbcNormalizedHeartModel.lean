/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.WholeTowerIntegralPullbackComparison
public import Sheaf.Paper.IntegralPullbackShiftCoordinates
public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.PbcQbarStandardCohomology
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CompletedCoefficientPresentationTransport
import Sheaf.Paper.ConstructibleTruncations
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Normalized sf/PBC hearts and finite continuous models

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
current blueprint, thm-zl-real-mixed-by-curves, constructible-to-lisse paragraph
(blueprint: lem-zl-sf-pbc-normalized-heart-model).

The coefficient equivalences and continuous realizations are inputs with their existing
normalizations. The new comparison data extend the recorded isomorphism-only interface
to arbitrary scheme morphisms. The theorem asserts all clauses simultaneously.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- A separated finite-type scheme over the fixed geometric field, including the empty scheme.
Source: BS 6.8.14, geometric specialization
(blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
structure ZlHeartBase (D : FiniteFieldDatum.{u}) where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of D.k)
  [finiteType : LocallyOfFiniteType structureMap]
  [quasiCompact : QuasiCompact structureMap]
  [separated : IsSeparated structureMap]

attribute [instance] ZlHeartBase.finiteType ZlHeartBase.quasiCompact ZlHeartBase.separated

/-- The geometric bounds are conclusions, not extra assumptions on finite-type schemes.
Source: BS 6.8.14; Stacks 01T6
(blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
class ZlHeartBounds (D : FiniteFieldDatum.{u}) : Prop where
  noetherian : ∀ X : ZlHeartBase D, IsNoetherian X.scheme
  dimension : ∀ X : ZlHeartBase D, ∃ n : ℕ, topologicalKrullDim X.scheme ≤ n

/-- Stalk invertibility, asserted as a conclusion under the prime-to-characteristic hypothesis.
Source: BS 6.8.14 (blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
class ZlHeartPrimeUnits (D : FiniteFieldDatum.{u}) (l : ℕ) : Prop where
  invertible : ∀ (X : ZlHeartBase D) (x : X.scheme), IsUnit (l : X.scheme.presheaf.stalk x)

/-- Use the asserted Noetherian conclusion in the recorded coefficient interfaces.
Source: Stacks 01T6 (blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
instance zlHeartNoetherian (D : FiniteFieldDatum.{u}) [B : ZlHeartBounds D]
    (X : ZlHeartBase D) : IsNoetherian X.scheme := B.noetherian X

/-- Use the asserted finite dimension, without excluding dimension minus infinity.
Source: finite-type dimension lemma (blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
instance zlHeartDimension (D : FiniteFieldDatum.{u}) [B : ZlHeartBounds D]
    (X : ZlHeartBase D) : Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) :=
  ⟨B.dimension X⟩

/-- Use the asserted stalk invertibility in completed pullback.
Source: prime-to-characteristic convention (blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
instance zlHeartInvertible (D : FiniteFieldDatum.{u}) (l : ℕ) [B : ZlHeartPrimeUnits D l]
    (X : ZlHeartBase D) : Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x)) :=
  ⟨B.invertible X⟩

/-- The same scheme with exactly the geometric hypotheses required by continuous realization.
Source: BS 6.8.14 (blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
def zlHeartContinuousBase (D : FiniteFieldDatum.{u}) (l : ℕ) [B : ZlHeartBounds D] [I :
  ZlHeartPrimeUnits D l]
    (X : ZlHeartBase D) : ContinuousRational.Base.{u} l :=
  { scheme := X.scheme
    dimension := B.dimension X
    prime_unit := I.invertible X }

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Integral and rational comparison for an arbitrary scheme morphism. The ambient
normalization uses the existing whole strict tower chain with its actual quotient maps.
Its inverse is the displayed J Lh* to Lh* J comparison in the node.
Source: BS 6.8.15; Stacks 099N
(blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
structure ZlFinitePullbackComparison {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
    (h : U ⟶ T) (E : Padic.FiniteCoefficientFields l Ω) where
  chain : FdPullbackChain l Ω E h
  integral : (CT.stage E).integral.functor ⋙ fdPbcIntegralPull l Ω h E ≅
    constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h ⋙
      (CU.stage E).integral.functor
  ambient : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
        pbcActualCompletedPull h (pbcStageDatum.{u} l Ω E) ≅
    constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h ⋙
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) U).ι ⋙
        integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)
  lift : ∀ K, HEq (integral.hom.app K).hom (ambient.hom.app K)
  normalization : ∀ (P : (integralOperationsGoodComplex l
      (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((pbcActualCompletedPullUnit h (pbcStageDatum.{u} l Ω E)).app
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj
          (DerivedCategory.Q.obj P.obj)) ≫
      ambient.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).map
        ((integralDerivedPullbackComparison l (pbcFiniteField.{u} l Ω E) h).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) U).hom.app
        ((integralOperationsPullbackComplexFunctor l
          (pbcFiniteField.{u} l Ω E) h).obj P.obj))
      ((pbcActualDerivedPull h (pbcStageDatum.{u} l Ω E)).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcActualPullComplexCounit h (pbcStageDatum.{u} l Ω E)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map (chain.map.app P.obj))
  rational : (CT.stage E).rational.functor ⋙ (pbcQbarPullFamily l Ω h).Φ E ≅
    rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) h ⋙
      (CU.stage E).rational.functor
  rationalization : ∀ K,
    HEq (rational.hom.app
      ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K))
      ((pbcStageLocalization l Ω U E).map (integral.hom.app K))


/-- The same comparison on actual common-stage arrows. The mixed transformation
records the scalar square, and pair_components fixes the descended comparison on each stage.
Source: BS 6.8.14--6.8.15
(blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
structure ZlPullbackSystem {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
    (h : U ⟶ T) where
  finite : ∀ E, ZlFinitePullbackComparison l Ω CU CT h E
  sfFamily : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω U)
  sfFinite : ∀ E, HEq (sfFamily.Φ E)
    (rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) h)
  sfBeta : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (e : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((sfFamily.β e).hom.app K)
      (commonStagePullbackComparison l Ω h ⟨E, K⟩ L e).hom
  sfPair : sfFamily.functor = commonStageDerivedPullback l Ω h
  mixed : StageSystem.Morphism.Hom
    (CT.family.comp (pbcQbarPullFamily l Ω h)) (sfFamily.comp CU.family)
  mixed_components : ∀ E, HEq (mixed.τ E) (finite E).rational.hom
  pair : CT.equivalence.functor ⋙ pbcQbarCompletedPull l Ω h ≅
    commonStageDerivedPullback l Ω h ⋙ CU.equivalence.functor
  pair_components : ∀ P
    (K : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω P.stage) T),
    HEq P.obj K → HEq (pair.hom.app P)
      (((pbcScalarSystem l Ω U Fact.out Fact.out).ι P.stage).map
        ((finite P.stage).rational.hom.app K))


/-- Identity, composition, scalar and shift normalization for one arbitrary-morphism
comparison family, using the fixed whole-diagram realization system of S.
Source: Stacks 099N and BS 6.8.15
(blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
structure ZlWholePullbackComparison (D : FiniteFieldDatum.{u}) [ZlHeartBounds D]
  [ZlHeartPrimeUnits D l]
    (S : FdCoefficientComparisonSystem.{u} l Ω) where
  /-- The inverse b, its ambient lift, actual unit-section chain map, and raw localization.
  The mixed field is the rational scalar square with the specified inverse chi maps. -/
  pullback : ∀ {U T : ZlHeartBase D}
    (h : U.scheme ⟶ T.scheme), ZlPullbackSystem l Ω (S.coefficients U.scheme) (S.coefficients
      T.scheme) h
  /-- Identity compatibility with the specified whole-system and actual PBC units. -/
  unit : ∀ (T : ZlHeartBase D)
    (E : Padic.FiniteCoefficientFields l Ω),
    ∃ su : constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) (𝟙 T.scheme) ≅ 𝟭 _,
    ∃ pu : fdPbcIntegralPull l Ω (𝟙 T.scheme) E ≅ 𝟭 _,
      (∀ K, (su.hom.app K).hom =
        (integralComparisonUnit l (pbcFiniteField.{u} l Ω E) S.realization T.scheme K).hom) ∧
      (∀ K, HEq (pu.hom.app K).hom
        ((pbcActualCompletedPullIdIso (pbcStageDatum.{u} l Ω E) T.scheme).hom.app
          ⟨K.obj, K.property.1⟩)) ∧
      (∀ K, ((pullback (U := T) (T := T) (𝟙 T.scheme)).finite E).integral.hom.app K ≫
          ((S.coefficients T.scheme).stage E).integral.functor.map (su.hom.app K) =
        pu.hom.app (((S.coefficients T.scheme).stage E).integral.functor.obj K))
  /-- Composition compatibility, with both compositors fixed independently of b. -/
  composition : ∀ (U V T : ZlHeartBase D)
    (h : U.scheme ⟶ V.scheme) (k : V.scheme ⟶ T.scheme) (E : Padic.FiniteCoefficientFields l Ω),
    ∃ sc : constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) (h ≫ k) ≅
        constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) k ⋙
          constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h,
    ∃ pc : fdPbcIntegralPull l Ω (h ≫ k) E ≅
        fdPbcIntegralPull l Ω k E ⋙ fdPbcIntegralPull l Ω h E,
      (∀ K, (sc.hom.app K).hom =
        (integralComparisonComposition l (pbcFiniteField.{u} l Ω E) S.realization
          h k K).hom) ∧
      (∀ K, HEq (pc.hom.app K).hom
        ((pbcActualCompletedPullCompIso h k
          (pbcStageDatum.{u} l Ω E)).inv.app ⟨K.obj, K.property.1⟩)) ∧
      (∀ K, ((pullback (U := U) (T := T) (h ≫ k)).finite E).integral.hom.app K ≫
          ((S.coefficients U.scheme).stage E).integral.functor.map (sc.hom.app K) =
        pc.hom.app (((S.coefficients T.scheme).stage E).integral.functor.obj K) ≫
          (fdPbcIntegralPull l Ω h E).map
            (((pullback (U := V) (T := T) k).finite E).integral.hom.app K) ≫
          ((pullback (U := U) (T := V) h).finite E).integral.hom.app
            ((constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) k).obj K))
  /-- The scalar alpha is precisely lambda followed by mu inverse, retaining chi. -/
  scalar_realization : ∀ {U T : ZlHeartBase D}
    (h : U.scheme ⟶ T.scheme) (E L : Padic.FiniteCoefficientFields l Ω) (e : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T.scheme),
    (integralPullbackScalarComparison l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h K).hom.hom =
      (integralComparisonScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω e) S.realization h K).hom
  /-- The integral mixed square, in the inverse-b orientation. The coefficient datum's
  chi field fixes both scalar identifications by the actual completion chain map. -/
  integral_scalar : ∀ {U T : ZlHeartBase D}
    (h : U.scheme ⟶ T.scheme) (E L : Padic.FiniteCoefficientFields l Ω) (e : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T.scheme),
    ∃ alpha : pbcAmbientScalarExtension l Ω T.scheme e ⋙
        pbcActualCompletedPull h (pbcStageDatum.{u} l Ω L) ≅
      pbcActualCompletedPull h (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω U.scheme e,
    HEq alpha.hom
      (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h).hom ∧
    HEq
      ((pbcAmbientScalarExtension l Ω U.scheme e).map
          (((pullback (U := U) (T := T) h).finite E).ambient.hom.app K) ≫
        ((S.coefficients U.scheme).integral_scalar e).hom.app
          ((constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h).obj K) ≫
        (integralDetailedTransport U.scheme l (pbcFiniteField.{u} l Ω L)).map
          (integralPullbackScalarComparison l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h K).hom.hom)
      (alpha.inv.app
          ((integralDetailedTransport T.scheme l (pbcFiniteField.{u} l Ω E)).obj K.obj) ≫
        (pbcActualCompletedPull h (pbcStageDatum.{u} l Ω L)).map
          (((S.coefficients T.scheme).integral_scalar e).hom.app K) ≫
        ((pullback (U := U) (T := T) h).finite L).ambient.hom.app
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) T.scheme).obj K))
  /-- The shift is the signed cone shift, descended through the specified representative
  comparison; the same ambient comparison commutes with it for every integer. -/
  shifts : ∀ {U T : ZlHeartBase D}
    (h : U.scheme ⟶ T.scheme) (E : Padic.FiniteCoefficientFields l Ω),
    ∃ c : (integralOperationsPullbackComplexFunctor l
      (pbcFiniteField.{u} l Ω E) h).CommShift ℤ,
    ∃ d : (integralDerivedPullback l (pbcFiniteField.{u} l Ω E) h).CommShift ℤ,
      IntegralCompletedComparison.ShiftCoordinates l (pbcFiniteField.{u} l Ω E) h c ∧
      IntegralCompletedComparison.ShiftDescent l (pbcFiniteField.{u} l Ω E) h c d ∧
      (fun [_sd : (integralDerivedPullback l
          (pbcFiniteField.{u} l Ω E) h).CommShift ℤ] ↦
        ∀ (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T.scheme) (r : ℤ),
        ∃ hKr : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T.scheme (K.obj⟦r⟧),
        HEq
          (((pullback (U := U) (T := T) h).finite E).ambient.hom.app ⟨K.obj⟦r⟧, hKr⟩ ≫
            ((integralDerivedPullback l (pbcFiniteField.{u} l Ω E) h ⋙
              integralDetailedTransport U.scheme l (pbcFiniteField.{u} l Ω E)).commShiftIso
                r).hom.app K.obj)
          (((integralDetailedTransport T.scheme l (pbcFiniteField.{u} l Ω E) ⋙
              pbcActualCompletedPull h (pbcStageDatum.{u} l Ω E)).commShiftIso
                r).hom.app K.obj ≫
            (((pullback (U := U) (T := T) h).finite E).ambient.hom.app K)⟦r⟧')) (_sd := d)

/-- All half-identifications, finite heart models and normalized pullback restrictions
for the fixed identity-induced coefficient system and continuous realization family.
Source: BS 6.8.14(2), 6.8.15, and the blueprint's constructible-to-lisse paragraph
(blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
structure ZlHeartComparison (D : FiniteFieldDatum.{u}) [ZlHeartBounds D] [ZlHeartPrimeUnits
  D l]
    (S : FdCoefficientComparisonSystem.{u} l Ω) (R : ContinuousRational.Family.{u} l) where
  /-- The integral comparison uses the same ambient cohomology after coefficient relabeling. -/
  cohomology : ∀ (X : ZlHeartBase D) (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) X.scheme) (r : ℤ),
    Nonempty (((DerivedCategory.homologyFunctor _ r).obj
      (((S.coefficients X.scheme).stage E).integral.functor.obj K).obj) ≅
      (fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) X.scheme).obj
        ((DerivedCategory.homologyFunctor
          (scalarReductionSource.{u, u} l (pbcFiniteField.{u} l Ω E) X.scheme) r).obj K.obj))
  /-- Both integral halves test the same ambient vanishing, in every degree. -/
  integral_halves : ∀ (X : ZlHeartBase D) (E : Padic.FiniteCoefficientFields l Ω)
    (b : Bool) (n : ℤ)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) X.scheme),
    sfIntegralStandardClass l (pbcFiniteField.{u} l Ω E) X.scheme b n K ↔
      (if b then (pbcIntegralTStructure X.scheme l (pbcFiniteField.{u} l Ω E)).le n
        else (pbcIntegralTStructure X.scheme l (pbcFiniteField.{u} l Ω E)).ge n)
          (((S.coefficients X.scheme).stage E).integral.functor.obj K)
  /-- Rational halves are the same isomorphism closures of integral halves. -/
  rational_halves : ∀ (X : ZlHeartBase D) (E : Padic.FiniteCoefficientFields l Ω)
    (b : Bool) (n : ℤ)
    (K : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) X.scheme),
    sfRationalStandardClass l (pbcFiniteField.{u} l Ω E) X.scheme b n K ↔
      ∃ L : pbcIntegralStage l Ω X.scheme E,
        (if b then (pbcIntegralTStructure X.scheme l (pbcFiniteField.{u} l Ω E)).le n L
          else (pbcIntegralTStructure X.scheme l (pbcFiniteField.{u} l Ω E)).ge n L) ∧
        Nonempty ((((S.coefficients X.scheme).stage E).rational.functor.obj K) ≅
          (pbcStageLocalization l Ω X.scheme E).obj L)
  /-- Common-stage halves agree, without assuming that an individual inclusion reflects them. -/
  common_halves : ∀ (X : ZlHeartBase D) (b : Bool) (n : ℤ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme),
    sfCommonStageStandardClass l X.scheme Ω b n K ↔
      pbcQbarStandardClass l Ω X.scheme b n
        ((S.coefficients X.scheme).equivalence.functor.obj K)
  /-- One finite stage witnesses both heart halves, with an actual continuous sheaf in degree zero.
  A finite locally closed partition witnesses constructibility, with no fixed rank. -/
  finite_heart : ∀ (X : ZlHeartBase D) (M : sfCommonStageHeart l X.scheme Ω),
    ∃ (E : Padic.FiniteCoefficientFields l Ω)
      (M_E : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X.scheme E),
      sfRationalHeartProperty l (pbcFiniteField.{u} l Ω E) X.scheme M_E ∧
      Nonempty ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := X.scheme) E).obj M_E ≅ M.obj) ∧
      ∃ F : pbcModules X.scheme
        (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)),
        (∃ s : FiniteLocallyClosedStratification X.scheme, ∀ i : Fin s.n,
          ((proEtaleModuleInverseImage (s.immersion i)
            (rationalCoefficientSheaf l X.scheme
              (pbcFiniteField.{u} l Ω E))).obj F).IsFiniteLocallyFree) ∧
        Nonempty (((R.realization (pbcFiniteField.{u} l Ω E)
          (zlHeartContinuousBase D l X)).J.obj
            (((S.coefficients X.scheme).stage E).rational.functor.obj M_E)) ≅
          (DerivedCategory.singleFunctor _ 0).obj F)
/-- Realization of the fixed arbitrary-morphism comparison, with exact immersion pullback.
Source: BS 6.8.15 (blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
structure ZlContinuousComparison (D : FiniteFieldDatum.{u}) [ZlHeartBounds D]
    [ZlHeartPrimeUnits D l] (S : FdCoefficientComparisonSystem.{u} l Ω)
    (R : ContinuousRational.Family.{u} l) (whole : ZlWholePullbackComparison l Ω D S) where
  /-- Under realization the comparison is ordinary derived module inverse image. -/
  continuous : ∀ {U T : ZlHeartBase D} (h : U.scheme ⟶ T.scheme)
    (E : Padic.FiniteCoefficientFields l Ω),
    ∃ q : (pbcQbarPullFamily l Ω h).Φ E ≅
        (R.along (pbcFiniteField.{u} l Ω E)
          (X := zlHeartContinuousBase D l U) (Y := zlHeartContinuousBase D l T) h).raw
            l (pbcFiniteField.{u} l Ω E),
      ∃ e : ∀ K, ((pbcQbarPullFamily l Ω h).Φ E).obj K =
          ((R.along (pbcFiniteField.{u} l Ω E)
            (X := zlHeartContinuousBase D l U) (Y := zlHeartContinuousBase D l T) h).raw
              l (pbcFiniteField.{u} l Ω E)).obj K,
      ∀ K, q.hom.app K = eqToHom (e K)
  /-- Realization uses the same completed pullback unit, including length-zero restriction. -/
  identity : ∀ (T : ZlHeartBase D) (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcStageCategory l Ω T.scheme E),
    HEq ((R.identity (pbcFiniteField.{u} l Ω E)
      (zlHeartContinuousBase D l T)).raw.hom.app K)
      ((pbcStageLocalization l Ω T.scheme E).map
        (((whole.unit T E).choose_spec.choose).hom.app K.obj))
  /-- The realized binary compositor is precisely the localized completed compositor.
  Together with identity this gives compatibility for every finite succession. -/
  composition : ∀ (U V T : ZlHeartBase D) (h : U.scheme ⟶ V.scheme)
    (k : V.scheme ⟶ T.scheme) (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcStageCategory l Ω T.scheme E),
    HEq ((R.composition (pbcFiniteField.{u} l Ω E)
      (X := zlHeartContinuousBase D l V) (Y := zlHeartContinuousBase D l T)
      (Z := zlHeartContinuousBase D l U) k h).raw.hom.app K)
      ((pbcStageLocalization l Ω U.scheme E).map
        (((whole.composition U V T h k E).choose_spec.choose).hom.app K.obj))
  /-- For a locally closed immersion, this is exact ordinary inverse image. -/
  immersion_exact : ∀ {U T : ZlHeartBase D} (h : U.scheme ⟶ T.scheme) [IsImmersion h]
    (E : Padic.FiniteCoefficientFields l Ω),
    IsIso (R.along (pbcFiniteField.{u} l Ω E)
      (X := zlHeartContinuousBase D l U) (Y := zlHeartContinuousBase D l T) h).coefficient ∧
    PreservesFiniteLimits (ContinuousRational.modulePull h
      (R := rationalCoefficientSheaf l T.scheme (pbcFiniteField.{u} l Ω E))
      (S := rationalCoefficientSheaf l U.scheme (pbcFiniteField.{u} l Ω E))
      (R.along (pbcFiniteField.{u} l Ω E)
        (X := zlHeartContinuousBase D l U) (Y := zlHeartContinuousBase D l T) h).coefficient) ∧
    PreservesFiniteColimits (ContinuousRational.modulePull h
      (R := rationalCoefficientSheaf l T.scheme (pbcFiniteField.{u} l Ω E))
      (S := rationalCoefficientSheaf l U.scheme (pbcFiniteField.{u} l Ω E))
      (R.along (pbcFiniteField.{u} l Ω E)
        (X := zlHeartContinuousBase D l U) (Y := zlHeartContinuousBase D l T) h).coefficient)

/-- The simultaneous normalized heart, tower and continuous comparison conclusions.
Source: BS 6.8.14--6.8.15 (blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
structure ZlNormalizedHeartModel (D : FiniteFieldDatum.{u}) [ZlHeartBounds D]
    [ZlHeartPrimeUnits D l] (S : FdCoefficientComparisonSystem.{u} l Ω)
    (R : ContinuousRational.Family.{u} l) where
  whole : ZlWholePullbackComparison l Ω D S
  heart : ZlHeartComparison l Ω D S R
  continuous : ZlContinuousComparison l Ω D S R whole

/-- The realized sf pullback comparison is the specified composite of the normalized
raw comparison, the identity adapter, and the existing continuous realization comparison.
Source: BS 6.8.15 (blueprint: lem-zl-sf-pbc-normalized-heart-model). -/
def zlContinuousPullbackComparison (D : FiniteFieldDatum.{u}) [ZlHeartBounds D]
    [ZlHeartPrimeUnits D l] (S : FdCoefficientComparisonSystem.{u} l Ω)
    (R : ContinuousRational.Family.{u} l) (A : ZlNormalizedHeartModel l Ω D S R)
    {U T : ZlHeartBase D} (h : U.scheme ⟶ T.scheme)
    (E : Padic.FiniteCoefficientFields l Ω) :=
  let sf := rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) h
  let jU := ((S.coefficients U.scheme).stage E).rational.functor
  let jT := ((S.coefficients T.scheme).stage E).rational.functor
  let rU := (R.realization (pbcFiniteField.{u} l Ω E) (zlHeartContinuousBase D l U)).J
  let pbc := (pbcQbarPullFamily l Ω h).Φ E
  let a := R.along (pbcFiniteField.{u} l Ω E)
    (X := zlHeartContinuousBase D l U) (Y := zlHeartContinuousBase D l T) h
  let q := (A.continuous.continuous (U := U) (T := T) h E).choose
  (Functor.associator sf jU rU).symm ≪≫
    Functor.isoWhiskerRight ((A.whole.pullback (U := U) (T := T) h).finite E).rational.symm rU ≪≫
    Functor.associator jT pbc rU ≪≫ Functor.isoWhiskerLeft jT (Functor.isoWhiskerRight q rU) ≪≫
    Functor.isoWhiskerLeft jT a.comparison

/-- The normalized sf/PBC heart comparison and its continuous finite-stage models.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; current blueprint,
thm-zl-real-mixed-by-curves, constructible-to-lisse paragraph
(blueprint: lem-zl-sf-pbc-normalized-heart-model).

Proof plan (the nine steps of this DAG node):
1. A field is Noetherian. Finite type over Spec k gives Noetherianity by
lem-weil-pbc-finite-type-over-noetherian and finite dimension by
lem-kun-dimension-finite-type. Since ell differs from p, it is a unit in k and in
all scheme stalks. This supplies ZlHeartBounds, also on the empty scheme.
2. Apply lem-weil-pbc-integral-stratified-perfect-characterization to the integral
identity specified by S. Its exact coefficient restriction identifies ambient
cohomology. The two integral half-definitions therefore agree in every degree.
3. Rational half-witnesses are integral objects and localized isomorphisms. The
identity-induced rational equivalences carry exactly these witnesses in both
directions. The same finite-stage witness argument identifies common-stage halves.
4. Choose nonpositive and nonnegative finite-stage representatives of a common-stage
heart object. Represent their isomorphism and inverse over one field, and their two
inverse identities over one further field, using the Hom-colimit equality rule of
def-weil-algebraically-closed-coefficients. Scalar extension preserves both halves
by prop-constructible-truncations. Their common representative is therefore in the
finite-stage heart; no reflection assertion for stage inclusions is used.
5. Apply lem-per-continuous-rational-derived-realization to its PBC image. Its heart
criterion gives F[0], and its strata criterion gives a finite locally closed
partition with finite locally free restrictions. Integral representatives may have
additional uniformizer-torsion cohomology; none is asserted to be in the integral heart.
6. Take a flat-term K-flat representative by lem-pc-kflat-resolution. Keep the
quotient maps in the entire strict tower. The coefficient presentation transport of
def-pur-completed-coefficient-presentation-transport identifies its two versions.
Clause (1) of lem-pur-framework-pbc-pullback-scalar-bridge realizes the identity of
that whole tower and preserves every projection, not just isolated reductions.
7. Localize this integral comparison on all fraction arrows. The bridge's clause
(2) gives the mixed square with the PBC scalar map in its corrected inverse direction.
Its clause (4) and lem-trf-integral-pullback-comparison-realization identify units,
compositors, shifts and successive coefficient associators. Conjugation by the fixed
j maps then descends the comparison to actual common-stage arrows; intermediate
maps cancel for composition and independence of enlargement.
8. The realization family R identifies PBC pullback with ordinary derived module
inverse image. For an immersion the coefficient map is an isomorphism and ordinary
inverse image is exact. Its identity, composition and mixed equations combine with
the previous normalization to give restriction compatibility. Binary composition
and the unit imply the same assertion for every finite succession, including length zero.
9. All functors preserve zero. The empty partition witnesses constructibility on
the empty scheme, where every module sheaf is zero by the empty covering condition.
No positive rank, nonempty stratum, k-linearity, or finite-reduction Tor bound is used. -/
theorem zlSfPbcNormalizedHeartModel (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (S : FdCoefficientComparisonSystem.{u} l Ω) (R : ContinuousRational.Family.{u} l) :
    ∃ (B : ZlHeartBounds D) (I : ZlHeartPrimeUnits D l),
      (fun [b : ZlHeartBounds D] [i : ZlHeartPrimeUnits D l] ↦
        Nonempty (ZlNormalizedHeartModel l Ω D S R)) (b := B) (i := I) := by
  sorry

end WeilConjectures
