/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportWitnessFamilies
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import Mathlib.Tactic.DefEqTransformations
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations

/-! # Coherence of the condensed compact-support projection

Source: latest blueprint, sec-six-functors/sk-prop-sf-pf-coherence, statement and
seven-step DAG proof (blueprint: sk-prop-sf-pf-coherence).

The ambient arrows are the published proper/open projection maps. Only the comparison
and composition clauses evaluate compactification comparisons on Loc(Dctf). The scalar
square uses the pasted comparison as a morphism, with no invertibility assumption.
Realization uses the normalized finite discrete encoding and bounded-below site comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace ProjectionCoherence

open CompactificationReindexing
open CompactSupportComposition

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The bounded constructible finite-Tor property in the ambient module-derived category.
The site smallness instance is the project-wide scalar-reduction instance.
Source: det-def-sf-operations, Dbc/Dctf domain convention
(blueprint: sk-prop-sf-pf-coherence). -/
def Dctf (T : Scheme.{u}) : ObjectProperty (D Λ T) := by
  letI : EssentiallySmall.{u + 1} T.ProEt :=
    WeilConjectures.scalarReductionSiteSmall.{u, u} T
  exact fun K ↦ constantModelBoundedConstructible Λ T K ∧
    _root_.DerivedCategory.finiteTorAmplitude.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) K

/-- Naturality in both inputs of the specified ambient projection.
Source: blueprint opening sentence and DAG proof step 1
(blueprint: sk-prop-sf-pf-coherence). -/
def Natural : Prop :=
  ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K K' : D Λ X} {L L' : D Λ Y} (a : K ⟶ K') (b : L ⟶ L'),
    ((F Λ c).map a ⊗ₘ b) ≫ pf Λ c K' L' =
      pf Λ c K L ≫ (F Λ c).map (a ⊗ₘ (P Λ f).map b)

/-- Identity normalization, through the canonical identity support and pullback comparisons.
Source: blueprint identity sentence and DAG proof step 1
(blueprint: sk-prop-sf-pf-coherence). -/
def Identity : Prop :=
  ∀ (X : Scheme.{u}) (K L : D Λ X),
    pf Λ (Compactification.ofIsProper (𝟙 X)) K L ≫
        (CompactSupportComposition.identity Λ X).hom.app (K ⊗ (P Λ (𝟙 X)).obj L) ≫
        (𝟙 K ⊗ₘ (leftDerivedUpperStarId Λ X).hom.app L) =
      (CompactSupportComposition.identity Λ X).hom.app K ⊗ₘ 𝟙 L

/-- Tensor associativity of projection, with the canonical pullback tensor comparison.
Source: blueprint associativity pentagon and DAG proof step 5
(blueprint: sk-prop-sf-pf-coherence). -/
def TensorAssociativity : Prop :=
  ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : D Λ X) (L M : D Λ Y),
    (pf Λ c K L ⊗ₘ 𝟙 M) ≫ pf Λ c (K ⊗ (P Λ f).obj L) M ≫
        (F Λ c).map ((α_ K ((P Λ f).obj L) ((P Λ f).obj M)).hom ≫
          (𝟙 K ⊗ₘ inv (((leftDerivedUpperStarTensor Λ f).app L).app M))) =
      (α_ ((F Λ c).obj K) L M).hom ≫ pf Λ c K (L ⊗ M)

/-- The canonical proper comparison, using the identity-open compactification.
Source: blueprint proper coincidence sentence and DAG proof step 4
(blueprint: sk-prop-sf-pf-coherence). -/
def properIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    F Λ (Compactification.ofIsProper f) ≅ R Λ f :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ X) (R Λ f) ≪≫
    Functor.leftUnitor _

/-- Proper coincidence identifies the actual projection arrows, not just invertibility.
Source: blueprint proper coincidence sentence and DAG proof step 4
(blueprint: sk-prop-sf-pf-coherence). -/
def Proper : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (K : D Λ X) (L : D Λ Y),
    pf Λ (Compactification.ofIsProper f) K L ≫
        (properIso Λ f).hom.app (K ⊗ (P Λ f).obj L) =
      ((properIso Λ f).hom.app K ⊗ₘ 𝟙 L) ≫ moduleObjectProjectionMap Λ f K L

/-- The Q76OpenExchangeFamily binder of Q76 sk-thm-sf-comp-composition, with k-morphisms.
Source: delivered Q76 9bbc212d94ba (blueprint: sk-prop-sf-pf-coherence). -/
def Q76OpenExchangeFamily (k : Type u) [Field k] :=
  ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left),
    D((c.i)_!open⟦Λ⟧) ⋙ moduleObjectDerivedPullback Λ (pullback.fst c.g v.hom.left) ≅
      moduleObjectDerivedPullback Λ a.hom.left ⋙ D(((c.ofIsPullback sq).i)_!open⟦Λ⟧)

/-- The Q76PullbackPreservationFamily binder of Q76 sk-thm-sf-comp-composition, with k-morphisms.
Source: delivered Q76 9bbc212d94ba (blueprint: sk-prop-sf-pf-coherence). -/
def Q76PullbackPreservationFamily (k : Type u) [Field k] :=
  ∀ (X Y : SepFinType k) (v : X ⟶ Y),
    (∀ K : D Λ Y.obj.left, localizingClosureProEtale Λ Y.obj.left K →
      localizingClosureProEtale Λ X.obj.left ((moduleObjectDerivedPullback Λ v.hom.left).obj K)) ∧
    (∀ K : D Λ Y.obj.left, Dctf Λ Y.obj.left K →
      Dctf Λ X.obj.left ((moduleObjectDerivedPullback Λ v.hom.left).obj K))

/-- The Q76ExchangeFamily binder of Q76 sk-thm-sf-comp-composition, with k-morphisms.
Source: delivered Q76 9bbc212d94ba (blueprint: sk-prop-sf-pf-coherence). -/
def Q76ExchangeFamily (k : Type u) [Field k] :=
  ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (_sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙ moduleObjectDerivedPullback Λ v.hom.left) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ a.hom.left ⋙ rightDerivedLowerShriekOfCompactification Λ d)

set_option maxHeartbeats 4000000 in
-- The twelve laws elaborate nested derived-functor comparison types.
/-- The exact Q76 compact-support comparison law conjunction.
Source: Q76 sk-thm-sf-comp-composition at 9bbc212d94ba, extracted verbatim
(blueprint: sk-prop-sf-pf-coherence). -/
def Q76ComparisonLaws (k : Type u) [Field k]
    (preserves : PreservationFamily Λ k)
    (comparison : RefinementComparisonFamily Λ k)
    (comp : CompositionComparisonFamily Λ k)
    (openIso : Q76OpenExchangeFamily Λ k)
    (pullback_preserves : Q76PullbackPreservationFamily Λ k)
    (exchange : Q76ExchangeFamily Λ k) : Prop :=
  -- refinement
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d : Compactification f.hom.left)
      (r : Compactification.DenseBoundaryCompactification f.hom.left)
      [QuasiCompact f.hom.left]
      (hc : r.obj ⟶ detSfBoundaryCompactification c)
      (hd : r.obj ⟶ detSfBoundaryCompactification d)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comparison f c d).hom.app K ≫ compactificationRefinementComponent Λ hd K.obj =
      compactificationRefinementComponent Λ hc K.obj) ∧
  -- comparison_id
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    comparison f c c = Iso.refl _) ∧
  -- comparison_cocycle
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d e : Compactification f.hom.left),
    comparison f c d ≪≫ comparison f d e = comparison f c e) ∧
  -- comp_normalized
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (T : Compactification.Triangle f.hom.left g.hom.left)
      (_hT : IsSchemeTheoreticallyDominant T.q)
      [QuasiCompact (T.cf.g ≫ T.cg.i)]
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    ∃ m, compositionInterchangeIsNormalized Λ T.cf.g T.cg.i
        (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Λ⟧).obj K.obj) m ∧
      (comp f g T.cf T.cg T.cfg).hom.app K =
        R((T.cg.g)_*⟦Λ⟧).map
          (m ≫ R((T.p)_*⟦Λ⟧).map
            ((openFactor Λ T.cf.i T.q T.cfg.i T.i_q).hom.app K.obj)) ≫
          (rightDerivedLowerStarComp Λ T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg (lowerStar Λ) T.p_g))).hom.app
              (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj)) ∧
  -- comp_independent
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c c' : Compactification f.hom.left) (d d' : Compactification g.hom.left)
      (e e' : Compactification (f.hom.left ≫ g.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comp f g c d e).hom.app K ≫ (comparison (f ≫ g) e e').hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ d).map ((comparison f c c').hom.app K) ≫
        (comparison g d d').hom.app
          ⟨_, (preserves f c').1 K.obj K.property⟩ ≫ (comp f g c' d' e').hom.app K) ∧
  -- unit_left
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comp (𝟙 X) f (Compactification.ofIsProper (𝟙 X.obj.left)) c
      (c.copy (Category.id_comp f.hom.left))).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map ((identity Λ X.obj.left).hom.app K.obj)) ∧
  -- unit_right
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comp f (𝟙 Y) c (Compactification.ofIsProper (𝟙 Y.obj.left))
      (c.copy (Category.comp_id f.hom.left))).hom.app K =
      (identity Λ Y.obj.left).hom.app ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj)) ∧
  -- assoc
  (∀ {X Y Z W : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification h.hom.left)
      (cd : Compactification (f.hom.left ≫ g.hom.left))
      (de : Compactification (g.hom.left ≫ h.hom.left))
      (cde : Compactification ((f.hom.left ≫ g.hom.left) ≫ h.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (rightDerivedLowerShriekOfCompactification Λ e).map ((comp f g c d cd).hom.app K) ≫
        (comp (f ≫ g) h cd e cde).hom.app K =
      (comp g h d e de).hom.app ⟨_, (preserves f c).1 K.obj K.property⟩ ≫
        (comp f (g ≫ h) c de (cde.copy (Category.assoc _ _ _).symm)).hom.app K) ∧
  -- open_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left),
    (openIso (a := a) (v := v) sq c).inv = openExchange Λ sq c) ∧
  -- exchange_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (exchange (a := a) (v := v) sq c d).hom.app K =
      (condensedAmbientExchange Λ (square (c.isPullback_g_ofIsPullback sq).flip)).app
          (D((c.i)_!open⟦Λ⟧).obj K.obj) ≫
        R(((c.ofIsPullback sq).g)_*⟦Λ⟧).map ((openIso (a := a) (v := v) sq c).hom.app K.obj) ≫
        (comparison f' (c.ofIsPullback sq) d).hom.app
          ⟨_, (pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- exchange_independent
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c c' : Compactification f.hom.left) (d d' : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (moduleObjectDerivedPullback Λ v.hom.left).map ((comparison f c c').hom.app K) ≫
        (exchange (a := a) (v := v) sq c' d').hom.app K =
      (exchange (a := a) (v := v) sq c d).hom.app K ≫ (comparison f' d d').hom.app
        ⟨_, (pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- Pasting in the base-change direction, with the canonical pullback compositors.
  (∀ {X Y X' Y' X'' Y'' : SepFinType k}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      {a : X' ⟶ X} {v : Y' ⟶ Y} {b : X'' ⟶ X'} {w : Y'' ⟶ Y'}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (sq' : IsPullback b.hom.left f''.hom.left f'.hom.left w.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
      (e : Compactification f''.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (leftDerivedUpperStarComp Λ w.hom.left v.hom.left).hom.app
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj) ≫
      (moduleObjectDerivedPullback Λ w.hom.left).map
        ((exchange (a := a) (v := v) sq c d).hom.app K) ≫
      (exchange (a := b) (v := w) sq' d e).hom.app
        ⟨_, (pullback_preserves X' X a).1 K.obj K.property⟩ =
    (exchange (a := b ≫ a) (v := w ≫ v) (sq'.paste_horiz sq) c e).hom.app K ≫
      (rightDerivedLowerShriekOfCompactification Λ e).map
        ((leftDerivedUpperStarComp Λ b.hom.left a.hom.left).hom.app K.obj))

/-- Compactification independence on Loc(Dctf), using the normalized comparison of the
recorded composition interface. The existential proof states tensor closure as part of
the conclusion rather than adding a hypothesis on the first input.
Source: blueprint independence sentence and DAG proof step 4
(blueprint: sk-prop-sf-pf-coherence). -/
def Compactification (k : Type u) [Field k]
    (_preserves : PreservationFamily Λ k)
    (comparison : RefinementComparisonFamily Λ k) : Prop :=
  ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c d : AlgebraicGeometry.Compactification f.hom.left)
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) (L : D Λ Y.obj.left),
    (Dctf Λ Y.obj.left L) →
    ∃ h : localizingClosureProEtale Λ X.obj.left (K.obj ⊗ (P Λ f.hom.left).obj L),
      ((comparison f c d).hom.app K ⊗ₘ 𝟙 L) ≫ pf Λ d K.obj L =
        pf Λ c K.obj L ≫ (comparison f c d).hom.app ⟨_, h⟩

/-- Projection commutes with the canonical compact-support compositor. Its coherence laws
are the exact Q76 normalized law conjunction, including the units, associativity,
comparison independence, k-morphism exchange normalization, and pasted base change.
Source: blueprint composition sentence and DAG proof step 5
(blueprint: sk-prop-sf-pf-coherence). -/
def Composition (k : Type u) [Field k]
    (comp : CompositionComparisonFamily Λ k) : Prop :=
  ∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : AlgebraicGeometry.Compactification f.hom.left)
    (d : AlgebraicGeometry.Compactification g.hom.left)
    (e : AlgebraicGeometry.Compactification (f.hom.left ≫ g.hom.left))
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) (L : D Λ Z.obj.left),
    (Dctf Λ Z.obj.left L) →
    ∃ h : localizingClosureProEtale Λ X.obj.left
        (K.obj ⊗ (P Λ (f.hom.left ≫ g.hom.left)).obj L),
      ((comp f g c d e).hom.app K ⊗ₘ 𝟙 L) ≫ pf Λ e K.obj L =
        pf Λ d ((F Λ c).obj K.obj) L ≫
          (F Λ d).map (pf Λ c K.obj ((P Λ g.hom.left).obj L)) ≫
          (F Λ d).map ((F Λ c).map
            (𝟙 K.obj ⊗ₘ (leftDerivedUpperStarComp Λ f.hom.left g.hom.left).inv.app L)) ≫
          (comp f g c d e).hom.app ⟨_, h⟩

/-- The fixed-compactification exchange for an arbitrary Cartesian square, with no
invertibility of exchange or projection assumed.
Source: blueprint displayed square and DAG proof steps 2--3
(blueprint: sk-prop-sf-pf-coherence). -/
def squareExchange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback a f' f v)
    (c : AlgebraicGeometry.Compactification f) :
    F Λ c ⋙ P Λ v ⟶ P Λ a ⋙ F Λ (c.ofIsPullback sq) :=
  CompactificationReindexing.squareExchange Λ
    { middle := pullback.fst c.g v
      openSquare := c.isPullback_i_ofIsPullback sq
      properSquare := (IsPullback.of_hasPullback c.g v).toCommSq }

/-- The monoidal target identification in the displayed base-change square.
Source: blueprint displayed square and DAG proof steps 2--3
(blueprint: sk-prop-sf-pf-coherence). -/
def squareTensorInput {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback a f' f v)
    (K : D Λ X) (L : D Λ Y) :
    (P Λ a).obj (K ⊗ (P Λ f).obj L) ⟶
      (P Λ a).obj K ⊗ (P Λ f').obj ((P Λ v).obj L) :=
  ((leftDerivedUpperStarTensor Λ a).app K).app ((P Λ f).obj L) ≫
    (𝟙 _ ⊗ₘ (pullbackSquareComparison Λ sq.toCommSq).inv.app L)

set_option maxHeartbeats 4000000 in
-- The square elaborates several large derived-functor comparison types.
/-- Base-change compatibility for Dbc in the first variable and Dctf in the second.
The vertical scheme maps are morphisms in `SepFinType k`, hence k-morphisms.
No finite-Tor condition is put on K.
Source: blueprint displayed square and DAG proof steps 2--3
(blueprint: sk-prop-sf-pf-coherence). -/
def BaseChange (k : Type u) [Field k] : Prop :=
  ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : AlgebraicGeometry.Compactification f.hom.left)
    (K : D Λ X.obj.left) (L : D Λ Y.obj.left),
    constantModelBoundedConstructible Λ X.obj.left K →
    (Dctf Λ Y.obj.left L) →
    let a₀ := a.hom.left
    let v₀ := v.hom.left
    (P Λ v₀).map (pf Λ c K L) ≫
        (squareExchange Λ sq c).app (K ⊗ (P Λ f.hom.left).obj L) ≫
        (F Λ (c.ofIsPullback sq)).map (squareTensorInput Λ sq K L) =
        ((leftDerivedUpperStarTensor Λ v₀).app ((F Λ c).obj K)).app L ≫
        ((squareExchange Λ sq c).app K ⊗ₘ 𝟙 _) ≫
        pf Λ (c.ofIsPullback sq) ((P Λ a₀).obj K) ((P Λ v₀).obj L)

/-- Finite discrete etale/pro-etale realization of the same compactification projection.
The three bounded-below witnesses permit exactly the site comparisons used below.
The coefficient encoding, tensorator, pullback map and compact-support comparison are
all the normalized existing constructions; no existential comparison map is substituted.
Source: blueprint realization clause and DAG proof step 7
(blueprint: sk-prop-sf-pf-coherence). -/
def FiniteRealization : Prop :=
  ∀ (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : AlgebraicGeometry.Compactification f)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} A) X)
    (N : Etale.DerivedCategoryModule (ULift.{u + 1} A) Y)
    (hM : DerivedCategory.TStructure.t.plus M)
    (_hN : DerivedCategory.TStructure.t.plus N)
    (hT : DerivedCategory.TStructure.t.plus
      (M ⊗ (FiniteNativeTensor.etaleU A f).obj N)),
    let VX := FiniteDiscreteOrdinary.internalEtaleRealization A X (E X)
    let VY := FiniteDiscreteOrdinary.internalEtaleRealization A Y (E Y)
    letI := FiniteNativeTensor.realizationMonoidal A X (E X)
    letI := FiniteNativeTensor.realizationMonoidal A Y (E Y)
    VY.map (FiniteNativeTensor.etaleP A c M N) ≫
        (FiniteNativeTensor.compactComparison A E c ⟨_, hT⟩).hom =
      (Functor.Monoidal.μIso VY ((FiniteNativeTensor.etaleF A c).obj M) N).inv ≫
        ((FiniteNativeTensor.compactComparison A E c ⟨M, hM⟩).hom ⊗ₘ 𝟙 _) ≫
        pf (FiniteDiscreteOrdinary.coefficient A) c (VX.obj M) (VY.obj N) ≫
        (F (FiniteDiscreteOrdinary.coefficient A) c).map
          ((𝟙 _ ⊗ₘ (FiniteNativeTensor.realizationPull A E f).inv.app N) ≫
            (Functor.Monoidal.μIso VX M ((FiniteNativeTensor.etaleU A f).obj N)).hom)

/-- Coherence of the canonical condensed projection transformations.

Source: latest blueprint sec-six-functors/sk-prop-sf-pf-coherence, all clauses
(blueprint: sk-prop-sf-pf-coherence).

Proof, in the order of the seven DAG steps:
1. Expand the projection into its proper counit transpose and its inverse open-unit
   tensor comparison. Both are natural. At the identity compactification the adjunction
   units and counits and the canonical pullback/tensor identity comparisons cancel.
2. For the proper factor, transpose the base-change square. Monoidality of the pullback
   square and the triangle identity identify both adjuncts with the pulled-back counit
   tensored with the identity. Neither projection nor exchange is inverted.
3. For the open factor, use the invertible open units to restrict both composites to
   the open. They are the identity there. Paste with step 2 to get BaseChange.
4. Transpose the dense-refinement square and restrict to the original open, where it
   is the identity. Apply proper projection composition and common dense refinements.
   Cancel only the refinement comparisons on Loc(Dctf), using the specified localizing
   compactification coherence. This gives Compactification and transfers Identity and
   Proper from their identity-open models to every compactification.
5. Expand both composable projection words into proper/open factors. Mate pasting and
   the normalized middle interchange give Composition. For three arrows the compositor
   associativity law in Q76ComparisonLaws identifies the bracketings; tensor associativity
   identifies the tensor reassociations. This gives the associativity pentagon.
6. Tensor/evaluation and open-unit scalar compatibility give Scalar with the actual
   pasted scalarCompactSupportMap. On the listed scalar comparison domain it is the
   comparison of scalarSixCompactSupportForScalarMaps. No arbitrary-input inverse is used.
7. At finite discrete coefficients use moduleObject_ordinary_coefficient_equivalence.
   Its normalized section-action encoding identifies the internal adjunctions and
   relative tensors. The bounded-below site comparison preserves the proper counit,
   open unit and pullback tensorator. Paste these squares to get FiniteRealization.
Zero objects, empty schemes, identity coefficient maps and identity opens require no
separate choices; every comparison in the displayed identities has the same normalization.
-/
theorem condensedProjectionFormulaCoherence
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    Natural Λ ∧ Identity Λ ∧ TensorAssociativity Λ ∧ Proper Λ ∧
      (∃ (preserves : PreservationFamily Λ k)
        (comparison : RefinementComparisonFamily Λ k)
        (comp : CompositionComparisonFamily Λ k)
        (openIso : Q76OpenExchangeFamily Λ k)
        (pullback_preserves : Q76PullbackPreservationFamily Λ k)
        (exchange : Q76ExchangeFamily Λ k),
        Q76ComparisonLaws Λ k preserves comparison comp openIso pullback_preserves exchange ∧
          Compactification (Λ := Λ) k preserves comparison ∧
          Composition (Λ := Λ) k comp) ∧
      BaseChange (Λ := Λ) k ∧ Scalar ∧ FiniteRealization := by
  sorry

end ProjectionCoherence
end AlgebraicGeometry.ProEtale.CondensedRing
