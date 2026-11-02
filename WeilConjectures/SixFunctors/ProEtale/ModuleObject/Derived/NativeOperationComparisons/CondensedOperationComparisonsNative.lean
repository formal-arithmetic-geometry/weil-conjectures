/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixNormalizedImmersion
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompatibility
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarCompatibility
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAffineGeometry
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Compact-support, exceptional and coefficient comparisons on native condensed categories

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
prop-pur-weil-equivariance-compatibilities.proof.md, sole proof paragraph, constituent
compact-support, mate/counit and coefficient/exchange compatibilities
(blueprint: lem-pur-condensed-operation-comparisons).

The full subcategories are the published bounded constructible finite-Tor categories of
ordinary derived internal modules over the coefficient ring pulled from the condensed point.
The selected composition and exchange maps are fixed by the dependency's refinement and
proper/open normalization equations. Selecting them does not choose arbitrary isomorphisms.
Right adjoints are quantified together with their adjunctions; their conjugates and exceptional
exchange maps below are actual adjunction constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace NativeOperationComparisons

open CompactSupportComposition

/-- Exactly the four coefficient stages in the statement, invariant under coefficient
isomorphism. The finite quotient uses the recorded uniformizer and the discrete topology.
Source: opening coefficient convention (blueprint: lem-pur-condensed-operation-comparisons). -/
def IsCoefficient (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) : Prop :=
  (∃ (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ), 1 ≤ n ∧
    Nonempty (Mon.mk Λ.X ≅ Mon.mk
      (cartesianFinitePointRing (ULift.{u} (Padic.coefficientExtensionRing ell E.1 n))))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E.1))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
  Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell))

/-- The k-linear native witness package extracted from the current compact-support
composition theorem.  Every square in this package is indexed by `SepFinType k`; in
particular no arbitrary scheme-map or semilinear square is hidden in the native data.
The package records the six witness families supplied by
`sk_thm_sf_comp_composition`; its complete normalization and coherence conjunction is
carried by `Data.coherent_laws` below.
Source: sk-thm-sf-comp-composition clauses (1)-(2), as used in proof step 1 of the node
(blueprint: lem-pur-condensed-operation-comparisons). -/
structure NativeCompactSupportData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] where
  preserves : ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    (∀ K, localizingClosureProEtale Λ X.obj.left K →
      localizingClosureProEtale Λ Y.obj.left
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ X.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ Y.obj.left
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ∧
        DerivedCategory.finiteTorAmplitude _
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
  comparison : ∀ {X Y : SepFinType k} (f : X ⟶ Y)
    (c d : Compactification f.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ d
  comp : ∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification (f.hom.left ≫ g.hom.left)),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙
          rightDerivedLowerShriekOfCompactification Λ d) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ e
  openIso : ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left),
    D((c.i)_!open⟦Λ⟧) ⋙ moduleObjectDerivedPullback Λ (pullback.fst c.g v.hom.left) ≅
      moduleObjectDerivedPullback Λ a.hom.left ⋙ D(((c.ofIsPullback sq).i)_!open⟦Λ⟧)
  pullback_preserves : ∀ (X Y : SepFinType k) (v : X ⟶ Y),
    (∀ K, localizingClosureProEtale Λ Y.obj.left K →
      localizingClosureProEtale Λ X.obj.left
        ((moduleObjectDerivedPullback Λ v.hom.left).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ Y.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ X.obj.left
        ((moduleObjectDerivedPullback Λ v.hom.left).obj K) ∧
        DerivedCategory.finiteTorAmplitude _
          ((moduleObjectDerivedPullback Λ v.hom.left).obj K))
  exchange : ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (_sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙
          moduleObjectDerivedPullback Λ v.hom.left) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ a.hom.left ⋙
          rightDerivedLowerShriekOfCompactification Λ d)

/-- The complete normalization and coherence conjunction from Q76.  Keeping this
predicate on `Data` is what makes the restricted alpha and B maps canonical rather
than arbitrary endpoint isomorphisms. The conjunction is verbatim the law part of
`sk_thm_sf_comp_composition`.
Source: sk-thm-sf-comp-composition, refinement, canonicity, unit, associativity and
proper/open normalization equations, as used in proof step 1 of the node
(blueprint: lem-pur-condensed-operation-comparisons). -/
def NativeCompactSupportLaws
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k]
    (H : NativeCompactSupportData Λ k) : Prop :=
  -- refinement
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d : Compactification f.hom.left)
      (r : Compactification.DenseBoundaryCompactification f.hom.left)
      [QuasiCompact f.hom.left]
      (hc : r.obj ⟶ detSfBoundaryCompactification c)
      (hd : r.obj ⟶ detSfBoundaryCompactification d)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comparison f c d).hom.app K ≫ compactificationRefinementComponent Λ hd K.obj =
      compactificationRefinementComponent Λ hc K.obj) ∧
  -- comparison_id
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    H.comparison f c c = Iso.refl _) ∧
  -- comparison_cocycle
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d e : Compactification f.hom.left),
    H.comparison f c d ≪≫ H.comparison f d e = H.comparison f c e) ∧
  -- comp_normalized
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (T : Compactification.Triangle f.hom.left g.hom.left)
      (_hT : IsSchemeTheoreticallyDominant T.q)
      [QuasiCompact (T.cf.g ≫ T.cg.i)]
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    ∃ m, compositionInterchangeIsNormalized Λ T.cf.g T.cg.i
        (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Λ⟧).obj K.obj) m ∧
      (H.comp f g T.cf T.cg T.cfg).hom.app K =
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
    (H.comp f g c d e).hom.app K ≫ (H.comparison (f ≫ g) e e').hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ d).map ((H.comparison f c c').hom.app K) ≫
        (H.comparison g d d').hom.app
          ⟨_, (H.preserves f c').1 K.obj K.property⟩ ≫ (H.comp f g c' d' e').hom.app K) ∧
  -- unit_left
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comp (𝟙 X) f (Compactification.ofIsProper (𝟙 X.obj.left)) c
      (c.copy (Category.id_comp f.hom.left))).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map ((identity Λ X.obj.left).hom.app K.obj)) ∧
  -- unit_right
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comp f (𝟙 Y) c (Compactification.ofIsProper (𝟙 Y.obj.left))
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
    (rightDerivedLowerShriekOfCompactification Λ e).map ((H.comp f g c d cd).hom.app K) ≫
        (H.comp (f ≫ g) h cd e cde).hom.app K =
      (H.comp g h d e de).hom.app ⟨_, (H.preserves f c).1 K.obj K.property⟩ ≫
        (H.comp f (g ≫ h) c de (cde.copy (Category.assoc _ _ _).symm)).hom.app K) ∧
  -- open_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left),
    (H.openIso (a := a) (v := v) sq c).inv = openExchange Λ sq c) ∧
  -- exchange_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.exchange (a := a) (v := v) sq c d).hom.app K =
      (condensedAmbientExchange Λ (square (c.isPullback_g_ofIsPullback sq).flip)).app
          (D((c.i)_!open⟦Λ⟧).obj K.obj) ≫
        R(((c.ofIsPullback sq).g)_*⟦Λ⟧).map ((H.openIso (a := a) (v := v) sq c).hom.app K.obj) ≫
        (H.comparison f' (c.ofIsPullback sq) d).hom.app
          ⟨_, (H.pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- exchange_independent
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c c' : Compactification f.hom.left) (d d' : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (moduleObjectDerivedPullback Λ v.hom.left).map ((H.comparison f c c').hom.app K) ≫
        (H.exchange (a := a) (v := v) sq c' d').hom.app K =
      (H.exchange (a := a) (v := v) sq c d).hom.app K ≫ (H.comparison f' d d').hom.app
        ⟨_, (H.pullback_preserves X' X a).1 K.obj K.property⟩) ∧
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
        ((H.exchange (a := a) (v := v) sq c d).hom.app K) ≫
      (H.exchange (a := b) (v := w) sq' d e).hom.app
        ⟨_, (H.pullback_preserves X' X a).1 K.obj K.property⟩ =
    (H.exchange (a := b ≫ a) (v := w ≫ v) (sq'.paste_horiz sq) c e).hom.app K ≫
      (rightDerivedLowerShriekOfCompactification Λ e).map
        ((leftDerivedUpperStarComp Λ b.hom.left a.hom.left).hom.app K.obj))

variable {k : Type u} [Field k] {Λ : ScalarSixRing.{u}}

/-- Preservation and the canonical comparison family supplied by the Q76 attachment.
This first projection is proof data, not a choice of a new functor.
Source: composition theorem, preservation (blueprint: lem-pur-condensed-operation-comparisons). -/
abbrev preserves (H : NativeCompactSupportData Λ.X k)
    {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  H.preserves (X := X) (Y := Y) f c

/-- The model compositor supplied by the Q76 attachment; its normalization is recorded
in `Data.coherent_laws`.
Source: composition theorem, alpha (blueprint: lem-pur-condensed-operation-comparisons). -/
@[irreducible] def modelComposition (H : NativeCompactSupportData Λ.X k)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.hom.left) (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ g.hom.left)) :
    (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ.X c ⋙
          rightDerivedLowerShriekOfCompactification Λ.X d) ≅
      (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ.X e :=
  H.comp (X := X) (Y := Y) (Z := Z) f g c d e

/-- Pullback preservation, the proof field in the same coherent comparison family.
Source: composition theorem, k-linear base maps
(blueprint: lem-pur-condensed-operation-comparisons). -/
abbrev pullPreserves (H : NativeCompactSupportData Λ.X k)
    (X Y : SepFinType k) (v : X ⟶ Y) :=
  H.pullback_preserves X Y v

/-- The exchange supplied by the Q76 attachment; its proper/open normalization and
compactification comparison are recorded in `Data.coherent_laws`.
Source: composition theorem, B (blueprint: lem-pur-condensed-operation-comparisons). -/
@[irreducible] def modelExchange (H : NativeCompactSupportData Λ.X k)
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left) :
    (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ.X c ⋙
          moduleObjectDerivedPullback Λ.X v.hom.left) ≅
      (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ.X u.hom.left ⋙
          rightDerivedLowerShriekOfCompactification Λ.X d) :=
  H.exchange (X := X) (Y := Y) (X' := X') (Y' := Y')
    (f := f) (f' := f') (a := u) (v := v) sq c d

/-- The fully faithful inclusion of the existing Dctf category in its ambient derived category.
Source: full-subcategory convention (blueprint: lem-pur-condensed-operation-comparisons). -/
abbrev inclusion (Γ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Γ.X X ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Γ.X X) :=
  ObjectProperty.ι _

/-- The canonical inclusion of Dctf in its localizing closure, with unchanged objects and maps.
Source: composition theorem, restriction to C
(blueprint: lem-pur-condensed-operation-comparisons). -/
def toLocalizing (Γ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Γ.X X ⥤
      (localizingClosureProEtale Γ.X X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)

/-- The chosen compactification functor, restricted to the actual Dctf full subcategories.
Source: sk-thm-existence (blueprint: lem-pur-condensed-operation-comparisons). -/
def lower (H : NativeCompactSupportData Λ.X k)
    {X Y : SepFinType k} (f : X ⟶ Y) :
    ConstantModelConstructibleFiniteTor Λ.X X.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X Y.obj.left :=
  ObjectProperty.lift _
    (inclusion Λ X.obj.left ⋙
      rightDerivedLowerShriekOfCompactification Λ.X (compactificationOverField f.hom))
    (fun K ↦ (preserves H f (compactificationOverField f.hom)).2 K.obj K.property)

/-- Derived pullback restricted by the dependency's preservation assertion. The underlying
map is a morphism in `SepFinType k`, so its underlying scheme map is k-linear.
Source: composition theorem, U and V (blueprint: lem-pur-condensed-operation-comparisons). -/
def pull (H : NativeCompactSupportData Λ.X k)
    (X Y : SepFinType k) (v : X ⟶ Y) :
    ConstantModelConstructibleFiniteTor Λ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left :=
  ObjectProperty.lift _ (inclusion Λ Y.obj.left ⋙ moduleObjectDerivedPullback Λ.X v.hom.left)
    (fun K ↦ (pullPreserves H X Y v).2 K.obj K.property)

/-- Alpha is the restriction of exactly the normalized dependency compositor.
Source: first displayed comparison (blueprint: lem-pur-condensed-operation-comparisons). -/
def composition (H : NativeCompactSupportData Λ.X k)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lower H f ⋙ lower H g ≅ lower H (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (inclusion Λ Z.obj.left)
    (Functor.isoWhiskerLeft (toLocalizing Λ X.obj.left)
      (modelComposition H f g (compactificationOverField f.hom)
        (compactificationOverField g.hom) (compactificationOverField (f ≫ g).hom)))

/-- B is the restriction of exactly the normalized dependency exchange. Cartesian squares
are given by IsPullback, so this includes all their realizations, not only a chosen pullback.
Source: compact-support exchange (blueprint: lem-pur-condensed-operation-comparisons). -/
def exchange (H : NativeCompactSupportData Λ.X k)
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left) :
    lower H f ⋙ pull H Y' Y v ≅ pull H X' X u ⋙ lower H f' :=
  Functor.fullyFaithfulCancelRight (inclusion Λ Y'.obj.left)
    (Functor.isoWhiskerLeft (toLocalizing Λ X.obj.left)
      (modelExchange H (X := X) (Y := Y) (X' := X') (Y' := Y')
        (f := f) (f' := f') sq (compactificationOverField f.hom)
        (compactificationOverField f'.hom)))

/-- The inherited identity pullback comparison, retaining its canonical unit normalization.
Source: identity square (blueprint: lem-pur-condensed-operation-comparisons). -/
def pullId (H : NativeCompactSupportData Λ.X k) (X : SepFinType k) :
    pull H X X (𝟙 X) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (inclusion Λ X.obj.left)
    (Functor.isoWhiskerLeft (inclusion Λ X.obj.left) (leftDerivedUpperStarId Λ.X X.obj.left))

/-- The canonical inherited pullback compositor used in successive base change.
Source: vertical pasting (blueprint: lem-pur-condensed-operation-comparisons). -/
def pullComp (H : NativeCompactSupportData Λ.X k) (X Y Z : SepFinType k)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull H X Z (f ≫ g) ≅ pull H Y Z g ⋙ pull H X Y f :=
  Functor.fullyFaithfulCancelRight (inclusion Λ X.obj.left)
    (Functor.isoWhiskerLeft (inclusion Λ Z.obj.left)
      (leftDerivedUpperStarComp Λ.X f.hom.left g.hom.left))

/-- The conjugate of alpha under the specified composite adjunction and the gf adjunction.
The right adjoint to F_f then F_g is E_g then E_f in Lean's functor order.
Source: first counit identity (blueprint: lem-pur-condensed-operation-comparisons). -/
def conjugate {X Y Z : SepFinType k} (H : NativeCompactSupportData Λ.X k)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {Ef : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left}
    {Eg : ConstantModelConstructibleFiniteTor Λ.X Z.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X Y.obj.left}
    {Egf : ConstantModelConstructibleFiniteTor Λ.X Z.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left}
    (af : lower H f ⊣ Ef) (ag : lower H g ⊣ Eg) (agf : lower H (f ≫ g) ⊣ Egf) :
    Egf ≅ Eg ⋙ Ef :=
  conjugateIsoEquiv agf (af.comp ag) (composition H f g)

/-- The transpose of inverse B followed by the pulled-back counit. This construction is
made for every square; invertibility is a separate geometric assertion below.
Source: second counit identity (blueprint: lem-pur-condensed-operation-comparisons). -/
def exceptional {X Y X' Y' : SepFinType k}
    (H : NativeCompactSupportData Λ.X k) {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    {Ef : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left}
    {Ef' : ConstantModelConstructibleFiniteTor Λ.X Y'.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X'.obj.left}
    (af : lower H f ⊣ Ef) (af' : lower H f' ⊣ Ef') :
    Ef ⋙ pull H X' X u ⟶ pull H Y' Y v ⋙ Ef' :=
  (mateEquiv af af' (TwoSquare.mk _ _ _ _ (exchange H sq).inv)).natTrans

variable {D : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ} [Fact ell.Prime]

/-- The native condensed compact-support comparisons, their conjugate and exceptional counit
identities, smooth exceptional invertibility, and the scalar/exchange rectangle with its
composition and pasting coherences. The base datum retains q = p^a and the specified
algebraic closure. Every coefficient stage retains the finite-subextension convention,
and every geometric arrow in this helper is a morphism of `SepFinType D.k`.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
prop-pur-weil-equivariance-compatibilities.proof.md, sole proof paragraph, constituent
compact-support, mate/counit and coefficient/exchange compatibilities
(blueprint: lem-pur-condensed-operation-comparisons).

Proof, following the nine steps of the node:
1. By sk-thm-existence the compact-support functors and their right adjoints restrict to the
   constructible finite-Tor categories. The field `D.k` is an algebraic closure of `F_q`, so the
   standing hypothesis `Finite k ∨ IsAlgClosed k` of `sk_thm_sf_comp_composition` holds, and every
   displayed map is a morphism of `SepFinType D.k`. Clause (1) supplies the canonical associative
   and unital alpha with its proper/open interchange normalization; clause (2) supplies the
   canonical invertible proper/open exchange B and its compatibility with composing Cartesian
   squares. The compactification identifications are those of sk-prop-sf-comp-coherence, and the
   formula for B is def-sfb-compact-support-base-change-maps. This gives `Data.coherent` and
   `Data.coherent_laws` for each of the four coefficient stages.
2. Equip `F_g F_f ⊣ E_f E_g` with the composite adjunction, whose counit at K is
   `ε_g K ∘ F_g(ε_f (E_g K))`. Conjugate alpha under it and `F_{gf} ⊣ E_{gf}`; conjugation sends
   isomorphisms to isomorphisms, giving `c : E_{gf} ≅ E_f E_g` (`conjugate`). The mate-counit
   identity with identity side functors is `composition_counit` (Stacks 0DV0; Mathlib
   `conjugateEquiv_counit`). The identity and composition properties of conjugation and mate
   pasting (2)-(4) identify its unit and associativity constraints with those of alpha.
3. Compute B on a compactification `f = p j`: by def-sfb-compact-support-base-change-maps it is
   `Rp'_* o_v ∘ Ex_{v,p}(j_! -)`, with `o_v` inverse to the canonical open-adjunction mate. For
   successive base maps, mate pasting (1), with the inverse-image compositors of
   prop-sfb-module-left-derived-upper-star-comp, gives
   `Ex_{vw,p} = (Ex_{w,p'} v̄^*) ∘ (w^* Ex_{v,p})`; the same identity for the open adjunctions
   gives `o_{vw} = (o_w u^*) ∘ (w̄^* o_v)`, identified with the internal open maps by
   lem-sfb-internal-module-operations-transport. The identity case is mate pasting (4).
4. Substituting Step 3, naturality moves the middle open comparison past proper exchange,
   giving `B_{vw} = (B_w u^*) ∘ (w^* B_v)` and `B_id = 1` (`exchange_identity`,
   `exchange_pasting`). For the stacked-square equation (`composition_exchange`) use the
   normalized models `f = p j`, `g = q i`, `i p = r h` of clause (1), with mixed map
   `ι : J_i R_p → R_r J_h` the open-adjunction transpose of inverse open restriction
   (det-sf-comp-composition-interchange). Pull this Cartesian proper/open square back along w.
   The two maps of the mixed cube, both from `P_w J_i R_p` to `R_{r'} J_{h'} P_c`, become the
   same `Ex_p` after identifying the source with `J_{i'} P_a R_p` by `o_i` and transposing under
   `J_{i'} ⊣ P_{i'}` (mate pasting (1)-(2), lem-sfb-derived-open-restriction-normalization,
   lem-sfb-ringed-derived-monoidal-comparisons). Expand alpha by `Rq_*(ι_{J_j K})` and B by proper
   then open exchange, paste the proper and open factors, and move the sole interchange by the
   mixed cube; this yields `(α_{g',f'} u^*) ∘ F_{g'}(B_{v,f}) ∘ (B_{w,g} F_f)`.
   Non-dense pulled-back models are compared to dense refinements by
   lem-sfb-compact-support-refinement-base-change and the cocycle of sk-prop-sf-comp-coherence;
   the equation restricts to Dctf.
5. Apply lem-amb-mate-unit-counit to `L₁ = F_f`, `L₂ = F_{f'}`, `G = U`, `H = V` and `B⁻¹`; its
   mate is `exceptional`. Hence `ε_{f'} (V K) ∘ F_{f'}(e_K) = V(ε_f K) ∘ B⁻¹_{E_f K}`; composing
   with `B_{E_f K}` gives `exceptional_counit`.
6. For f smooth of pure relative dimension d, the exceptional base-change comparison of
   sk-prop-sp-purity-bc is exactly `e`, and its equation reads
   `e_K ∘ u^* γ_f(K) = γ_{f'}(v^* K) ∘ s_K`. By sk-thm-purity-transport both γ's are isomorphisms
   for every admissible Λ, and `s_K` is invertible, so `e_K` is invertible. For general smooth f,
   cover X by the open loci `X_d` of sbc-lem-smooth-relative-dimension-locally-constant (Noetherian
   by lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-noetherian-open-subscheme-noetherian).
   Step 4 for `j_d` and f with mate pasting identifies `e_{f_d}` with `E_{j'_d}(e_f) ∘ e_{j_d,E_f}`,
   so `E_{j'_d}(e_f)` is invertible; purity in dimension zero identifies `E_{j'_d}` with open
   restriction, and lem-sfb-sheaf-cover-local-isomorphism on the cohomology sheaves of the cone of
   `e_f` gives `smooth_exceptional`. The empty source gives the zero category.
7. For coefficient change, the open comparison `h_j : T j_! ≅ j'_! T` is the normalized comparison
   of lem-sfb-scalar-six-normalized-immersion. The two routes exchanging scalar change with
   `o_v` are maps between extensions by zero from the same pulled-back open; restriction there is
   faithful (lem-sfb-locally-closed-extension-coherence, transported by
   lem-sfb-internal-module-operations-transport), and the restrictions agree by
   lem-sfb-scalar-pullback-square-coherence. Hence the open coefficient/exchange rectangle commutes.
8. For the proper part, apply lem-sfb-scalar-geometric-exchange-rectangle to p and `j_! K`, with its
   λ replaced by `j⁻¹` (lem-sfb-scalar-six-derived-pullback-normalization,
   def-sfb-scalar-six-coefficient-interfaces, lem-sfb-kflat-scalar-comparison-normalization). Paste
   it with the open rectangle of Step 7 and apply proper pushforward; by
   det-prop-scalar-six-compact-support the coefficient sides are `b_f`, `b_{f'}`, by
   def-sfb-compact-support-base-change-maps the exchange sides are B, B'. Cancelling the adjacent
   inverse j's gives `scalar_exchange`; the listed hypotheses make the b's isomorphisms
   (`scalar_isIso`, with `scalar_preserves` from det-prop-scalar-six-compact-support).
9. Paste two instances of Step 8, replacing successive B's by `B_{vw}` (Step 4) and successive
   scalar/pullback comparisons by the composite one (det-prop-scalar-six-pullback (1)); this is
   `scalar_exchange_pasting`. For a composite gf, paste the equations for g and f and identify the
   composite b with `b_{gf}` (det-prop-scalar-six-compact-support) and the exchange sides through
   alpha (Step 4); this is `scalar_composition`.
The theorem below is intentionally left as the single named stage-2 `sorry`.
-/
theorem nativeCondensedOperationComparisons (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p) :
    ∃ S : Data D ell, Laws S := by
  sorry

end NativeOperationComparisons
end AlgebraicGeometry.ProEtale.CondensedRing
