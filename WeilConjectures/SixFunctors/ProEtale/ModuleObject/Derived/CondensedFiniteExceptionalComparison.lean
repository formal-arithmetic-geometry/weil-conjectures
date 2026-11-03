/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
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
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldFiniteTorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Affine.AffineEtaleFreeDetection
public import Mathlib.CategoryTheory.Skeletal
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalBounds
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
public import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
public import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.PoincareDuality.ProjectionFormula
import Mathlib.Tactic.DefEqTransformations
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarPullbackMateInverseNormalized
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification

/-! # Finite condensed exceptional comparison

Source: latest blueprint, sec-six-functors/sk-thm-sf-package/_section.md, clause (1),
and sk-thm-sf-package.proof.md, paragraph beginning "Clause (1)".
(blueprint: lem-sf-condensed-finite-exceptional-comparison).

All derived categories here are ordinary uncompleted categories. The coefficient index
bundles a finite commutative ell-primary ring, including the zero ring. The witnesses
below retain the normalized section-action encoding and the actual proper/open scalar
map. No functor or comparison is selected from the final existence theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The pro-etale site has the existing small-site size bound.
Source: the project size convention (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
private instance finiteExceptionalProEtEssentiallySmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Binder packaging for arbitrary finite commutative ell-primary rings.
Source: blueprint clause (1), finite coefficients
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
structure FiniteExceptionalRing (ell : ℕ) where
  ring : CommRingCat.{u}
  finite : Finite ring
  killed : ∃ n : ℕ, (ell : ring) ^ n = 0

attribute [instance] FiniteExceptionalRing.finite

/-- The recorded discrete condensed coefficient, with no new coefficient model.
Source: blueprint finite coefficient convention
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev FiniteExceptionalRing.coefficient {ell : ℕ} (A : FiniteExceptionalRing.{u} ell) :
    ScalarSixRing.{u} := ⟨cartesianFinitePointRing A.ring⟩

/-- The ordinary uncompleted internal-module derived category.
Source: blueprint clause (1)
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev FiniteExceptionalRing.ambient {ell : ℕ} (A : FiniteExceptionalRing.{u} ell)
    (T : Scheme.{u}) :=
  DerivedCategory (ModuleRingedComparison.internalModules A.coefficient.X T)

/-- The recorded bounded constructible finite-Tor full subcategory.
Source: blueprint clause (1)
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev FiniteExceptionalRing.small {ell : ℕ} (A : FiniteExceptionalRing.{u} ell)
    (T : Scheme.{u}) := ConstantModelConstructibleFiniteTor A.coefficient.X T

/-- The recorded ambient localizing closure, without derived completion.
Source: blueprint clause (1)
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev FiniteExceptionalRing.localizing {ell : ℕ} (A : FiniteExceptionalRing.{u} ell)
    (T : Scheme.{u}) := (localizingClosureProEtale A.coefficient.X T).FullSubcategory

/-- Ordinary etale modules in the existing fixed universe-lift presentation.
Source: blueprint finite module and site comparisons
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev FiniteExceptionalRing.etale {ell : ℕ} (A : FiniteExceptionalRing.{u} ell)
    (T : Scheme.{u}) := Etale.DerivedCategoryModule (ULift.{u + 1} A.ring) T

/-- The actual postcomposition map of discrete condensed rings. Its components send
s to phi composed with s, so every unital ring map, including nonflat maps, is admitted.
Source: blueprint arbitrary finite coefficient maps
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalCoefficientMap {ell : ℕ} {A B : FiniteExceptionalRing.{u} ell}
    (φ : A.ring →+* B.ring) : A.coefficient ⟶ B.coefficient := by
  letI : TopologicalSpace A.ring := ⊥
  letI : TopologicalSpace B.ring := ⊥
  letI : DiscreteTopology A.ring := discreteTopology_bot _
  letI : DiscreteTopology B.ring := discreteTopology_bot _
  let g : Profinite.continuousCoefficientRingSheaf A.ring ⟶
      Profinite.continuousCoefficientRingSheaf B.ring :=
    Profinite.continuousMapRingSheafMapOfUniverse φ continuous_of_discreteTopology
  let m : A.coefficient.X ⟶ B.coefficient.X :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map g
  letI : IsMonHom m := Sheaf.isMonHom_sheafCompose_map _ g
  exact ⟨⟨m⟩⟩

/-- The normalized section-action encoding, at the fixed discrete topology.
Source: lem-sf-module-object-ordinary-coefficient-equivalence
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev finiteExceptionalEncoding {ell : ℕ} (A : FiniteExceptionalRing.{u} ell)
    (T : Scheme.{u}) :=
  letI : TopologicalSpace A.ring := ⊥
  letI : DiscreteTopology A.ring := discreteTopology_bot _
  FiniteDiscreteOrdinary.Encoding A.ring T

/-- The actual termwise derived encoding, rather than an unrelated derived equivalence.
Source: lem-sf-module-object-ordinary-coefficient-equivalence
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalEncodingDerived {ell : ℕ} {A : FiniteExceptionalRing.{u} ell}
    {T : Scheme.{u}} (e : finiteExceptionalEncoding A T) :=
  letI : TopologicalSpace A.ring := ⊥
  letI : DiscreteTopology A.ring := discreteTopology_bot _
  e.fixedDerived

/-- The underived normalized encoding whose termwise localization is the recorded
finite derived encoding. Source: finite coefficient identification, steps 2--4
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev finiteExceptionalUnderivedEncoding {ell : ℕ} {A : FiniteExceptionalRing.{u} ell}
    {T : Scheme.{u}} (e : finiteExceptionalEncoding A T) :=
  letI : TopologicalSpace A.ring := ⊥
  letI : DiscreteTopology A.ring := discreteTopology_bot _
  e.ordinary.trans e.fixed

/-- The actual pulled-back coefficient-ring map, with no alternate scalar model.
Source: blueprint coefficient change
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev finiteExceptionalSchemeCoefficientMap {ell : ℕ}
    {A B : FiniteExceptionalRing.{u} ell} (φ : A.ring →+* B.ring) (T : Scheme.{u}) :=
  coefficientMap (Λ := A.coefficient.X) (Λ' := B.coefficient.X)
    (finiteExceptionalCoefficientMap φ).hom.hom T

/-- Restriction comparison with the identity action on every underlying section.
This is the restriction normalization of internal_section_scalar_adjunction, after
restricting to the constant scalar sections of the two normalized encodings.
Source: Stacks 03EK, 06YY, internal_section_scalar_adjunction
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
structure FiniteExceptionalEncodingRestriction {ell : ℕ} {T : Scheme.{u}}
    {A B : FiniteExceptionalRing.{u} ell} (φ : A.ring →+* B.ring)
    (eA : finiteExceptionalEncoding A T) (eB : finiteExceptionalEncoding B T) where
  comparison :
    Mod.comap (finiteExceptionalSchemeCoefficientMap φ T) ⋙
        (finiteExceptionalUnderivedEncoding eA).functor ≅
      (finiteExceptionalUnderivedEncoding eB).functor ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ.ulift
  sections : ∀ (N : ModuleRingedComparison.internalModules B.coefficient.X T)
    (V : T.ProEtᵒᵖ)
    (x : ((finiteExceptionalUnderivedEncoding eA).functor.obj
      ((Mod.comap (finiteExceptionalSchemeCoefficientMap φ T)).obj N)).obj.obj V),
    HEq (((comparison.hom.app N).hom.app V) x) x

/-- Localization of the identity-on-sections restriction comparison. There is no
independent derived restriction isomorphism to choose.
Source: Stacks 06YY, internal_section_scalar_adjunction
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def FiniteExceptionalEncodingRestriction.derived {ell : ℕ} {T : Scheme.{u}}
    {A B : FiniteExceptionalRing.{u} ell} {φ : A.ring →+* B.ring}
    {eA : finiteExceptionalEncoding A T} {eB : finiteExceptionalEncoding B T}
    (r : FiniteExceptionalEncodingRestriction φ eA eB) :
    (Mod.comap (finiteExceptionalSchemeCoefficientMap φ T)).mapDerivedCategory ⋙
        (finiteExceptionalEncodingDerived eA).functor ≅
      (finiteExceptionalEncodingDerived eB).functor ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ.ulift :=
  letI : TopologicalSpace A.ring := ⊥
  letI : DiscreteTopology A.ring := discreteTopology_bot _
  letI : TopologicalSpace B.ring := ⊥
  letI : DiscreteTopology B.ring := discreteTopology_bot _
  letI : (finiteExceptionalUnderivedEncoding eA).functor.Additive :=
    inferInstanceAs (eA.ordinary.functor ⋙ eA.fixed.functor).Additive
  letI : (finiteExceptionalUnderivedEncoding eB).functor.Additive :=
    inferInstanceAs (eB.ordinary.functor ⋙ eB.fixed.functor).Additive
  Functor.mapDerivedCategorySquareIso r.comparison

/-- The fixed-coefficient scalar adjunction supplied by the current derived
change-of-rings theorem, with its actual exact restriction functor.
Source: Stacks 06YY, 06XN (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalScalarAdjunction {D : Type (u + 1)} [Category.{u} D]
    [EssentiallySmall.{u + 1} D] (J : GrothendieckTopology D)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) :
    Sheaf.fixedCoefficientDerivedScalarExtension J φ ⊣ Sheaf.derivedRestrictScalars J φ :=
  letI := Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint J φ
  Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ)

/-- The scalar associator is the left-adjoint comparison of the actual
restriction-composition isomorphism, with no independent choice of coherence.
Source: Stacks 06YY (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalScalarComposition {D : Type (u + 1)} [Category.{u} D]
    [EssentiallySmall.{u + 1} D] (J : GrothendieckTopology D)
    {R S V : Type (u + 1)} [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ) :
    Sheaf.fixedCoefficientDerivedScalarExtension J φ ⋙
        Sheaf.fixedCoefficientDerivedScalarExtension J ψ ≅
      Sheaf.fixedCoefficientDerivedScalarExtension J χ :=
  Adjunction.leftAdjointCompIso (finiteExceptionalScalarAdjunction J φ)
    (finiteExceptionalScalarAdjunction J ψ) (finiteExceptionalScalarAdjunction J χ)
    (Sheaf.derivedRestrictScalarsCompIso J h)

/-- The site/restriction square comes from sectionwise commutation of site
restriction and coextension of scalars, conjugated through their specified adjunctions.
Source: Stacks 03D2 (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalSiteRestriction (T : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) :
    comparisonUpperStar (ModuleCat.{u + 1} S) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ ≅
      Sheaf.restrictScalars T.smallEtaleTopology φ ⋙
        comparisonUpperStar (ModuleCat.{u + 1} R) T :=
  ((conjugateIsoEquiv
    ((comparisonAdjunction (ModuleCat.{u + 1} S) T).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ))
    ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).comp
      (comparisonAdjunction (ModuleCat.{u + 1} R) T))).symm (Iso.refl _)).symm

/-- Exact localization of the specified site/restriction square.
Source: Stacks 03D2, 06YY (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalDerivedSiteRestriction (T : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} S) T)
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteExceptionalSiteRestriction T φ) ≪≫
    Functor.mapDerivedCategoryCompIso (Sheaf.restrictScalars T.smallEtaleTopology φ)
      (comparisonUpperStar (ModuleCat.{u + 1} R) T)

/-- The site/scalar reduction map is the actual mate of the derived restriction
square under the two current fixed-coefficient scalar adjunctions. Only this
specified map is needed for the coordinate normalization; it is not a free isomorphism.
Source: Stacks 07A4 (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalSiteScalarMap (T : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ⋙
        Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology T) φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory :=
  ((mateEquiv
    (G := (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory)
    (H := (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory)
    (finiteExceptionalScalarAdjunction T.smallEtaleTopology φ)
    (finiteExceptionalScalarAdjunction (Scheme.ProEt.topology T) φ)).symm
    (TwoSquare.mk _ _ _ _ (finiteExceptionalDerivedSiteRestriction T φ).inv)).natTrans

/-- Coordinates for the finite internal/ordinary and etale/pro-etale comparisons.
The functor square specifies the site comparison itself. The constructibility clause
identifies both finite-Tor full subcategories. All fields are witnesses in the theorem's
conclusion, not additional hypotheses on the geometry or the coefficient ring.
Source: blueprint clause (1), finite comparison
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
structure FiniteExceptionalCoordinates (ell : ℕ) (T : Scheme.{u}) where
  encoding : ∀ A : FiniteExceptionalRing.{u} ell, finiteExceptionalEncoding A T
  equivalence : ∀ A : FiniteExceptionalRing.{u} ell, A.etale T ≌ A.localizing T
  site : ∀ A : FiniteExceptionalRing.{u} ell,
    (equivalence A).functor ⋙ (localizingClosureProEtale A.coefficient.X T).ι ⋙
        (finiteExceptionalEncodingDerived (encoding A)).functor ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A.ring)) T).mapDerivedCategory
  ctf : ∀ (A : FiniteExceptionalRing.{u} ell) (K : A.etale T),
    (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A.ring) T K ∧
      _root_.DerivedCategory.finiteTorAmplitude _ K) ↔
    (constantModelBoundedConstructible A.coefficient.X T
        ((equivalence A).functor.obj K).obj ∧
      _root_.DerivedCategory.finiteTorAmplitude _ ((equivalence A).functor.obj K).obj)

/-- Ordinary etale compact support in the chosen compactification.
Source: blueprint clause (1), choice of etale compactification
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev finiteExceptionalEtaleSupport {ell : ℕ} (A : FiniteExceptionalRing.{u} ell)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1} A.ring)) c

/-- Transport of the actual etale compact-support functor to the same condensed closure.
Source: blueprint definition of F_A
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalTransportedSupport {ell : ℕ} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (U : FiniteExceptionalCoordinates ell X) (V : FiniteExceptionalCoordinates ell Y)
    (A : FiniteExceptionalRing.{u} ell) (c : Compactification f) :=
  (U.equivalence A).inverse ⋙ finiteExceptionalEtaleSupport A c ⋙ (V.equivalence A).functor

/-- Transport of a chosen ordinary etale exceptional adjoint.
Source: blueprint definition of G_A
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalTransportedRight {ell : ℕ} {X Y : Scheme.{u}}
    (U : FiniteExceptionalCoordinates ell X) (V : FiniteExceptionalCoordinates ell Y)
    (A : FiniteExceptionalRing.{u} ell) (J : A.etale Y ⥤ A.etale X) :=
  (V.equivalence A).inverse ⋙ J ⋙ (U.equivalence A).functor

/-- The transported adjunction has exactly the transported Hom bijections.
Source: blueprint transported adjunction
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalTransportedAdjunction {ell : ℕ} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (U : FiniteExceptionalCoordinates ell X) (V : FiniteExceptionalCoordinates ell Y)
    (A : FiniteExceptionalRing.{u} ell) (c : Compactification f)
    (J : A.etale Y ⥤ A.etale X) (adj : finiteExceptionalEtaleSupport A c ⊣ J) :
    finiteExceptionalTransportedSupport U V A c ⊣ finiteExceptionalTransportedRight U V A J :=
  ((U.equivalence A).symm.toAdjunction.comp adj).comp (V.equivalence A).toAdjunction

/-- The scalar coordinate isomorphism is fixed by the identity-on-sections restriction
comparison and the two specified scalar-adjunction units. Thus its inverse is the
unique transpose sending b tensor m to b tensor m. The final equation pins the site
transport to finiteExceptionalSiteScalarMap, so no scalar identification can be twisted.
Source: blueprint coefficient compatibility
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
structure FiniteExceptionalScalarCoordinates {ell : ℕ} {T : Scheme.{u}}
    (U : FiniteExceptionalCoordinates ell T) {A B : FiniteExceptionalRing.{u} ell}
    (φ : A.ring →+* B.ring) where
  preserves : ∀ K : A.localizing T, localizingClosureProEtale B.coefficient.X T
    ((scalarSixChange (finiteExceptionalCoefficientMap φ) T).obj K.obj)
  encodingRestriction : FiniteExceptionalEncodingRestriction φ (U.encoding A) (U.encoding B)
  encodingComparison :
    scalarSixChange (finiteExceptionalCoefficientMap φ) T ⋙
        (finiteExceptionalEncodingDerived (U.encoding B)).functor ≅
      (finiteExceptionalEncodingDerived (U.encoding A)).functor ⋙
        Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology T) φ.ulift
  encoding_unit : ∀ K : A.ambient T,
    (finiteExceptionalScalarAdjunction (Scheme.ProEt.topology T) φ.ulift).unit.app
          ((finiteExceptionalEncodingDerived (U.encoding A)).functor.obj K) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ.ulift).map
        (encodingComparison.inv.app K) =
    (finiteExceptionalEncodingDerived (U.encoding A)).functor.map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (finiteExceptionalSchemeCoefficientMap φ T)).unit.app K) ≫
      encodingRestriction.derived.hom.app
        ((scalarSixChange (finiteExceptionalCoefficientMap φ) T).obj K)
  comparison :
    (U.equivalence A).functor ⋙ (localizingClosureProEtale B.coefficient.X T).lift
        ((localizingClosureProEtale A.coefficient.X T).ι ⋙
          scalarSixChange (finiteExceptionalCoefficientMap φ) T) preserves ≅
      Sheaf.fixedCoefficientDerivedScalarExtension T.smallEtaleTopology φ.ulift ⋙
        (U.equivalence B).functor
  comparison_normalization : ∀ L : A.etale T,
    (finiteExceptionalEncodingDerived (U.encoding B)).functor.map
        ((comparison.hom.app L).hom) ≫
      (U.site B).hom.app
        ((Sheaf.fixedCoefficientDerivedScalarExtension T.smallEtaleTopology φ.ulift).obj L) =
    encodingComparison.hom.app ((U.equivalence A).functor.obj L).obj ≫
      (Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology T) φ.ulift).map
        ((U.site A).hom.app L) ≫
      (finiteExceptionalSiteScalarMap T φ.ulift).app L

/-- The scalar functor restricted to the same localizing categories.
Source: blueprint Q_T = B_T tensor^L_{A_T} -
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def FiniteExceptionalScalarCoordinates.change {ell : ℕ} {T : Scheme.{u}}
    {U : FiniteExceptionalCoordinates ell T} {A B : FiniteExceptionalRing.{u} ell}
    {φ : A.ring →+* B.ring} (s : FiniteExceptionalScalarCoordinates U φ) :=
  (localizingClosureProEtale B.coefficient.X T).lift
    ((localizingClosureProEtale A.coefficient.X T).ι ⋙
      scalarSixChange (finiteExceptionalCoefficientMap φ) T) s.preserves

/-- The induced scalar identification for an arbitrary condensed localizing object.
Source: blueprint scalar/site identifications
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def FiniteExceptionalScalarCoordinates.at {ell : ℕ} {T : Scheme.{u}}
    {U : FiniteExceptionalCoordinates ell T} {A B : FiniteExceptionalRing.{u} ell}
    {φ : A.ring →+* B.ring} (s : FiniteExceptionalScalarCoordinates U φ)
    (K : A.localizing T) :
    s.change.obj K ≅ (U.equivalence B).functor.obj
      ((Sheaf.fixedCoefficientDerivedScalarExtension T.smallEtaleTopology φ.ulift).obj
        ((U.equivalence A).inverse.obj K)) :=
  s.change.mapIso ((U.equivalence A).counitIso.app K).symm ≪≫
    s.comparison.app ((U.equivalence A).inverse.obj K)

/-- The genuine transported etale proper-counit/open-tensor map q, with both scalar
coordinate isomorphisms inserted explicitly.
Source: blueprint definition of q_phi
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalQ {ell : ℕ} {X Y : Scheme.{u}} {f : X ⟶ Y}
    {U : FiniteExceptionalCoordinates ell X} {V : FiniteExceptionalCoordinates ell Y}
    {A B : FiniteExceptionalRing.{u} ell} (φ : A.ring →+* B.ring)
    (sX : FiniteExceptionalScalarCoordinates U φ) (sY : FiniteExceptionalScalarCoordinates V φ)
    (c : Compactification f) (K : A.localizing X) :
    sY.change.obj ((finiteExceptionalTransportedSupport U V A c).obj K) ⟶
      (finiteExceptionalTransportedSupport U V B c).obj (sX.change.obj K) :=
  sY.comparison.hom.app ((finiteExceptionalEtaleSupport A c).obj
      ((U.equivalence A).inverse.obj K)) ≫
    (V.equivalence B).functor.map ((Etale.compactScalarMap φ.ulift c).app
      ((U.equivalence A).inverse.obj K)) ≫
    (V.equivalence B).functor.map ((finiteExceptionalEtaleSupport B c).map
      ((U.equivalence B).unitIso.hom.app
          ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ.ulift).obj
            ((U.equivalence A).inverse.obj K)) ≫
        (U.equivalence B).inverse.map (sX.at K).inv))

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

open CondensedRing

/-- The specified internal/fixed compact-support comparison. Both factors are the
normalized encoding comparisons, computed on the given open/proper factorization.
Source: finite coefficient comparison, proof steps 11--12
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalEncodingSupport {ell : ℕ} (A : FiniteExceptionalRing.{u} ell)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (eX : finiteExceptionalEncoding A X) (eY : finiteExceptionalEncoding A Y)
    (eZ : finiteExceptionalEncoding A c.Z) :
    CondensedRing.rightDerivedLowerShriekOfCompactification A.coefficient.X c ⋙
        (finiteExceptionalEncodingDerived eY).functor ≅
      (finiteExceptionalEncodingDerived eX).functor ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A.ring)) c :=
  letI : TopologicalSpace A.ring := ⊥
  letI : DiscreteTopology A.ring := discreteTopology_bot _
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (encodingDerivedPushforwardComparison A.ring c.g eY eZ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (encodingDerivedOpenShriekComparison A.ring c.i eZ eX) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

namespace AlgebraicGeometry.ProEtale.CondensedRing

open FiniteDiscreteOrdinary (finiteExceptionalEncodingSupport)

/-- Canonical tensor associator on the localizing full subcategories. The equality
only changes the spelling of postcomposition of the actual coefficient maps.
Source: blueprint coefficient cocycle
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalTower {ell : ℕ} {T : Scheme.{u}}
    {U : FiniteExceptionalCoordinates ell T} {A B C : FiniteExceptionalRing.{u} ell}
    (φ : A.ring →+* B.ring) (ψ : B.ring →+* C.ring)
    (sφ : FiniteExceptionalScalarCoordinates U φ)
    (sψ : FiniteExceptionalScalarCoordinates U ψ)
    (sψφ : FiniteExceptionalScalarCoordinates U (ψ.comp φ))
    (h : finiteExceptionalCoefficientMap φ ≫ finiteExceptionalCoefficientMap ψ =
      finiteExceptionalCoefficientMap (ψ.comp φ)) (K : A.localizing T) :
    sψ.change.obj (sφ.change.obj K) ≅ sψφ.change.obj K :=
  ObjectProperty.isoMk _
    ((scalarSixTower (finiteExceptionalCoefficientMap φ)
        (finiteExceptionalCoefficientMap ψ) T).app K.obj ≪≫
      (eqToIso (congrArg (fun a ↦ scalarSixChange a T) h)).app K.obj)

/-- Canonical tensor unit on the localizing category, with the unchanged identity
coefficient map. Source: blueprint identity coefficient maps
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
def finiteExceptionalUnit {ell : ℕ} {T : Scheme.{u}}
    {U : FiniteExceptionalCoordinates ell T} (A : FiniteExceptionalRing.{u} ell)
    (s : FiniteExceptionalScalarCoordinates U (RingHom.id A.ring))
    (h : finiteExceptionalCoefficientMap (RingHom.id A.ring) = 𝟙 A.coefficient)
    (K : A.localizing T) : s.change.obj K ≅ K :=
  ObjectProperty.isoMk _
    ((eqToIso (congrArg (fun a ↦ scalarSixChange a T) h)).app K.obj ≪≫
      (scalarChangeUnit A.coefficient T).app K.obj)

/-- The concrete choices introduced by the statement: finite site coordinates,
Brown adjoints of the actual condensed compact-support functors, and ordinary etale
right adjoints. These are data in the conclusion of the theorem, never extra
assumptions on the schemes or on coefficient maps.
Source: blueprint clause (1), finite coefficients
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
structure FiniteExceptionalModels (ell : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  source : FiniteExceptionalCoordinates ell X
  target : FiniteExceptionalCoordinates ell Y
  middle : ∀ A : FiniteExceptionalRing.{u} ell, finiteExceptionalEncoding A c.Z
  brown : ∀ A : FiniteExceptionalRing.{u} ell, ScalarExceptionalAdjoint A.coefficient c
  ordinary : ∀ A : FiniteExceptionalRing.{u} ell, A.etale Y ⥤ A.etale X
  ordinaryAdjunction : ∀ A : FiniteExceptionalRing.{u} ell,
    finiteExceptionalEtaleSupport A c ⊣ ordinary A
  scalarSource : ∀ {A B : FiniteExceptionalRing.{u} ell} (φ : A.ring →+* B.ring),
    FiniteExceptionalScalarCoordinates source φ
  scalarTarget : ∀ {A B : FiniteExceptionalRing.{u} ell} (φ : A.ring →+* B.ring),
    FiniteExceptionalScalarCoordinates target φ
  coefficient_comp : ∀ {A B C : FiniteExceptionalRing.{u} ell}
    (φ : A.ring →+* B.ring) (ψ : B.ring →+* C.ring),
    finiteExceptionalCoefficientMap φ ≫ finiteExceptionalCoefficientMap ψ =
      finiteExceptionalCoefficientMap (ψ.comp φ)
  coefficient_id : ∀ A : FiniteExceptionalRing.{u} ell,
    finiteExceptionalCoefficientMap (RingHom.id A.ring) = 𝟙 A.coefficient

namespace FiniteExceptionalModels

variable {ell : ℕ} {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (M : FiniteExceptionalModels ell c)

/-- Condensed compact support on the localizing closure.
Source: blueprint F_A^c (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev Fc (A : FiniteExceptionalRing.{u} ell) :=
  localizingLowerShriek A.coefficient.X c (M.brown A).localizing

/-- The transported ordinary etale compact-support functor.
Source: blueprint F_A (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev F (A : FiniteExceptionalRing.{u} ell) :=
  finiteExceptionalTransportedSupport M.source M.target A c

/-- The transported ordinary etale exceptional functor.
Source: blueprint G_A (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev G (A : FiniteExceptionalRing.{u} ell) :=
  finiteExceptionalTransportedRight M.source M.target A (M.ordinary A)

/-- The actual transported ordinary etale adjunction.
Source: blueprint F_A adjoint to G_A
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev adjunction (A : FiniteExceptionalRing.{u} ell) :=
  finiteExceptionalTransportedAdjunction M.source M.target A c
    (M.ordinary A) (M.ordinaryAdjunction A)

/-- The source derived tensor extension, restricted to the localizing closure.
Source: blueprint Q_X (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev QX {A B : FiniteExceptionalRing.{u} ell} (φ : A.ring →+* B.ring) :=
  (M.scalarSource φ).change

/-- The target derived tensor extension, restricted to the localizing closure.
Source: blueprint Q_Y (blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev QY {A B : FiniteExceptionalRing.{u} ell} (φ : A.ring →+* B.ring) :=
  (M.scalarTarget φ).change

/-- The source derived tensor associator, not a freely chosen coherence.
Source: blueprint coefficient cocycle
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev towerX {A B C : FiniteExceptionalRing.{u} ell}
    (φ : A.ring →+* B.ring) (ψ : B.ring →+* C.ring) (K : A.localizing X) :=
  finiteExceptionalTower φ ψ (M.scalarSource φ) (M.scalarSource ψ)
    (M.scalarSource (ψ.comp φ)) (M.coefficient_comp φ ψ) K

/-- The target derived tensor associator, not a freely chosen coherence.
Source: blueprint coefficient cocycle
(blueprint: lem-sf-condensed-finite-exceptional-comparison). -/
abbrev towerY {A B C : FiniteExceptionalRing.{u} ell}
    (φ : A.ring →+* B.ring) (ψ : B.ring →+* C.ring) (K : A.localizing Y) :=
  finiteExceptionalTower φ ψ (M.scalarTarget φ) (M.scalarTarget ψ)
    (M.scalarTarget (ψ.comp φ)) (M.coefficient_comp φ ψ) K

end FiniteExceptionalModels

set_option maxHeartbeats 2000000 in
-- Elaborate the scalar coordinate cocycles and all counit equations in one witness structure.
end AlgebraicGeometry.ProEtale.CondensedRing
