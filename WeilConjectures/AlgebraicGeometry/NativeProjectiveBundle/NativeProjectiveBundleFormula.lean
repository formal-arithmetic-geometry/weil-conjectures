/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalClass
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateTransitivity
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.StrictCoefficientProperReduction
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeDirectComparison
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.CommonFieldLatticeGenerators
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.SmoothFibreRegularLocal
public import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
public import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
public import Mathlib.RingTheory.Smooth.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Regular
public import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

public import WeilConjectures.AlgebraicGeometry.ProEtaleKummerLimitBoundary
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Algebra
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
public import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
public import WeilConjectures.CategoryTheory.SiteMorphismComposition
public import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
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
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.GroupTheory.QuotientGroup.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Topology.Connected.Separation
import WeilConjectures.RingTheory.StrictlyHenselianOfDimensionZero
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.Separable
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.Compactification.OnePoint.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactKunnethSectionUnit.CompactKunnethSectionUnit
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
import Mathlib.CategoryTheory.Monoidal.CommMon_
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Data.ZMod.Basic
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RelativeKunneth.CondensedRelativeKunneth
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections

/-! # The native projective-bundle formula
Source: latest blueprint, thm-pur-projective-bundle-formula, Step 2.
(blueprint: thm-pur-projective-bundle-formula). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeProjectiveBundle

variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

/-- The ordered tensor power of the shifted root-normalized native Tate line.
Source: blueprint Step 2 (blueprint: thm-pur-projective-bundle-formula). -/
def positive (T : Scheme.{u}) : ℕ → c.derived ell T
  | 0 => 𝟙_ _
  | a + 1 => positive T a ⊗ c.derivedLine ell T 1

/-- The zero negative power is the unit; other powers use the derived dual.
For an invertible Tate line this is precisely Lambda(-a)[-2a].
Source: blueprint displayed source (blueprint: thm-pur-projective-bundle-formula). -/
def summand (T : Scheme.{u}) : ℕ → c.derived ell T
  | 0 => 𝟙_ _
  | a + 1 => (ihom (positive ell c T (a + 1))).obj (𝟙_ _)

/-- Iterate the existing ordered-cup construction in the native derived tensor category.
Source: blueprint Step 2 (blueprint: thm-pur-projective-bundle-formula). -/
def cupPower (T : Scheme.{u}) (h : (𝟙_ (c.derived ell T)) ⟶ c.derivedLine ell T 1) :=
  WeilConjectures.projectiveBundleOrderedCup (curriedTensor (c.derived ell T))
    (𝟙_ _) (c.derivedLine ell T 1) (positive ell c T) (Iso.refl _)
    (fun _ ↦ Iso.refl _) (λ_ (𝟙_ _)).inv h

/-- Evaluate a cup power against the inverse shifted Tate line; the zeroth is identity.
Source: blueprint component construction (blueprint: thm-pur-projective-bundle-formula). -/
def evaluate (T : Scheme.{u}) (h : (𝟙_ (c.derived ell T)) ⟶ c.derivedLine ell T 1) :
    (a : ℕ) → summand ell c T a ⟶ 𝟙_ _
  | 0 => 𝟙 _
  | a + 1 => (λ_ _).inv ≫ (cupPower ell c T h (a + 1) ⊗ₘ 𝟙 _) ≫
      (ihom.ev (positive ell c T (a + 1))).app (𝟙_ _)

/-- Pullback of positive powers by the monoidal tensorator and root-normalized comparison.
Source: blueprint base change (blueprint: thm-pur-projective-bundle-formula). -/
def positivePullback {T T' : Scheme.{u}} (f : T' ⟶ T)
    (p : PurityTransport.LinePullCoordinates ell c f) :
    (a : ℕ) → (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor.obj
      (positive ell c T a) ≅ positive ell c T' a
  | 0 => CondensedRing.leftDerivedUpperStarUnitIso (c.obj ell) f
  | a + 1 =>
      ((CondensedRing.leftDerivedUpperStarTensorIso (c.obj ell) f).app
        (positive ell c T a)).app (c.derivedLine ell T 1) ≪≫
      tensorIso (positivePullback f p a) (p.derived ell 1)

/-- Pullback on the inverse Tate power is the transpose of pulled-back evaluation.
Source: blueprint Tate identifications (blueprint: thm-pur-projective-bundle-formula). -/
def summandPullback {T T' : Scheme.{u}} (f : T' ⟶ T)
    (p : PurityTransport.LinePullCoordinates ell c f) :
    (a : ℕ) → (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor.obj
      (summand ell c T a) ⟶ summand ell c T' a
  | 0 => (CondensedRing.leftDerivedUpperStarUnitIso (c.obj ell) f).hom
  | a + 1 => (ihom.adjunction (positive ell c T' (a + 1))).homEquiv _ _
      (((positivePullback ell c f p (a + 1)).inv ⊗ₘ 𝟙 _) ≫
        (((CondensedRing.leftDerivedUpperStarTensorIso (c.obj ell) f).app
          (positive ell c T (a + 1))).app (summand ell c T (a + 1))).inv ≫
        (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor.map
          ((ihom.ev (positive ell c T (a + 1))).app (𝟙_ _)) ≫
        (CondensedRing.leftDerivedUpperStarUnitIso (c.obj ell) f).hom)

/-- The component is the specified pullback-pushforward adjunct of the cup evaluation.
Source: blueprint Step 2 (blueprint: thm-pur-projective-bundle-formula). -/
def component {T B : Scheme.{u}} (f : T ⟶ B)
    (p : PurityTransport.LinePullCoordinates ell c f)
    (h : (𝟙_ (c.derived ell T)) ⟶ c.derivedLine ell T 1) (a : ℕ) :
    summand ell c B a ⟶
      (CondensedRing.lowerStar (c.obj ell) f).rightDerivedFunctor.obj (𝟙_ _) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj ell) f).homEquiv _ _
    (summandPullback ell c f p a ≫ evaluate ell c T h a)

/-- The actual finite coproduct map with the specified adjoint components.
Source: blueprint displayed map (blueprint: thm-pur-projective-bundle-formula). -/
def bundleMap {T B : Scheme.{u}} (f : T ⟶ B)
    (p : PurityTransport.LinePullCoordinates ell c f)
    (h : (𝟙_ (c.derived ell T)) ⟶ c.derivedLine ell T 1) (n : ℕ) :
    (∐ fun a : Fin (n + 1) ↦ summand ell c B a.val) ⟶
      (CondensedRing.lowerStar (c.obj ell) f).rightDerivedFunctor.obj (𝟙_ _) :=
  Sigma.desc (fun a ↦ component ell c f p h a.val)

/-- Proper exchange followed by the native coefficient-unit pullback identification.
Source: blueprint base-change equality (blueprint: thm-pur-projective-bundle-formula). -/
def targetBaseChange {T B T' B' : Scheme.{u}} {f : T ⟶ B} {f' : T' ⟶ B'}
    {g : B' ⟶ B} {v : T' ⟶ T} (sq : CommSq v f' f g) :
    (CondensedRing.upperStar (c.obj ell) g).leftDerivedFunctor.obj
      ((CondensedRing.lowerStar (c.obj ell) f).rightDerivedFunctor.obj (𝟙_ _)) ⟶
      (CondensedRing.lowerStar (c.obj ell) f').rightDerivedFunctor.obj (𝟙_ _) :=
  (CondensedRing.baseChangeMap (c.obj ell) sq).app (𝟙_ _) ≫
    (CondensedRing.lowerStar (c.obj ell) f').rightDerivedFunctor.map
      (CondensedRing.leftDerivedUpperStarUnitIso (c.obj ell) v).hom

/-- Identify the constructed inverse shifted power with the recorded signed Tate line.
Source: blueprint displayed source and sk-def-sp-tate-twist
(blueprint: thm-pur-projective-bundle-formula).
Proof: on a compatible primitive-root cover the first Tate line is the coefficient
unit. Tensor powers are flat lines, and their internal duals are again flat lines.
Consequently underived sheaf Hom computes their derived Hom. The tensor/shift
comparison identifies the ordered positive power with Lambda(a)[2a], and its dual
with the recorded sheaf dual Lambda(-a)[-2a]. At zero use the unit comparison.
These comparisons descend because they are evaluation maps, independent of the
chosen local primitive root. -/
theorem summand_signedTwist (T : Scheme.{u})
    [∀ x : T, Invertible (ell : T.residueField x)] (a : ℕ) :
    Nonempty (summand ell c T a ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (spInternalSignedTwist T (condensedRingObj (c.obj ell) T)
          (c.firstLine ell T) (-(a : ℤ))))⟦-(2 * (a : ℤ))⟧) := by
  sorry

end AlgebraicGeometry.ProEtale.NativeProjectiveBundle

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry.ProEtale.NativeProjectiveBundle

end WeilConjectures.PurityFiniteSetting
