/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothCoefficientArrows
public import WeilConjectures.SecSmoothPurity.ReductionExceptional
public import WeilConjectures.SecSmoothPurity.FiniteGeneralRing
import WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtension
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom

import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
import WeilConjectures.SecSmoothPurity.IntrinsicCompactSupportRestriction
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjointComparisons
import WeilConjectures.AlgebraicGeometry.FiniteFreeProjectionExchange
import WeilConjectures.AlgebraicGeometry.CanonicalFiniteLevelCompactSupportBaseChange
import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.AlgebraicGeometry.FiniteCompactProjectionFormula
import WeilConjectures.AlgebraicGeometry.SfPreservationClass
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassScalarFaithfulness
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctMate
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
import WeilConjectures.AlgebraicGeometry.ProjectiveLineConstantCoefficientGenerator
import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteGeometricPointHomology
import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1FibreHomologyCard
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalTriangles
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalIntegral
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummerSupplement
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits
import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalPicard
import WeilConjectures.AlgebraicGeometry.P1DiagonalLocalIdeal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedChernNormalization
import WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.SectionProjectionUnitSupplement
import Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalCoefficientTriangles
import WeilConjectures.AlgebraicGeometry.EtaleSupportedDiagonalUnitSupplement
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalTriangles
import WeilConjectures.AlgebraicGeometry.EtaleProperSectionContraction
import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
import WeilConjectures.CategoryTheory.AdjunctionUnitTransport
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionIntegral
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.ConstructibleSheaf.LisseRankOne
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.GroupTheory.Torsion
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
import WeilConjectures.AlgebraicGeometry.TorsionAssembly
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorization
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp
import WeilConjectures.AlgebraicGeometry.EtaleKunnethSymmetricFactorization
import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
import WeilConjectures.AlgebraicGeometry.EtaleKunnethTensorSymmetry
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRightRoute
import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceNormalization
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
import WeilConjectures.AlgebraicGeometry.EtaleEvenLineSelfSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
import Mathlib.Tactic.SuppressCompilation
import WeilConjectures.AlgebraicGeometry.EtaleLineFlatBraiding
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.EtaleSecondCoordinateContraction
import WeilConjectures.AlgebraicGeometry.EtaleTraceBaseChangeEvaluation
import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceTensorInterchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCounitCoefficient
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceEvaluationNormalization
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalTraceCoordinates
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux
import WeilConjectures.AlgebraicGeometry.EtaleChartExchangePasting
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistComposition
import WeilConjectures.CategoryTheory.ShiftedCompositeComparison
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Ring.Int.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleExactExchangeComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceScalarSquare
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounitComparisons
import WeilConjectures.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMapsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedPairingPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.AlgebraicGeometry.EtaleFlatSingleTensorCompatibilityDataSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorNaturality
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorAssociativity
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackCounit
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
import WeilConjectures.CategoryTheory.FlatPairingAssociativityAssembly
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.FlatPairingPullbackAssembly
import WeilConjectures.AlgebraicGeometry.DerivedPairingOppositeShiftsPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPairing
import WeilConjectures.AlgebraicGeometry.FiniteTwistFlatEvaluationPullback
import WeilConjectures.AlgebraicGeometry.FlatSinglePairingSymmetricPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDerivedRightUnitPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedFactorComparisons
import WeilConjectures.AlgebraicGeometry.FiniteShiftedLineSquare
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalFirstCoordinateExchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalSecondCoordinateExchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.FiniteFreeCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.AffineSpaceTopTrace
import WeilConjectures.Targets.VectorBundlePurity
import WeilConjectures.AlgebraicGeometry.VectorBundleIntegration
import WeilConjectures.AlgebraicGeometry.VectorBundlePurity
import WeilConjectures.AlgebraicGeometry.DiagonalRegularPureCodimension
import WeilConjectures.AlgebraicGeometry.PurityDiagonalDualizingObject
import WeilConjectures.AlgebraicGeometry.PuritySectionInvariantIntrinsic
import WeilConjectures.AlgebraicGeometry.PurityDiagonalBaseChangeCompared
import WeilConjectures.AlgebraicGeometry.PurityDncInvariance
import WeilConjectures.SecSmoothPurity.PurityDncCoefficientTransport
import WeilConjectures.AlgebraicGeometry.SmoothPurityMap

/-! # Finite smooth trace and extension of coefficients

Source: main-20261015 blueprint, sec-smooth-purity/sk-thm-purity-transport,
proof Steps 1 and 3 (blueprint: lem-pur-finite-universal-smooth-trace).

The trace is the recorded normalized smooth trace. Its tensor-unit and shift
presentation is changed by canonical isomorphisms only. Both root comparisons
below retain the generator and derived-counit normalizations of the published API.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The prime-field stage in the same fixed coefficient closure, at positive level r.
Source: purity transport, A=Z/ell^r (blueprint: lem-pur-finite-universal-smooth-trace). -/
abbrev primeTraceSetting (P : PurityFiniteSetting.{u}) (r : ℕ) (hr : 1 ≤ r) :
    PurityFiniteSetting.{u} where
  field := P.field
  coefficients := P.coefficients
  extension := ⊥
  level := r
  level_pos := hr

/-- The recorded shifted coefficient line in intrinsic constant-ring coordinates.
Source: purity transport, T_A (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceTwist (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :=
  (sfIntrinsicDerivedEquivalence X P.Ring).functor.obj (P.diagonalTwist X d)

/-- Canonical pullback of the unit in the fixed module presentation: use the realization
unit, the site/pullback comparison and the ordinary constant-object comparison.
Source: purity transport, T_A (blueprint: lem-pur-finite-universal-smooth-trace). -/
def tracePulledUnitIso (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (P.smoothPurityPullback f).obj
        ((sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (coefficientUnit P Y)) ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit P.Coefficient X) :=
  P.smoothPurityPullbackComparison f
      ((sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (coefficientUnit P Y))
      (Etale.ordinaryFiniteUnit P.Coefficient Y)
      ((sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app _) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (Etale.ordinaryFiniteUnitPullback P.Coefficient f)


/-- Remove the constant unit in the ordinary presentation using its canonical left unitor.
Source: purity transport Step 2 (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceEtaleUnitIso (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule A X) :
    ((Etale.ordinaryFiniteTensor A X).obj (Etale.ordinaryFiniteUnit A X)).obj K ≅ K :=
  ((Etale.ordinaryFiniteTensor A X).mapIso
    (smoothPurityUnitIso A X)).app K ≪≫
    Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X K


/-- Transport the ordinary left unitor through the canonical site tensor comparison.
Source: purity transport Step 2 (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceComparedUnitIso (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :
    ((smoothPurityTensor P.Coefficient X).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient X))).obj (P.diagonalTwist X d) ≅
            P.diagonalTwist X d :=
  (smoothPurityComparisonTensor P.Coefficient X
      (Etale.ordinaryFiniteUnit P.Coefficient X) (P.diagonalTwistEtale X d)).symm ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (traceEtaleUnitIso P.Coefficient X (P.diagonalTwistEtale X d))


/-- Remove the explicit unit factor in the trace's tensor presentation, using the
site/tensor comparison and the ordinary left unitor. No orientation is chosen.
Source: purity transport, T_A (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceTensorUnitIso (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : ℕ) :
    P.smoothPurityTensorSource f d (coefficientUnit P Y) ≅ P.diagonalTwist X d :=
  ((smoothPurityTensor P.Coefficient X).mapIso
      (tracePulledUnitIso P f)).app (P.diagonalTwist X d) ≪≫
    traceComparedUnitIso P X d


/-- The actual source object of smoothTrace, before removing its shifts and unit.
Source: recorded smooth trace (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceSource (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :=
  (sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
    ((((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj
        ((sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (coefficientUnit P Y)))).obj
          ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧))⟦2 * (d : ℤ)⟧)


/-- Canonical identification of the recorded trace source with A_X(d)[2d].
Source: purity transport, unit-coefficient trace
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceSourceIso (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    traceSource P f d ≅ traceTwist P X d :=
  (sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso
    (P.smoothPurityReassociation X d
        ((P.smoothPurityPullback f).obj
          ((sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (coefficientUnit P Y))) ≪≫
      traceTensorUnitIso P f d)


/-- The canonical extension of the shifted Tate line. First enlarge the prime-power
root exponent by the inverse of its normalized power-map comparison; then use the
coefficient extension fixed on scalar/root generators. Site realization supplies the
outside comparison. Source: purity transport Steps 1 and 3
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceTwistExtensionIso (P Q : PurityFiniteSetting.{u}) (φ : Q.Ring →+* P.Ring)
    (T : Scheme.{u}) (d : ℕ) (hA : (P.diagonalExponent : Q.Coefficient) = 0)
    (a : finiteEtaleTateLine T P.diagonalExponent Q.Coefficient hA ≅
      finiteEtaleTateLine T Q.diagonalExponent Q.Coefficient Q.diagonalExponent_annihilates)
    (σ : Etale.FiniteSmoothPurity.CoefficientLineComparison φ.ulift
      P.diagonalExponent P.diagonalExponent hA P.diagonalExponent_annihilates T) :
    (scalarExtensionFunctor φ T).obj (traceTwist Q T d) ≅ traceTwist P T d :=
  (reductionSiteScalarIso φ T).app (Q.diagonalTwistEtale T d) ≪≫
    (reductionSite P.Ring T).mapIso
      ((Etale.scalarExtension φ.ulift T).mapIso
          (finiteGeneralRingLevelPower Q.Coefficient P.diagonalExponent Q.diagonalExponent
            hA Q.diagonalExponent_annihilates T a d).symm ≪≫ σ.tensorPower d)

variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]


/-- The recorded normalized trace, expressed on the stated shifted Tate line.
Source: purity transport, t_A and t_B (blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceOnTwist (d : ℕ) [SmoothOfRelativeDimension d f] :
    (smoothCompactSupport P f).obj (traceTwist P X d) ⟶ coefficientUnit P Y :=
  (smoothCompactSupport P f).map (traceSourceIso P f d).inv ≫ smoothTrace P f d


/-- Change only the direct-image presentation of the same chosen support functor.
The equality is fixed by the sectionwise coefficient adjunction, not chosen data.
Source: purity transport, compactification comparison
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceSupportModel :
    letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
    smoothCompactSupport P f ≅
      reductionCompactSupport P.Ring (HasCompactification.compactification f).i
        (HasCompactification.compactification f).g := by
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  exact Functor.isoWhiskerLeft
    (sfIntrinsicExtensionByZero
      (HasCompactification.compactification f).i P.Ring).mapDerivedCategory
    (eqToIso (reductionConstantPush_eq P.Ring (HasCompactification.compactification f).g).symm)

/-- The actual finite-free coefficient arrow on the same chosen compactification.
This is extension by zero followed by the proper tensor/counit mate.
Source: purity transport, c_{B/A,M}
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceCompactComparison (r : ℕ) (hr : 1 ≤ r)
    (φ : (primeTraceSetting P r hr).Ring →+* P.Ring)
    (M : proEtaleDerivedCategory X (primeTraceSetting P r hr).Ring) :
    (scalarExtensionFunctor φ Y).obj ((smoothCompactSupport (primeTraceSetting P r hr) f).obj M) ⟶
      (smoothCompactSupport P f).obj ((scalarExtensionFunctor φ X).obj M) :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  (scalarExtensionFunctor φ Y).map ((traceSupportModel (primeTraceSetting P r hr) f).hom.app M) ≫
    (reductionDirectImageComparison φ
      (HasCompactification.compactification f).i
      (HasCompactification.compactification f).g).app M ≫
    (traceSupportModel P f).inv.app ((scalarExtensionFunctor φ X).obj M)

/-- Multiplication-normalized extension of the coefficient unit, with the actual
site/scalar and realization comparisons.
Source: purity transport, A_Y tensor B = B_Y
(blueprint: lem-pur-finite-universal-smooth-trace). -/
def traceUnitExtensionIso {Q : PurityFiniteSetting.{u}} (φ : Q.Ring →+* P.Ring)
    (T : Scheme.{u}) :
    (scalarExtensionFunctor φ T).obj (coefficientUnit Q T) ≅ coefficientUnit P T :=
  (reductionSiteScalarIso φ T).app (Etale.ordinaryFiniteUnit Q.Coefficient T) ≪≫
    (reductionSite P.Ring T).mapIso
      ((Etale.scalarExtension φ.ulift T).mapIso (smoothPurityUnitIso Q.Coefficient T) ≪≫
        Etale.ExceptionalCoefficients.unitIso φ.ulift T ≪≫
        (smoothPurityUnitIso P.Coefficient T).symm)


/-- Finite-free coefficient extension carries the normalized prime-power smooth trace
exactly to the normalized ramified trace, including its sign and shifted Tate line.
The existential comparison data are fixed by unitality and scalar/root generators;
they are presentations of the canonical identifications, not extra hypotheses.
Source: main-20261015 sk-thm-purity-transport, proof Steps 1 and 3
(blueprint: lem-pur-finite-universal-smooth-trace).

Proof plan:
1. Finite-free extension and scalar-extension preservation give B at level er and
   the same bounded constructible finite-Tor domain; compare ordinary and pro-etale
   constructible origins (lem-coef-finite-free-extension, det-sp-scalar-extension-functor,
   lem-sf-proetale-constructible-origin).
2. Balance the common root tower, use locally free Tate lines and commute even shifts;
   apply lem-pur-vector-integration-site-comparison to the actual integration maps.
3. On the common compactification use open extension by zero and the proper tensor
   counit mate to obtain the displayed coefficient map (lem-coef-finite-direct-image,
   lem-cbc-extension-zero-projection-formula, lem-sf-compact-support-restriction-of-scalars).
4. The finite exceptional comparison is the counit transpose, hence satisfies its
   counit equation (lem-pur-finite-coefficient-adjoint-comparisons).
5. Transport the actual projection, exchange and their inverses using
   lem-pur-finite-free-projection-exchange and thm-cbc-finite-level-proetale.
6. Transpose the tensor/counit formula for co-smoothness; its equality follows from
   the counit equation and naturality of the inverse projection formula.
7. Transport the unit-and-Kummer decomposition of the projective line; uniqueness of
   its mate fixes the positive normalized trace (lem-asd-ordinary-finite-p1-adjunction).
8. The geometric compositor obeys lem-pur-finite-free-compact-composition, on product
   compactifications as well as refinements.
9. Induct on ordered affine coordinates, with identity at zero, the projective-line
   trace at each successor and mate pasting for composition; all shifts are even.
10. Glue the degree-zero vector-bundle integration maps on trivializing opens;
    uniqueness identifies their scalar extensions (thm-amb-vector-bundle-purity).
11. Express the diagonal orientation by section base change, normalized deformation
    to the normal bundle and zero-section pullback of the vector orientation.
12. Apply lem-pur-dnc-coefficient-transport with R=A=Z/ell^r and target B: its
    counit-characterized comparison is the same mate as in step 4 (det-sp-reduction-exceptional),
    so its section comparisons are s^*b and the DNC arrow and the first section
    identification commute with coefficient extension.
13. The zero-section vector orientation commutes by steps 10 and 2; composing the three
    arrows gives alpha_B b = S(alpha_A) under S_Y A_Y = B_Y and S_X T_A = T_B.
14. Invert that orientation, tensor it with pullback of the unit and use the
    co-smoothness formula from step 6; thus the smooth purity map commutes
    (def-pur-smooth-purity-map, lem-weil-finite-compact-projection-formula).
15. Apply compact-support pushforward and then its counit. Naturality of the support
    comparison and step 4 cancel the exceptional comparison and give precisely the
    stated trace equation (def-pur-smooth-trace). -/
theorem finite_universal_smooth_trace
    (P : PurityFiniteSetting.{u}) (r : ℕ) (hr : 1 ≤ r)
    (_hlevel : P.level = P.ramificationIndex * r)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃ (eA : (primeTraceSetting P r hr).Ring ≃+*
        ULift.{u} (ZMod (primeTraceSetting P r hr).diagonalExponent))
      (hB : ((primeTraceSetting P r hr).diagonalExponent : P.Ring) = 0)
      (hA : (P.diagonalExponent : (primeTraceSetting P r hr).Coefficient) = 0)
      (q : X.rootsOfUnitySheaf P.diagonalExponent ⟶
        X.rootsOfUnitySheaf (primeTraceSetting P r hr).diagonalExponent)
      (a : finiteEtaleTateLine X P.diagonalExponent
          (primeTraceSetting P r hr).Coefficient hA ≅
        finiteEtaleTateLine X (primeTraceSetting P r hr).diagonalExponent
          (primeTraceSetting P r hr).Coefficient
          (primeTraceSetting P r hr).diagonalExponent_annihilates)
      (σ : Etale.FiniteSmoothPurity.CoefficientLineComparison
        (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA).ulift
        P.diagonalExponent P.diagonalExponent hA P.diagonalExponent_annihilates X),
      FiniteGeneralRingKummerComparison (primeTraceSetting P r hr).Coefficient
        P.diagonalExponent (primeTraceSetting P r hr).diagonalExponent
        hA (primeTraceSetting P r hr).diagonalExponent_annihilates X q a ∧
      σ.roots = 𝟙 _ ∧
      (∀ M : proEtaleDerivedCategory X (primeTraceSetting P r hr).Ring,
        finiteTorConstructible (primeTraceSetting P r hr).coefficients.l
          (primeTraceSetting P r hr).extension
          r hr X M →
        IsIso (traceCompactComparison P f r hr
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA) M)) ∧
      traceCompactComparison P f r hr
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA)
          (traceTwist (primeTraceSetting P r hr) X d) ≫
        (smoothCompactSupport P f).map
          (traceTwistExtensionIso P (primeTraceSetting P r hr)
            (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA)
            X d hA a σ).hom ≫
        traceOnTwist P f d =
      (scalarExtensionFunctor
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA) Y).map
        (traceOnTwist (primeTraceSetting P r hr) f d) ≫
        (traceUnitExtensionIso P
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA) Y).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
