/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointComparisons
import WeilConjectures.SmoothPurity.FiniteFreeProjectionExchange.FiniteFreeProjectionExchange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.GlobalFiniteLevelCompactSupportBaseChange
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactProjectionFormula
import WeilConjectures.AlgebraicGeometry.SfAffineChartPresentation.PurityAffineChartBounds
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
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
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
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
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
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
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
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
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
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
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalCoefficientTriangles
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedDiagonalUnitSupplement
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
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricRingTransport
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
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
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedPairingPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
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
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.FiniteFreeCompactSupport.FiniteFreeCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorBundlePurity
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.PuritySectionInvariantIntrinsic
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalBaseChangeCompared
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
import WeilConjectures.SmoothPurity.DncCoefficientTransport.PurityDncCoefficientTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackUnitCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompactSupportRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
public import WeilConjectures.SixFunctors.DncCoefficientTransport.SectionScalarBaseChange
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientExceptionalGeometryOfCube
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapClosedGeometry
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapDirectGeometry
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapHomGeometry
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapProClosedGeometry
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapProHomGeometry
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapProOmegaGeometry
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedProScalarTensorGeometricSquare
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageCoefficientCalculus
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarPullNormalization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

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

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

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

end WeilConjectures.PurityFiniteSetting
