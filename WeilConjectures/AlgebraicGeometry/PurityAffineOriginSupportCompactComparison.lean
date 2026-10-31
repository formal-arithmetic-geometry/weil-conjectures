/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientQuotientLine
import WeilConjectures.AlgebraicGeometry.PurityDivisorClass
public import WeilConjectures.AlgebraicGeometry.PurityRankOneLocalCalculation
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper

import WeilConjectures.AlgebraicGeometry.CartesianCoefficientsFiniteFree
import WeilConjectures.AlgebraicGeometry.PadicIntegersInvertEll
import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.MilnorTower
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimitSupplement
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.OpenImmersionTensorProjection
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
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
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
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
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
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
import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import WeilConjectures.CategoryTheory.RingedTowerPushforwardLimitComparison
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.FiniteTateSiteDescent
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummerSupplement
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
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
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
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.RestrictionRingedToposModuleDirectImageSupplement
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
import WeilConjectures.AlgebraicGeometry.CompletedCoefficientPushforwardComparison

/-!
# Support at the origin and compact support on the affine line

Source: latest blueprint, sec-smooth-purity/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison).

The coefficient rings, Tate lines, closed-support kernel, open extension by zero,
and derived direct images below are the published constructions. In particular,
the supported and compact objects are objects of the sheaf-valued ordinary derived
category on the small pro-etale site of the geometric point.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineOrigin

/-- The four coefficient cases; finite level n means the positive exponent n+1.
Source: Step 2 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
inductive Stage
  | finite (n : ℕ)
  | integral
  | rational
  | closure

/-- The actual condensed rings, with the finite-subextension-valued closure ring.
Source: coefficient convention in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def ring (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) : Stage →
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  | .finite n => Profinite.continuousMapRingObj (completedResidue l E π n)
  | .integral => Profinite.padicIntegersRingObj l E.1
  | .rational => Profinite.continuousMapRingObj E.1
  | .closure => Profinite.padicAlgClRingObj l

/-- Transport the existing ring-object structures case by case.
Source: pulled-back coefficient convention
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
instance ringMonObj (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (b : Stage) : MonObj (ring l E π b) := by
  cases b <;> dsimp only [ring] <;> infer_instance

/-- Every coefficient ring in this statement is commutative.
Source: coefficient convention
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
instance ringComm (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (b : Stage) : IsCommMonObj (ring l E π b) := by
  cases b <;> dsimp only [ring] <;> infer_instance

/-- The published positive Tate lines, including every uniformizer quotient.
Source: sk-def-sp-tate-twist and its uniformizer reduction
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def line (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (X : Scheme.{u}) :
    (b : Stage) → CondensedRing.supportModules (ring l E π b) X
  | .finite n => DiagonalCoefficients.quotientLine l E π n X
  | .integral => spIntegralTwist X l E
  | .rational => spRationalTwist X l E
  | .closure => spQbarTwist X l

/-- The canonical chart A^1 -> P^1, with the same one-coordinate presentation as
PurityFiniteSetting.Line. Source: fixed compactification in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def chart (s : Scheme.{u}) : WeilConjectures.PurityFiniteSetting.Line s ⟶ ProjectiveLine s :=
  AffineSpace.reindex (fun _ : PUnit.{u + 1} => (ULift.up 0 : ULift.{u} (Fin 1))) s ≫
    ProjectiveLine.affineChart s

/-- The chart is an open immersion: reindexing the singleton coordinate is an
isomorphism and the standard projective-line chart is open.
Source: fixed compactification in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison).
Proof: inverse reindexing is given by the unique map to PUnit; the two reindex
composites are identities. Compose this isomorphism with the standard open chart. -/
@[instance] theorem chart_isOpenImmersion (s : Scheme.{u}) :
    IsOpenImmersion (chart s) := by sorry

/-- The fixed chart lies over the affine-line projection.
Source: fixed compactification in Step 1
(blueprint: lem-pur-affine-origin-support-compact-comparison).
Proof: compose the standard affine-chart projection equation with the singleton
reindexing projection equation; both are the published affine-space structure maps. -/
theorem chart_over (s : Scheme.{u}) :
    chart s ≫ (ProjectiveLine s ↘ s) =
      WeilConjectures.PurityFiniteSetting.lineProjection s := by sorry

/-- The zero section is closed. Source: the origin in Step 1
(blueprint: lem-pur-affine-origin-support-compact-comparison).
Proof: it is a section of the separated affine-space projection. -/
@[instance] theorem origin_isClosedImmersion (s : Scheme.{u}) :
    IsClosedImmersion (WeilConjectures.PurityFiniteSetting.zeroSection s) := by sorry

/-- The punctured-line inclusion is quasi-compact: on each affine test it is
principal open. Source: Step 1
(blueprint: lem-pur-affine-origin-support-compact-comparison).
Proof: the inverse image of the unique coordinate's basic open on an affine
open of the line is again principal affine. -/
@[instance] theorem punctured_quasiCompact (s : Scheme.{u}) :
    QuasiCompact (WeilConjectures.PurityFiniteSetting.openImmersion s) := by sorry

/-- The origin and the punctured-line open are complementary.
Source: Step 1 of the node's proof
(blueprint: lem-pur-affine-origin-support-compact-comparison).
Proof: AffineSpace.compl_range_zeroSection identifies the complement with the
basic open of the unique affine coordinate, which is exactly openImmersion. -/
theorem origin_complement (s : Scheme.{u}) :
    Set.range (WeilConjectures.PurityFiniteSetting.zeroSection s).base =
      (Set.range (WeilConjectures.PurityFiniteSetting.openImmersion s).base)ᶜ := by sorry

/-- The fixed standard compactification, as actual scheme data.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def compactification (s : Scheme.{u}) :
    Compactification (WeilConjectures.PurityFiniteSetting.lineProjection s) where
  Z := ProjectiveLine s
  g := ProjectiveLine s ↘ s
  i := chart s
  comm := (chart_over s).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- i_* Ri^!: the right-derived closed-support kernel, followed by exact closed
extension, in the ordinary pro-etale module category.
Source: Step 1 and det-lem-formal-closed-support-adjunction
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def supported (s : Scheme.{u}) :
    DerivedCategory (CondensedRing.supportModules Λ
      (WeilConjectures.PurityFiniteSetting.Line s)) ⥤
      DerivedCategory (CondensedRing.supportModules Λ
        (WeilConjectures.PurityFiniteSetting.Line s)) := by
  let i := WeilConjectures.PurityFiniteSetting.zeroSection s
  let o := WeilConjectures.PurityFiniteSetting.openImmersion s
  letI := CondensedRing.closedSupport_lowerStarExact Λ i o (origin_complement s)
  exact (CondensedRing.closedSupport Λ i o).rightDerivedFunctor ⋙
    (CondensedRing.lowerStar Λ i).mapDerivedCategory

/-- The actual support counit, with the normalization of the recorded adjunction.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def supportCounit (s : Scheme.{u}) : supported Λ s ⟶ 𝟭 _ := by
  let i := WeilConjectures.PurityFiniteSetting.zeroSection s
  let o := WeilConjectures.PurityFiniteSetting.openImmersion s
  letI := CondensedRing.closedSupport_lowerStarExact Λ i o (origin_complement s)
  exact (CondensedRing.closedSupportDerivedAdjunction Λ i o (origin_complement s)).counit

/-- Ra_* on the affine line; no sections-at-a-singleton functor occurs.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
abbrev direct (s : Scheme.{u}) :=
  (CondensedRing.lowerStar Λ
    (WeilConjectures.PurityFiniteSetting.lineProjection s)).rightDerivedFunctor

/-- Rq_* j_! for the fixed standard projective-line compactification: the published
derived lower shriek of this compactification (exact j_! followed by Rq_*).
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
abbrev compact (s : Scheme.{u}) :=
  CondensedRing.rightDerivedLowerShriekOfCompactification Λ (compactification s)

/-- The normalized map j_! K -> Rj_* K, constructed from the two open adjunctions.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def openToDirect (s : Scheme.{u})
    (K : DerivedCategory (CondensedRing.supportModules Λ
      (WeilConjectures.PurityFiniteSetting.Line s))) :
    (CondensedRing.openImmersionLowerShriek Λ (chart s)).mapDerivedCategory.obj K ⟶
      (CondensedRing.lowerStar Λ (chart s)).rightDerivedFunctor.obj K :=
  letI : IsIso (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
      Λ (chart s)).unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (chart s)).unit.app _ ≫
    (CondensedRing.lowerStar Λ (chart s)).rightDerivedFunctor.map
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion
        Λ (chart s)).hom.app _ ≫
        inv ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
          Λ (chart s)).unit.app K))

/-- Rq_* j_! -> Ra_* on the fixed compactification, including composition transport.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def compactToDirect (s : Scheme.{u})
    (K : DerivedCategory (CondensedRing.supportModules Λ
      (WeilConjectures.PurityFiniteSetting.Line s))) :
    (compact Λ s).obj K ⟶ (direct Λ s).obj K := by
  exact (CondensedRing.lowerStar Λ (ProjectiveLine s ↘ s)).rightDerivedFunctor.map
      (openToDirect Λ s K) ≫
    (CondensedRing.rightDerivedLowerStarComp Λ (chart s) (ProjectiveLine s ↘ s)).hom.app K ≫
    (eqToIso (congrArg (fun f =>
      (CondensedRing.lowerStar Λ f).rightDerivedFunctor.obj K) (chart_over s))).hom

/-- The coefficient unit as a degree-zero complex over the actual pulled-back ring.
Source: source identifications in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
abbrev unit (s : Scheme.{u}) :=
  (DerivedCategory.singleFunctor (CondensedRing.supportModules Λ s) 0).obj
    (Mod.regular (condensedRingObj Λ s))

/-- The published Tate line in degree zero.
Source: Step 2 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def tate (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (b : Stage) (s : Scheme.{u}) :=
  (DerivedCategory.singleFunctor (CondensedRing.supportModules (ring l E π b)
    (WeilConjectures.PurityFiniteSetting.Line s)) 0).obj
      (line l E π (WeilConjectures.PurityFiniteSetting.Line s) b)

/-- S_Lambda = Ra_* i_* Ri^!(Lambda_X(1)), an actual object of D(s_proet,Lambda_s).
Source: displayed definition S in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def S (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (b : Stage) (s : Scheme.{u}) :=
  (direct (ring l E π b) s).obj
    ((supported (ring l E π b) s).obj (tate l E π b s))

/-- C_Lambda = Rq_* j_! Lambda_X(1) for the standard P^1 compactification.
Source: displayed definition C in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def C (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (b : Stage) (s : Scheme.{u}) :=
  (compact (ring l E π b) s).obj (tate l E π b s)


/-- Exact closed extension at the origin, using the recorded support adjunction.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
instance originLowerStarExact (s : Scheme.{u}) :
    PreservesFiniteColimits (CondensedRing.lowerStar Λ
      (WeilConjectures.PurityFiniteSetting.zeroSection s)) :=
  CondensedRing.closedSupport_lowerStarExact Λ _ _ (origin_complement s)

/-- Ra_* i_* as an exact-closed/derived-direct composite.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def originPush (s : Scheme.{u}) :=
  (CondensedRing.lowerStar Λ
    (WeilConjectures.PurityFiniteSetting.zeroSection s)).mapDerivedCategory ⋙ direct Λ s

/-- The canonical identity Ra_* i_* = R(a i)_* = id, including the exact-closed
comparison and the identity-map comparison.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def originPushIso (s : Scheme.{u}) : originPush Λ s ≅ 𝟭 _ := by
  let i := WeilConjectures.PurityFiniteSetting.zeroSection s
  exact Functor.isoWhiskerRight
      (CondensedRing.lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    CondensedRing.rightDerivedLowerStarComp Λ i
      (WeilConjectures.PurityFiniteSetting.lineProjection s) ≪≫
    Functor.rightDerivedFunctorNatIso
      (eqToIso (congrArg (CondensedRing.lowerStar Λ)
        (AffineSpace.zeroSection_over (ULift.{u} (Fin 1)) s)) ≪≫
          CondensedRing.lowerStarId Λ s) ≪≫
    (𝟭 (CondensedRing.supportModules Λ s)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Shift structure on the displayed composite, inherited from the exact and
right-derived functors. Source: Step 1
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
instance originPushCommShift (s : Scheme.{u}) : (originPush Λ s).CommShift ℤ := by
  dsimp only [originPush]
  infer_instance

/-- The sheaf i_* Lambda_s, used as the source of an actual Cartier arrow.
Source: Cartier clause in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
abbrev cartierSource (s : Scheme.{u}) :=
  (CondensedRing.lowerStar Λ (WeilConjectures.PurityFiniteSetting.zeroSection s)).obj
    (Mod.regular (condensedRingObj Λ s))

/-- The supported Cartier arrow is adjointed through i_* |- Ri^!, then carried
through Ra_* i_* = id. This fixes its actual source and target, including shifts.
Source: Cartier clause in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def supportedClass (s : Scheme.{u})
    (L : CondensedRing.supportModules Λ (WeilConjectures.PurityFiniteSetting.Line s))
    (c : (DerivedCategory.singleFunctor _ 0).obj (cartierSource Λ s) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj L)⟦(2 : ℤ)⟧) :
    unit Λ s ⟶ ((direct Λ s).obj ((supported Λ s).obj
      ((DerivedCategory.singleFunctor _ 0).obj L)))⟦(2 : ℤ)⟧ :=
  (originPushIso Λ s).inv.app _ ≫
    (originPush Λ s).map
      ((CondensedRing.closedSupportDerivedAdjunction Λ
        (WeilConjectures.PurityFiniteSetting.zeroSection s)
        (WeilConjectures.PurityFiniteSetting.openImmersion s)
        (origin_complement s)).homEquiv _ _
          (((CondensedRing.lowerStar Λ
            (WeilConjectures.PurityFiniteSetting.zeroSection s)
            ).mapDerivedCategorySingleFunctor 0).hom.app _ ≫ c)) ≫
    (originPush Λ s).map
      (((CondensedRing.closedSupport Λ
        (WeilConjectures.PurityFiniteSetting.zeroSection s)
        (WeilConjectures.PurityFiniteSetting.openImmersion s)
        ).rightDerivedFunctor.commShiftIso (2 : ℤ)).hom.app _) ≫
    ((originPush Λ s).commShiftIso (2 : ℤ)).hom.app _

/-- Proper support makes the compact-to-ordinary map invertible on i_* Ri^! K.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison).
Proof: the origin is disjoint from infinity and is proper over s. Extension by
zero and direct image of a complex supported there agree, by open/closed
localization. Apply Rq_* and the canonical composition isomorphism. -/
@[instance] theorem compactToDirect_supported_isIso (s : Scheme.{u})
    (K : DerivedCategory (CondensedRing.supportModules Λ
      (WeilConjectures.PurityFiniteSetting.Line s))) :
    IsIso (compactToDirect Λ s ((supported Λ s).obj K)) := by sorry

/-- The canonical proper-supported counit u: S -> C. Its two factors are the
inverse proper-support comparison and Rq_* j_! of the closed-support counit.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def forgetSupports (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (b : Stage) (s : Scheme.{u}) :
    S l E π b s ⟶ C l E π b s :=
  inv (compactToDirect (ring l E π b) s
    ((supported (ring l E π b) s).obj (tate l E π b s))) ≫
      (compact (ring l E π b) s).map
        ((supportCounit (ring l E π b) s).app (tate l E π b s))

/-- A Cartier arrow in the actual coefficient category, with its adjoint supported
class required to be an isomorphism. The arrow itself is not arbitrary data in a
hypothesis of the theorem: the theorem constructs a normalized family of these.
Source: Cartier clause in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
structure Cartier (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (b : Stage) (s : Scheme.{u}) where
  arrow : (DerivedCategory.singleFunctor _ 0).obj (cartierSource (ring l E π b) s) ⟶
    (tate l E π b s)⟦(2 : ℤ)⟧
  supported_iso : IsIso (supportedClass (ring l E π b) s
    (line l E π (WeilConjectures.PurityFiniteSetting.Line s) b) arrow)

/-- The supported class Lambda_s -> S_Lambda[2] of a Cartier arrow.
Source: Cartier clause in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def Cartier.alpha {l : ℕ} [Fact l.Prime] {E : PadicAlgCl.FiniteIntermediateField l}
    {π : PadicAlgCl.integers l E} {b : Stage} {s : Scheme.{u}}
    (d : Cartier l E π b s) : unit (ring l E π b) s ⟶ (S l E π b s)⟦(2 : ℤ)⟧ :=
  supportedClass (ring l E π b) s
    (line l E π (WeilConjectures.PurityFiniteSetting.Line s) b) d.arrow

/-- The compact image is literally u[2] composed with the supported class.
Source: compact-image clause in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def Cartier.beta {l : ℕ} [Fact l.Prime] {E : PadicAlgCl.FiniteIntermediateField l}
    {π : PadicAlgCl.integers l E} {b : Stage} {s : Scheme.{u}}
    (d : Cartier l E π b s) : unit (ring l E π b) s ⟶ (C l E π b s)⟦(2 : ℤ)⟧ :=
  d.alpha ≫ (forgetSupports l E π b s)⟦(2 : ℤ)⟧'

/-- Finite coefficients retain the canonical ordinary supported Cartier class,
transported through the coefficient realization fixed on rings and root sections.
The source identification is fixed on underlying sheaves; it cannot rescale one.
Source: Steps 2--4 and lem-pur-divisor-class
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def FiniteCartierNormalized (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (n : ℕ) (s : Scheme.{u}) (d : Cartier l E π (.finite n) s) : Prop :=
  ∃ (_hfinite : Finite (ULift.{u + 1} (completedResidue l E π n))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hX : IsUnit ((l ^ (r + 1) : ℕ) :
      Γ(WeilConjectures.PurityFiniteSetting.Line s, ⊤)))
    (hI : (WeilConjectures.PurityFiniteSetting.zeroSection s).ker.IsInvertible)
    (eS : DiagonalCoefficients.FiniteRealization (ring l E π (.finite n))
      (ULift.{u + 1} (completedResidue l E π n)) s)
    (eX : DiagonalCoefficients.FiniteRealization (ring l E π (.finite n))
      (ULift.{u + 1} (completedResidue l E π n))
        (WeilConjectures.PurityFiniteSetting.Line s))
    (roots : DiagonalCoefficients.QuotientLineRealization l E π n r hA
      (WeilConjectures.PurityFiniteSetting.Line s) eX)
    (sourceIso : eX.F.obj (cartierSource (ring l E π (.finite n)) s) ≅
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (completedResidue l E π n)))
        (WeilConjectures.PurityFiniteSetting.zeroSection s)).obj
          (geoCartierConstant (ULift.{u + 1} (completedResidue l E π n)) s)),
    HEq (eX.underlying.inv.app (cartierSource (ring l E π (.finite n)) s) ≫
      (sheafCompose (Scheme.ProEt.topology (WeilConjectures.PurityFiniteSetting.Line s))
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (completedResidue l E π n)))
          Ab.{u + 1})).map sourceIso.hom)
      ((lowerStar Ab.{u + 1} (WeilConjectures.PurityFiniteSetting.zeroSection s)).map
        (eS.underlying.inv.app (Mod.regular (condensedRingObj (ring l E π (.finite n)) s)) ≫
          (sheafCompose (Scheme.ProEt.topology s)
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (completedResidue l E π n)))
              Ab.{u + 1})).map eS.unitIso.hom)) ∧
    (DerivedCategory.singleFunctor _ 0).map sourceIso.inv ≫
      SpTowerClasses.mapSingleArrow eX.F (2 : ℤ) d.arrow ≫
        ((DerivedCategory.singleFunctor _ 0).map (roots.iso l).hom)⟦(2 : ℤ)⟧' =
      SpTowerClasses.extensionArrow
        (geoCartierCanonicalClass (ULift.{u + 1} (completedResidue l E π n))
          (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA
          (WeilConjectures.PurityFiniteSetting.zeroSection s) hI hX)


/-- The finite etale object i_* Ri^! L, in ordinary module-valued derived categories.
Source: finite etale-origin clause
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def etaleSupported (A : Type (u + 1)) [CommRing A] [Finite A] (s : Scheme.{u}) :
    DerivedCategory (Sheaf (WeilConjectures.PurityFiniteSetting.Line s).smallEtaleTopology
      (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf (WeilConjectures.PurityFiniteSetting.Line s).smallEtaleTopology
      (ModuleCat.{u + 1} A)) :=
  (Etale.lowerStar (ModuleCat.{u + 1} A)
    (WeilConjectures.PurityFiniteSetting.zeroSection s)).rightDerivedFunctor.rightAdjoint ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} A)
        (WeilConjectures.PurityFiniteSetting.zeroSection s)).rightDerivedFunctor

/-- The ordinary etale supported object, without replacing it by one cohomology group.
Source: finite etale-origin clause
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def etaleS (A : Type (u + 1)) [CommRing A] [Finite A] (s : Scheme.{u})
    (L : DerivedCategory (Sheaf
      (WeilConjectures.PurityFiniteSetting.Line s).smallEtaleTopology
        (ModuleCat.{u + 1} A))) :
    DerivedCategory (Sheaf s.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (Etale.lowerStar (ModuleCat.{u + 1} A)
    (WeilConjectures.PurityFiniteSetting.lineProjection s)).rightDerivedFunctor.obj
      ((etaleSupported A s).obj L)

/-- The fixed projective-line compact object on the etale site.
Source: finite etale-origin clause
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def etaleC (A : Type (u + 1)) [CommRing A] (s : Scheme.{u})
    (L : DerivedCategory (Sheaf
      (WeilConjectures.PurityFiniteSetting.Line s).smallEtaleTopology
        (ModuleCat.{u + 1} A))) :
    DerivedCategory (Sheaf s.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (compactification s)).obj L

/-- Proper support identifies the two etale pushforwards on the supported input.
Source: Steps 1--2 (blueprint: lem-pur-affine-origin-support-compact-comparison).
Proof: closed support is disjoint from infinity, so the proper-support comparison
is invertible before Rq_*; alternatively use proper i and shriek composition. -/
@[instance] theorem etaleSupported_compactificationForgetSupports_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (s : Scheme.{u})
    (L : DerivedCategory (Sheaf
      (WeilConjectures.PurityFiniteSetting.Line s).smallEtaleTopology
        (ModuleCat.{u + 1} A))) :
    IsIso ((Etale.compactificationForgetSupports (ModuleCat.{u + 1} A)
      (compactification s)).app ((etaleSupported A s).obj L)) := by sorry

/-- The actual finite etale supported counit, via its proper-support comparison.
Source: finite etale-origin clause
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def etaleForgetSupports (A : Type (u + 1)) [CommRing A] [Finite A] (s : Scheme.{u})
    (L : DerivedCategory (Sheaf
      (WeilConjectures.PurityFiniteSetting.Line s).smallEtaleTopology
        (ModuleCat.{u + 1} A))) : etaleS A s L ⟶ etaleC A s L :=
  inv ((Etale.compactificationForgetSupports (ModuleCat.{u + 1} A)
    (compactification s)).app ((etaleSupported A s).obj L)) ≫
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (compactification s)).map
        ((Adjunction.ofIsLeftAdjoint (Etale.lowerStar (ModuleCat.{u + 1} A)
          (WeilConjectures.PurityFiniteSetting.zeroSection s)).rightDerivedFunctor).counit.app L)

set_option maxHeartbeats 1600000 in
-- The retained site-comparison square elaborates several large derived-category instances.
/-- Retained finite etale witnesses for the realized supported and compact objects.
The site functor is the recorded comparison inverse image. Their exact antecedents
and the canonical-arrow square are specified in FiniteOriginCompatibility below.
Source: Step 2 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
structure FiniteOriginObjects (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) (s : Scheme.{u}) where
  [finite : Finite (ULift.{u + 1} (completedResidue l E π n))]
  r : ℕ
  annihilates : ((l ^ (r + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0
  realization : DiagonalCoefficients.FiniteRealization (ring l E π (.finite n))
    (ULift.{u + 1} (completedResidue l E π n)) s
  source : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology s)
    (ModuleCat.{u + 1} (ULift.{u + 1} (completedResidue l E π n))))
  target : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology s)
    (ModuleCat.{u + 1} (ULift.{u + 1} (completedResidue l E π n))))
  source_eq : source.obj = realization.F.mapDerivedCategory.obj (S l E π (.finite n) s)
  target_eq : target.obj = realization.F.mapDerivedCategory.obj (C l E π (.finite n) s)
  sourceOrigin : s.FixedEtaleOriginWitness
    (ULift.{u + 1} (completedResidue l E π n)) source
  targetOrigin : s.FixedEtaleOriginWitness
    (ULift.{u + 1} (completedResidue l E π n)) target

set_option maxHeartbeats 1600000 in
-- Naming the witness objects keeps the compatibility predicate from expanding their data.
/-- Exact finite-origin object and canonical-arrow identifications, followed by the
specified site-comparison square. Heterogeneous equalities only avoid eager proof
transport reduction; all objects belong to the fixed ordinary derived categories.
Source: Step 2 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def FiniteOriginCompatibility {l : ℕ} [Fact l.Prime]
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E}
    {n : ℕ} {s : Scheme.{u}} (o : FiniteOriginObjects l E π n s) : Prop :=
  letI := o.finite
  HEq o.sourceOrigin.complex.obj (etaleS
    (ULift.{u + 1} (completedResidue l E π n)) s
      (Etale.ordinaryFiniteLine (ULift.{u + 1} (completedResidue l E π n))
        (l ^ (o.r + 1)) o.annihilates (WeilConjectures.PurityFiniteSetting.Line s))) ∧
  HEq o.targetOrigin.complex.obj (etaleC
    (ULift.{u + 1} (completedResidue l E π n)) s
      (Etale.ordinaryFiniteLine (ULift.{u + 1} (completedResidue l E π n))
        (l ^ (o.r + 1)) o.annihilates (WeilConjectures.PurityFiniteSetting.Line s))) ∧
  ∃ etaleArrow : o.sourceOrigin.complex.obj ⟶ o.targetOrigin.complex.obj,
    HEq etaleArrow (etaleForgetSupports
      (ULift.{u + 1} (completedResidue l E π n)) s
        (Etale.ordinaryFiniteLine (ULift.{u + 1} (completedResidue l E π n))
          (l ^ (o.r + 1)) o.annihilates (WeilConjectures.PurityFiniteSetting.Line s))) ∧
    (comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} (completedResidue l E π n))) s).mapDerivedCategory.map
        etaleArrow ≫ o.targetOrigin.iso.hom ≫ eqToHom o.target_eq =
      o.sourceOrigin.iso.hom ≫ eqToHom o.source_eq ≫
        o.realization.F.mapDerivedCategory.map (forgetSupports l E π (.finite n) s)

/-- The retained finite-origin objects together with all exact compatibility clauses.
Source: Step 2 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
structure FiniteOrigin (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) (s : Scheme.{u}) where
  objects : FiniteOriginObjects l E π n s
  compatibility : FiniteOriginCompatibility objects

set_option maxHeartbeats 1600000 in
-- The semilinear coefficient unit involves the large module-object action instances.
/-- The canonical semilinear coefficient-unit map, retained with its underlying
pulled-back ring map. Source: coefficient source identifications
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
abbrev UnitMap {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] (s : Scheme.{u}) :=
  DiagonalCoefficients.Semilinear a (Mod.regular (condensedRingObj Λ s))
    (Mod.regular (condensedRingObj Λ' s)) (coefficientMap a s)

/-- The actual closed direct image of the semilinear coefficient unit.
Source: Cartier source comparison
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def sourceMap {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] (s : Scheme.{u})
    (m : UnitMap Λ a s) : cartierSource Λ s ⟶
      (Mod.comap (D := Sheaf
      (Scheme.ProEt.topology (WeilConjectures.PurityFiniteSetting.Line s)) Ab.{u + 1})
      (coefficientMap a (WeilConjectures.PurityFiniteSetting.Line s))).obj
        (cartierSource Λ' s) :=
  (CondensedRing.lowerStar Λ (WeilConjectures.PurityFiniteSetting.zeroSection s)).map m.hom ≫
    (CondensedRing.comapLowerStarIso a
      (WeilConjectures.PurityFiniteSetting.zeroSection s)).inv.app _

set_option maxHeartbeats 1600000 in
-- The quotient comparison elaborates the integral and finite module actions simultaneously.
/-- The integral Cartier arrow reduces through the actual quotient map on its
source and the prescribed root-line reduction on its target. No diagram of
arbitrary derived objects is substituted for this equation on the affine line.
Source: Step 10 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
structure CartierReduction (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (n : ℕ) (s : Scheme.{u}) (dR : Cartier l E π .integral s)
    (dn : Cartier l E π (.finite n) s) where
  source : UnitMap (ring l E π .integral) (DiagonalCoefficients.quotientMap l E π n) s
  line : DiagonalCoefficients.Semilinear (DiagonalCoefficients.quotientMap l E π n)
    (spIntegralTwist (WeilConjectures.PurityFiniteSetting.Line s) l E)
    (DiagonalCoefficients.quotientLine l E π n (WeilConjectures.PurityFiniteSetting.Line s))
    (DiagonalCoefficients.quotientLineMap l E π n (WeilConjectures.PurityFiniteSetting.Line s))
  equation : dR.arrow ≫ ((DerivedCategory.singleFunctor _ 0).map line.hom)⟦(2 : ℤ)⟧' =
    (DerivedCategory.singleFunctor _ 0).map
      (sourceMap (ring l E π .integral) (DiagonalCoefficients.quotientMap l E π n) s source) ≫
        SpTowerClasses.mapSingleArrow
          (Mod.comap (D := Sheaf
            (Scheme.ProEt.topology (WeilConjectures.PurityFiniteSetting.Line s)) Ab.{u + 1})
            (coefficientMap (DiagonalCoefficients.quotientMap l E π n)
              (WeilConjectures.PurityFiniteSetting.Line s))) (2 : ℤ) dn.arrow

/-- The scalar comparison of the Cartier arrow on the affine line is fixed by
its adjoint-normalized source and root-line endpoint maps.
Source: Step 10 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
structure CartierScalar {l : ℕ} [Fact l.Prime]
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E}
    {b b' : Stage} {s : Scheme.{u}}
    (a : ring l E π b ⟶ ring l E π b') [IsMonHom a]
    (v : (line l E π (WeilConjectures.PurityFiniteSetting.Line s) b).X ⟶
      (line l E π (WeilConjectures.PurityFiniteSetting.Line s) b').X)
    (d : Cartier l E π b s) (d' : Cartier l E π b' s) where
  coefficient : DiagonalCoefficients.Endpoint a
    (Mod.regular (condensedRingObj (ring l E π b) s))
    (Mod.regular (condensedRingObj (ring l E π b') s)) (coefficientMap a s)
  source : DiagonalCoefficients.Endpoint a
    (cartierSource (ring l E π b) s) (cartierSource (ring l E π b') s)
    (sourceMap (ring l E π b) a s coefficient.semilinear).hom
  line : DiagonalCoefficients.Endpoint a
    (line l E π (WeilConjectures.PurityFiniteSetting.Line s) b)
    (line l E π (WeilConjectures.PurityFiniteSetting.Line s) b') v
  equation : (DiagonalCoefficients.derivedScalars a
      (WeilConjectures.PurityFiniteSetting.Line s)).map d.arrow ≫ line.shift a =
    source.iso.hom ≫ d'.arrow
  supported : (DiagonalCoefficients.derivedScalars a s).obj (S l E π b s) ≅ S l E π b' s
  compact : (DiagonalCoefficients.derivedScalars a s).obj (C l E π b s) ≅ C l E π b' s
  alpha : (DiagonalCoefficients.derivedScalars a s).map d.alpha ≫
      ((DiagonalCoefficients.derivedScalars a s).commShiftIso (2 : ℤ)).hom.app _ ≫
        supported.hom⟦(2 : ℤ)⟧' = coefficient.iso.hom ≫ d'.alpha
  beta : (DiagonalCoefficients.derivedScalars a s).map d.beta ≫
      ((DiagonalCoefficients.derivedScalars a s).commShiftIso (2 : ℤ)).hom.app _ ≫
        compact.hom⟦(2 : ℤ)⟧' = coefficient.iso.hom ≫ d'.beta
  counit : (DiagonalCoefficients.derivedScalars a s).map (forgetSupports l E π b s) ≫
    compact.hom = supported.hom ≫ forgetSupports l E π b' s


/-- Exact restriction from one finite quotient to the actual integral ring sheaf.
Source: inverse-limit clause in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
abbrev restriction (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) (s : Scheme.{u}) :
    DerivedCategory (CondensedRing.supportModules (ring l E π (.finite n)) s) ⥤
      DerivedCategory (CondensedRing.supportModules (ring l E π .integral) s) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology s) Ab.{u + 1})
    (coefficientMap (DiagonalCoefficients.quotientMap l E π n) s)).mapDerivedCategory

/-- The coefficient A_n, regarded as an R_s-module, without deriving a quotient.
Source: source inverse-limit clause
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
abbrev restrictedUnit (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) (s : Scheme.{u}) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology s) Ab.{u + 1})
    (coefficientMap (DiagonalCoefficients.quotientMap l E π n) s)).obj
    (Mod.regular (condensedRingObj (ring l E π (.finite n)) s))

/-- The specified successive quotient map on condensed ring objects.
Source: inverse-limit clause
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def quotientTransition (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) :
    ring l E π (.finite (n + 1)) ⟶ ring l E π (.finite n) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (completedResidueTransition l E π n)

/-- Restrict the actual finite Cartier class, with the canonical single and shift
comparisons. Source: inverse-limit class clause
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def finiteAlpha {l : ℕ} [Fact l.Prime] {E : PadicAlgCl.FiniteIntermediateField l}
    {π : PadicAlgCl.integers l E} {n : ℕ} {s : Scheme.{u}}
    (d : Cartier l E π (.finite n) s) :
    (DerivedCategory.singleFunctor _ 0).obj (restrictedUnit l E π n s) ⟶
      ((restriction l E π n s).obj (S l E π (.finite n) s))⟦(2 : ℤ)⟧ :=
  ((Mod.comap (D := Sheaf (Scheme.ProEt.topology s) Ab.{u + 1})
    (coefficientMap (DiagonalCoefficients.quotientMap l E π n) s)
    ).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (restriction l E π n s).map d.alpha ≫
        ((restriction l E π n s).commShiftIso (2 : ℤ)).hom.app _

/-- Restrict the compact image of the actual finite Cartier class.
Source: inverse-limit compact-class clause
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def finiteBeta {l : ℕ} [Fact l.Prime] {E : PadicAlgCl.FiniteIntermediateField l}
    {π : PadicAlgCl.integers l E} {n : ℕ} {s : Scheme.{u}}
    (d : Cartier l E π (.finite n) s) :
    (DerivedCategory.singleFunctor _ 0).obj (restrictedUnit l E π n s) ⟶
      ((restriction l E π n s).obj (C l E π (.finite n) s))⟦(2 : ℤ)⟧ :=
  ((Mod.comap (D := Sheaf (Scheme.ProEt.topology s) Ab.{u + 1})
    (coefficientMap (DiagonalCoefficients.quotientMap l E π n) s)
    ).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (restriction l E π n s).map d.beta ≫
        ((restriction l E π n s).commShiftIso (2 : ℤ)).hom.app _

set_option maxHeartbeats 1600000 in
-- The tower legs compare the exact-single and restricted coefficient presentations.
/-- Three actual towers over R_s and their projection-normalized derived-limit
cones. All finite levels are the specified quotient, supported, and compact
objects. The coefficient transitions are fixed on underlying sheaves. The other
transitions and cone legs are fixed by the normalized Cartier isomorphisms;
thus they are unique, rather than arbitrary diagrams with the same object types.
Shifting both target towers by two gives precisely the displayed unshifted
Rlim identifications, since shift is an exact equivalence preserving products.
Source: Steps 5--7 and 10
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
structure IntegralComparison (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (s : Scheme.{u}) (d : ∀ b : Stage, Cartier l E π b s) where
  reductions : ∀ n : ℕ, CartierReduction l E π n s (d .integral) (d (.finite n))
  transition : ∀ n : ℕ,
    restrictedUnit l E π (n + 1) s ⟶ restrictedUnit l E π n s
  transition_normalization : ∀ n : ℕ,
    (transition n).hom = coefficientMap (quotientTransition l E π n) s
  coefficientLegs : (Functor.const ℕᵒᵖ).obj (unit (ring l E π .integral) s) ⟶
    Functor.ofOpSequence
      (X := fun n => (DerivedCategory.singleFunctor _ 0).obj (restrictedUnit l E π n s))
      (fun n => (DerivedCategory.singleFunctor _ 0).map (transition n))
  coefficient_normalization : ∀ n : ℕ, HEq (coefficientLegs.app (op n))
    ((DerivedCategory.singleFunctor _ 0).map (reductions n).source.hom)
  coefficient_limit : Pretriangulated.IsHomotopyLimit
    (Cone.mk (unit (ring l E π .integral) s) coefficientLegs)
  supportedTransition : ∀ n : ℕ,
    ((restriction l E π (n + 1) s).obj (S l E π (.finite (n + 1)) s))⟦(2 : ℤ)⟧ ⟶
      ((restriction l E π n s).obj (S l E π (.finite n) s))⟦(2 : ℤ)⟧
  compactTransition : ∀ n : ℕ,
    ((restriction l E π (n + 1) s).obj (C l E π (.finite (n + 1)) s))⟦(2 : ℤ)⟧ ⟶
      ((restriction l E π n s).obj (C l E π (.finite n) s))⟦(2 : ℤ)⟧
  supported_transition : ∀ n : ℕ,
    finiteAlpha (d (.finite (n + 1))) ≫ supportedTransition n =
      (DerivedCategory.singleFunctor _ 0).map (transition n) ≫ finiteAlpha (d (.finite n))
  compact_transition : ∀ n : ℕ,
    finiteBeta (d (.finite (n + 1))) ≫ compactTransition n =
      (DerivedCategory.singleFunctor _ 0).map (transition n) ≫ finiteBeta (d (.finite n))
  supportedLegs : (Functor.const ℕᵒᵖ).obj ((S l E π .integral s)⟦(2 : ℤ)⟧) ⟶
    Functor.ofOpSequence
      (X := fun n => ((restriction l E π n s).obj
        (S l E π (.finite n) s))⟦(2 : ℤ)⟧) supportedTransition
  compactLegs : (Functor.const ℕᵒᵖ).obj ((C l E π .integral s)⟦(2 : ℤ)⟧) ⟶
    Functor.ofOpSequence
      (X := fun n => ((restriction l E π n s).obj
        (C l E π (.finite n) s))⟦(2 : ℤ)⟧) compactTransition
  supported_limit : Pretriangulated.IsHomotopyLimit
    (Cone.mk ((S l E π .integral s)⟦(2 : ℤ)⟧) supportedLegs)
  compact_limit : Pretriangulated.IsHomotopyLimit
    (Cone.mk ((C l E π .integral s)⟦(2 : ℤ)⟧) compactLegs)
  alpha : ∀ n : ℕ, (d .integral).alpha ≫ supportedLegs.app (op n) =
    coefficientLegs.app (op n) ≫ finiteAlpha (d (.finite n))
  beta : ∀ n : ℕ, (d .integral).beta ≫ compactLegs.app (op n) =
    coefficientLegs.app (op n) ≫ finiteBeta (d (.finite n))
  counit : ∀ n : ℕ,
    (forgetSupports l E π .integral s)⟦(2 : ℤ)⟧' ≫ compactLegs.app (op n) =
      supportedLegs.app (op n) ≫
        ((restriction l E π n s).map (forgetSupports l E π (.finite n) s))⟦(2 : ℤ)⟧'

/-- The complete sheaf-valued assertion: actual supported counits are invertible;
finite Cartier classes and retained origins are the specified ones; all three
inverse-limit cones and both scalar-extension squares retain their source and
class normalizations. Source: Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
structure Comparison (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (s : Scheme.{u}) where
  cartier : ∀ b : Stage, Cartier l E π b s
  counit_iso : ∀ b : Stage, IsIso (forgetSupports l E π b s)
  finite_cartier : ∀ n : ℕ, FiniteCartierNormalized l E π n s (cartier (.finite n))
  finite_origin : ∀ n : ℕ, FiniteOrigin l E π n s
  integral : IntegralComparison l E π s cartier
  rational : CartierScalar (l := l) (E := E) (π := π) (s := s)
    (b := .integral) (b' := .rational) (padicIntegersRingObjToContinuousMapRingObj l E)
    (DiagonalCoefficients.rationalLineMap l E (WeilConjectures.PurityFiniteSetting.Line s))
    (cartier .integral) (cartier .rational)
  closure : CartierScalar (l := l) (E := E) (π := π) (s := s)
    (b := .rational) (b' := .closure) (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
    (DiagonalCoefficients.closureLineMap l E (WeilConjectures.PurityFiniteSetting.Line s))
    (cartier .rational) (cartier .closure)

/-- The canonical supported-to-compact comparison is an isomorphism, with all
coefficient and specified-class clauses in the ordinary sheaf-valued derived
categories. The base extension Omega/k is arbitrary, not assumed of finite type.
The finite Cartier normalization is the Yoneda Cartier normalization of
lem-pur-divisor-class; by rankOne_local_calculation its residue is -1, since
that theorem sends the frame boundary of kappa(t) to +1.

Source: latest blueprint, thm-pur-rank-one-thom.proof.md, Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison).

Proof (the ten steps of the DAG):
1. Use the closed-support localization triangle, derived composition, and the
open/closed exact extension sequence for A^1 in P^1. Properness of the origin
identifies its support with its extension by zero, giving the displayed counit.
2. At each positive finite quotient use finite Tate descent, the canonical
etale/pro-etale direct-image mate and extension-by-zero comparison. These
apply over arbitrary algebraically closed Omega.
3. The local calculation and the Cartier boundary normalization identify the
supported Cartier source with A[-2]; its residue is -1 and hence a unit.
4. The independent finite P^1 unit/Chern splitting identifies the compact
object with A[-2]. Forgetting support sends the Cartier class to c1(O(1)),
so the compact image is a generator and the canonical counit is invertible.
5. Form the strict positive uniformizer quotient diagrams in R-module sheaves.
Repleteness and epimorphic transitions identify the coefficient and Tate
sheaves with their derived limits, including the prescribed projections.
6. The completed coefficient comparison and the ringed tower pushforward/limit
comparison identify ordinary direct image with the same projected limit.
7. Open extension by zero preserves the relevant derived limits; apply Rq_*
to obtain the compact comparison. The support fiber gives the supported one.
8. The integral-to-field coefficient is the flat localization telescope. Qcqs
continuity of direct image on the common bounded-below inputs and open tensor
projection identify both scalar mates and their units.
9. The closure coefficient is the finite-subextension-valued filtered colimit.
Finite free coefficient extensions, flatness and the same continuity identify
both closure scalar mates.
10. Relative Kummer Cartier classes commute with quotient reduction and scalar
extension. Their actual affine-line equations fix the integral and scalar
classes. Adjunction and the proper-supported counit give the alpha, beta and
u squares. As alpha and beta are isomorphisms, their normalization determines
all the displayed comparison maps and transitions uniquely. -/
theorem affineOriginSupportCompactComparison
    (K : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ K.p)
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K.k Ω] :
    Nonempty (Comparison l E π (Spec (CommRingCat.of Ω))) := by sorry

end AlgebraicGeometry.ProEtale.AffineOrigin
