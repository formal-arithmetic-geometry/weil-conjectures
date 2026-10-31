/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1CompactificationFibre
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.AlgebraicGeometry.PurityFrameKummer
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassScalarFaithfulness
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctMate
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineConstantCoefficientGenerator
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteGeometricPointHomology
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1FibreHomologyCard
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalTriangles
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalIntegral
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummerSupplement
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits
public import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalPicard
public import WeilConjectures.AlgebraicGeometry.P1DiagonalLocalIdeal
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedChernNormalization
public import WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.CategoryTheory.SectionConjugateComparison
public import WeilConjectures.CategoryTheory.SectionProjectionUnitSupplement
public import Mathlib.Logic.Small.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleDiagonalCoefficientTriangles
public import WeilConjectures.AlgebraicGeometry.EtaleSupportedDiagonalUnitSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization
public import WeilConjectures.AlgebraicGeometry.EtaleDiagonalTriangles
public import WeilConjectures.AlgebraicGeometry.EtaleProperSectionContraction
public import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
public import WeilConjectures.CategoryTheory.AdjunctionUnitTransport
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionIntegral
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.GroupTheory.Torsion
public import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
public import WeilConjectures.AlgebraicGeometry.TorsionAssembly
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
public import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
public import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RestrictionRingedToposModuleDirectImageSupplement
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorization
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp
public import WeilConjectures.AlgebraicGeometry.EtaleKunnethSymmetricFactorization
public import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleKunnethTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRightRoute
public import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import WeilConjectures.AlgebraicGeometry.EtaleEvenLineSelfSymmetry
public import WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
public import Mathlib.Tactic.SuppressCompilation
public import WeilConjectures.AlgebraicGeometry.EtaleLineFlatBraiding
public import WeilConjectures.ConstructibleSheaf.InternalHom
public import WeilConjectures.AlgebraicGeometry.EtaleSecondCoordinateContraction
public import WeilConjectures.AlgebraicGeometry.EtaleTraceBaseChangeEvaluation
public import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceTensorInterchange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCounitCoefficient
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceEvaluationNormalization
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalTraceCoordinates
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux
public import WeilConjectures.AlgebraicGeometry.EtaleChartExchangePasting
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistComposition
public import WeilConjectures.CategoryTheory.ShiftedCompositeComparison
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Ring.Int.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceBaseChange
public import WeilConjectures.AlgebraicGeometry.EtaleExactExchangeComparison
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceScalarSquare
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounitComparisons
public import WeilConjectures.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMapsSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedPairingPullback
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.AlgebraicGeometry.EtaleFlatSingleTensorCompatibilityDataSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorNaturality
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorAssociativity
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorSymmetry
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
public import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackCounit
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
public import WeilConjectures.CategoryTheory.FlatPairingAssociativityAssembly
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.FlatPairingPullbackAssembly
public import WeilConjectures.AlgebraicGeometry.DerivedPairingOppositeShiftsPullback
public import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPullback
public import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPairing
public import WeilConjectures.AlgebraicGeometry.FiniteTwistFlatEvaluationPullback
public import WeilConjectures.AlgebraicGeometry.FlatSinglePairingSymmetricPullback
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDerivedRightUnitPullback
public import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedFactorComparisons
public import WeilConjectures.AlgebraicGeometry.FiniteShiftedLineSquare
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalFirstCoordinateExchange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalSecondCoordinateExchange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassComparison
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyTriangle
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.FiniteTateSiteDescent
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison

/-!
# The finite origin class and compact support

Source: blueprint sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2 (blueprint: lem-pur-finite-origin-forget-support).

The affine chart, excision and forget-supports map are those of P1CompactificationFibre.
All classes use the Kummer normalization and the actual derived support boundary.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.FiniteOrigin

open AlgebraicGeometry.Etale
open AlgebraicGeometry.Etale.P1CompactificationFibre

/-- The existing finite Tate line, at the exponent ell^n which kills every level-n
coefficient quotient. Source: blueprint Step 2
(blueprint: lem-pur-finite-origin-forget-support). -/
abbrev F (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  Scheme.finiteEtaleTateLine T P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates

/-- The existing degree-zero embedding of the finite Tate line.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev K (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (DerivedCategory.singleFunctor _ 0).obj (F P T)

/-- Supported derived sections on the affine chart.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev supported (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :=
  (rightDerivedSectionsWithSupport (C P.Coefficient) (z S)).obj
    (K P (𝔸(PUnit.{u + 1}; S)))

/-- Derived compact support via the specified projective compactification.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev compact (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :=
  (rightDerivedGlobalSections (C P.Coefficient) (ProjectiveLine S)).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((openImmersionLowerShriek (C P.Coefficient) (j S)).obj
        (F P (𝔸(PUnit.{u + 1}; S)))))

/-- The precise excision-then-kernel-inclusion morphism defining u.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def forget (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    supported P S ⟶ compact P S :=
  (excision S P.Coefficient (F P (𝔸(PUnit.{u + 1}; S)))).hom ≫
    (forgetSupport S P.Coefficient).app _

/-- Projective cohomology with the same finite twist.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev projective (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :=
  (rightDerivedGlobalSections (C P.Coefficient) (ProjectiveLine S)).obj
    (K P (ProjectiveLine S))

/-- Evaluate a derived class of modules on one, with the standard homology shift.
Source: blueprint Step 2, interpretation of cohomology classes
(blueprint: lem-pur-finite-origin-forget-support). -/
def element (A : Type (u + 1)) [CommRing A]
    (L : DerivedCategory (C A)) (q : ℤ)
    (c : (DerivedCategory.singleFunctor (C A) 0).obj (ModuleCat.of A A) ⟶ L⟦q⟧) :
    (DerivedCategory.homologyFunctor (C A) q).obj L :=
  (((DerivedCategory.singleFunctorCompHomologyFunctorIso (C A) 0).inv.app
      (ModuleCat.of A A) ≫ (DerivedCategory.homologyFunctor (C A) 0).map c) ≫
    ((DerivedCategory.homologyFunctor (C A) 0).shiftIso q 0 q (by simp)).hom.app L) (1 : A)

/-- Realize a global class using the derived constant-sheaf/global-sections adjunction.
Source: blueprint Step 2; Stacks 03FD
(blueprint: lem-pur-finite-origin-forget-support). -/
def globalElement (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (L : DerivedCategory (Sheaf T.smallEtaleTopology (C A))) (q : ℤ)
    (c : ordinaryFiniteUnit A T ⟶ L⟦q⟧) :
    (DerivedCategory.homologyFunctor (C A) q).obj
      ((rightDerivedGlobalSections (C A) T).obj L) :=
  element A _ q
    ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (constantSheafΓAdj T.smallEtaleTopology (C A))).homEquiv _ _
          (((constantSheaf T.smallEtaleTopology (C A)).mapDerivedCategorySingleFunctor 0).hom.app
            (ModuleCat.of A A) ≫ c) ≫
      ((rightDerivedGlobalSections (C A) T).commShiftIso q).hom.app L)

/-- The extension-by-zero counit, with the normalized finite-twist restriction.
Source: blueprint Step 2, compactification identification
(blueprint: lem-pur-finite-origin-forget-support). -/
def coefficientInclusion (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (hP : IsUnit (P.diagonalExponent : Γ(ProjectiveLine S, ⊤))) :
    (openImmersionLowerShriek (C P.Coefficient) (j S)).obj
        (F P (𝔸(PUnit.{u + 1}; S))) ⟶ F P (ProjectiveLine S) :=
  ((openImmersionLowerShriekAdjunction (C P.Coefficient) (j S)).homEquiv _ _).symm
    ((t.line (j S) hP).inv ≫
      (upperStarIsoOpenImmersionRestriction (C P.Coefficient) (j S)).hom.app _)

/-- The canonical map from compact to projective cohomology. Only its degree-two
map is asserted invertible. Source: blueprint Step 2
(blueprint: lem-pur-finite-origin-forget-support). -/
def toProjective (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (hP : IsUnit (P.diagonalExponent : Γ(ProjectiveLine S, ⊤))) :
    compact P S ⟶ projective P S :=
  (rightDerivedGlobalSections (C P.Coefficient) (ProjectiveLine S)).map
    ((DerivedCategory.singleFunctor _ 0).map (coefficientInclusion P S t hP))

/-- The origin divisor class in the canonical supported-Hom realization.
The Ext representative is the existing normalized relative Cartier Kummer boundary.
Source: lem-pur-divisor-class, relative construction and local equation
(blueprint: lem-pur-finite-origin-forget-support). -/
def divisorElement (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (c : Abelian.Ext
      ((lowerStar (C P.Coefficient) (z S)).obj (ordinaryFiniteConstant P.Coefficient S))
      (F P (𝔸(PUnit.{u + 1}; S))) 2) :
    (DerivedCategory.homologyFunctor (C P.Coefficient) 2).obj (supported P S) :=
  (derivedSupportCohomologyAddEquiv P.Coefficient (z S)
    (K P (𝔸(PUnit.{u + 1}; S))) 2).symm c.hom

/-- The origin is an effective Cartier divisor on the one-dimensional affine space.
Source: blueprint Step 2, z=V(t).
Proof: z is a section of the projection p of the affine line, which is smooth of
relative dimension one. The closed subscheme cut out by the ideal of z is isomorphic to
the base through p, so it is finite and flat over the base; the finite-flat criterion
for sections of smooth curves (RelativeEffectiveCartier) makes the ideal invertible.
(blueprint: lem-pur-finite-origin-forget-support). -/
theorem origin_isCartier (S : Scheme.{u}) : (z S).ker.IsInvertible := by
  let p : 𝔸(PUnit.{u + 1}; S) ⟶ S := 𝔸(PUnit.{u + 1}; S) ↘ S
  have hp : SmoothOfRelativeDimension 1 p := by
    simpa only [Nat.card_unique, Nat.card_ulift, Nat.card_fin] using
      AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} S
  let s := z S
  have hs : s ≫ p = 𝟙 S := AffineSpace.zeroSection_comp_over _ _
  let l := IsClosedImmersion.lift s s.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι s.ker).ge
  have hliso : IsIso l := IsClosedImmersion.isIso_lift s s.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι s.ker).symm
  have hl : s.ker.subschemeι ≫ p = l := by
    rw [← IsClosedImmersion.lift_fac s s.ker.subschemeι
      (Scheme.IdealSheafData.ker_subschemeι s.ker).ge, Category.assoc, hs,
      Category.comp_id]
  have : IsIso (s.ker.subschemeι ≫ p) := hl ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    inferInstance inferInstance inferInstance

/-- The normalized Cartier class of the origin, using the unique relative Kummer
class from the divisor-class dependency. Source: lem-pur-divisor-class and Step 2
(blueprint: lem-pur-finite-origin-forget-support). -/
def cl (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (hX : IsUnit (P.diagonalExponent : Γ(𝔸(PUnit.{u + 1}; S), ⊤))) :=
  divisorElement P S
    (ordinary_supported_kummer_uniqueBoundary (𝔸(PUnit.{u + 1}; S)) P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates hX (z S) (origin_isCartier S)).choose

/-- The coordinate basic open is precisely the complement of the origin.
Source: blueprint Step 2, X minus V(t).
Proof: AffineSpace.range_zeroSection identifies the image with simultaneous vanishing
of the coordinates. The index type PUnit has one element, so this is the vanishing
of t. The basic open immersion has exactly the complementary image.
(blueprint: lem-pur-finite-origin-forget-support). -/
theorem origin_complement (S : Scheme.{u}) :
    Set.range (z S).base =
      (Set.range ((𝔸(PUnit.{u + 1}; S)).basicOpen
        (AffineSpace.coord S PUnit.unit)).ι.base)ᶜ := by
  rw [Scheme.Opens.range_ι, AffineSpace.range_zeroSection]
  ext y
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  rw [Unique.forall_iff]
  have h : (default : PUnit.{u + 1}) = PUnit.unit := Subsingleton.elim _ _
  rw [h]
  change (¬ y ∈ 𝔸(PUnit.{u + 1}; S).basicOpen (AffineSpace.coord S PUnit.unit)) ↔
    (¬ y ∈ 𝔸(PUnit.{u + 1}; S).basicOpen (AffineSpace.coord S PUnit.unit))
  exact Iff.rfl

/-- The actual coordinate Kummer boundary: Yoneda composition with the canonical
open-closed coefficient extension. Its sign is therefore fixed independently of cl.
The Kummer class, constant comparisons and twist counit are the published ones.
Source: thm-pur-rank-one-local-calculation and blueprint Step 2
(blueprint: lem-pur-finite-origin-forget-support). -/
def boundary (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (a : S ⟶ Spec (.of P.field.k))
    (t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  let X := 𝔸(PUnit.{u + 1}; S)
  let U := X.basicOpen (AffineSpace.coord S PUnit.unit)
  let A := P.Coefficient
  let aX := (𝔸(PUnit.{u + 1}; S) ↘ S) ≫ a
  let hX := P.diagonalExponent_isUnit aX
  let eU := (Scheme.upperStarConstantSheafIso (C A) U.ι).app (ModuleCat.of A A)
  let eZ := (Scheme.upperStarConstantSheafIso (C A) (z S)).app (ModuleCat.of A A)
  let c := (shortExact_openClosedShortComplex (C A) U.ι (z S)
    (ordinaryFiniteConstant A X) (origin_complement S)).extClass
  let κ := (P.frameKummerEtale U.toScheme (U.ι ≫ aX) (X.basicOpenUnit _)).mapExactFunctor
    (openImmersionLowerShriek (C A) U.ι)
  let ε := (openImmersionLowerShriek (C A) U.ι).map (t.line U.ι hX).inv ≫
    (openImmersionLowerShriekUpperStarAdjunction (C A) U.ι).counit.app (F P X)
  divisorElement P S
    ((Abelian.Ext.mk₀ ((lowerStar (C A) (z S)).map eZ.inv)).comp
      (c.comp (((Abelian.Ext.mk₀
        ((openImmersionLowerShriek (C A) U.ι).map eU.hom)).comp κ (zero_add 1)).comp
          (Abelian.Ext.mk₀ ε) (add_zero 1)) (rfl : 1 + 1 = 2)) (zero_add 2))

/-- The Chern class h=c1(O(1)), realized by the existing normalized datum.
Source: blueprint Step 2 and lem-asd-ordinary-finite-p1-adjunction
(blueprint: lem-pur-finite-origin-forget-support). -/
def h (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    {t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates}
    {hS : IsUnit (P.diagonalExponent : Γ(S, ⊤))}
    (d : OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t S hS) :=
  globalElement P.Coefficient (ProjectiveLine S) (K P (ProjectiveLine S)) 2 d.chern

/-- Global sections over an algebraically closed point are an equivalence.
This uses the existing constant-sheaf equivalence, with its actual adjunction.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
instance pointSections_isEquivalence (A : Type (u + 1)) [CommRing A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (C A)).IsEquivalence :=
  Adjunction.isEquivalence_right_of_isEquivalence_left
    (constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology (C A))

/-- The actual projective-line trace before taking degree-zero homology of the
shift by two. Leray and the constant-sheaf unit are the canonical comparisons.
Source: lem-asd-ordinary-finite-p1-adjunction, definition t_q=pr2 b_q^-1
(blueprint: lem-pur-finite-origin-forget-support). -/
def traceShifted (P : PurityFiniteSetting.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates}
    {hS : IsUnit (P.diagonalExponent : Γ(Spec (.of Ω), ⊤))}
    (d : OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t (Spec (.of Ω)) hS) :
    (projective P (Spec (.of Ω)))⟦(2 : ℤ)⟧ ⟶
      (DerivedCategory.singleFunctor (C P.Coefficient) 0).obj
        (ModuleCat.of P.Coefficient P.Coefficient) :=
  (Functor.commShiftIso
    (rightDerivedGlobalSections (C P.Coefficient)
      (ProjectiveLine (Spec (.of Ω)))) (2 : ℤ)).inv.app _ ≫
    (properDirectImageComparison (Spec (.of Ω)) P.Coefficient).inv.app _ ≫
    (rightDerivedGlobalSections (C P.Coefficient) (Spec (.of Ω))).map d.trace ≫
    (Functor.singleFunctorCompRightDerivedFunctorIso
      (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (C P.Coefficient))).hom.app _ ≫
    (DerivedCategory.singleFunctor (C P.Coefficient) 0).map
      (asIso ((constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology
        (C P.Coefficient)).unit.app (ModuleCat.of P.Coefficient P.Coefficient))).inv

/-- The coefficient-linear trace on H2(P,A(1)).
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def trace (P : PurityFiniteSetting.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates}
    {hS : IsUnit (P.diagonalExponent : Γ(Spec (.of Ω), ⊤))}
    (d : OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t (Spec (.of Ω)) hS) :
    (DerivedCategory.homologyFunctor (C P.Coefficient) 2).obj
        (projective P (Spec (.of Ω))) ⟶ ModuleCat.of P.Coefficient P.Coefficient :=
  ((DerivedCategory.homologyFunctor (C P.Coefficient) 0).shiftIso (2 : ℤ) 0 2
      (by simp)).inv.app _ ≫
    (DerivedCategory.homologyFunctor (C P.Coefficient) 0).map (traceShifted P Ω d) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (C P.Coefficient) 0).hom.app _

private theorem evaluation_eq_ΓRes {D : Type*} [Category* D]
    (J : GrothendieckTopology D) [HasTerminal D] {V : D} (hV : IsTerminal V)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (C A)]
    (G : Sheaf J (C A)) :
    (Sheaf.ΓNatIsoSheafSections J (C A) hV).hom.app G = G.ΓRes (op V) := by
  let adj := constantSheafΓAdj J (C A)
  let adj' := constantSheafAdj J (C A) hV
  have hc := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj adj' G
  apply (adj'.homEquiv _ G).symm.injective
  change (adj'.homEquiv _ G).symm ((adj.rightAdjointUniq adj').hom.app G) = _
  rw [hc]
  apply (adj'.homEquiv _ G).injective
  rw [Equiv.apply_symm_apply]
  change (CategoryTheory.constantPresheafAdj (C A) hV).homEquiv _ _
    ((sheafificationAdjunction J (C A)).homEquiv _ _ (adj.counit.app G)) = _
  rw [Adjunction.homEquiv_unit]
  change (𝟙 _) ≫ ((sheafificationAdjunction J (C A)).homEquiv _ _
    (adj.counit.app G)).app (op V) =
      ((sheafificationAdjunction J (C A)).homEquiv _ _
        ((adj.homEquiv _ G).symm (𝟙 _))).app (op V)
  rw [Category.id_comp, adj.homEquiv_symm_id]
  rfl

/-- Restriction to the etale subsite identifies the actual support kernels. The
kernel-inclusion equation uniquely specifies the comparison, rather than choosing
an abstract isomorphism. Source: blueprint Step 2, finite site comparison.
Proof: comparisonLowerStar is restriction on etale objects. Its sections at the
terminal object and at the open complement are the same sections. The canonical
global-sections comparison intertwines restriction, so it induces an isomorphism on
kernels. Its kernel-inclusion equation determines it uniquely, naturally in G.
(blueprint: lem-pur-finite-origin-forget-support). -/
theorem existsUnique_supportRestrictionIso (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    ∃! e : AlgebraicGeometry.ProEtale.comparisonLowerStar (C A) T ⋙
        globalSectionsWithSupport (C A) i ≅
          AlgebraicGeometry.ProEtale.globalSectionsWithSupport (C A) i,
      ∀ G : Sheaf (Scheme.ProEt.topology T) (C A),
        e.hom.app G ≫ (Sheaf.ΓSupportι (Scheme.ProEt.topology T) (C A)
            (op (Scheme.ProEt.mk i.openComplement.ι))).app G =
          (Sheaf.ΓSupportι T.smallEtaleTopology (C A)
            (op (Scheme.Etale.mk i.openComplement.ι))).app
              ((AlgebraicGeometry.ProEtale.comparisonLowerStar (C A) T).obj G) ≫
            (AlgebraicGeometry.ProEtale.comparisonLowerStarCompGlobalSectionsIso
              (C A) T).hom.app G := by
  let R := AlgebraicGeometry.ProEtale.comparisonLowerStar (C A) T
  let r := Sheaf.natTransΓRes T.smallEtaleTopology (C A)
    (op (Scheme.Etale.mk i.openComplement.ι))
  let r' := Sheaf.natTransΓRes (Scheme.ProEt.topology T) (C A)
    (op (Scheme.ProEt.mk i.openComplement.ι))
  let W := (Functor.whiskeringLeft _ _ (C A)).obj R
  let e := AlgebraicGeometry.ProEtale.comparisonLowerStarCompGlobalSectionsIso (C A) T
  have he : W.map r ≫ (Iso.refl _).hom = e.hom ≫ r' := by
    apply NatTrans.ext
    funext G
    simp only [W, r, r', NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
      Functor.whiskerLeft_app, Iso.refl_hom, Category.comp_id,
      Sheaf.natTransΓRes_app]
    let eE := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (C A)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
    let eP := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology T) (C A)
      (Scheme.ProEt.isTerminalMkId T)
    have hE := Sheaf.ΓRes_map (R.obj G)
      (MorphismProperty.Over.homMk i.openComplement.ι
        (by change i.openComplement.ι ≫ 𝟙 T = _; simp) :
          Scheme.Etale.mk i.openComplement.ι ⟶ Scheme.Etale.mk (𝟙 T)).op
    have hP := Sheaf.ΓRes_map G
      (MorphismProperty.Over.homMk i.openComplement.ι
        (by change i.openComplement.ι ≫ 𝟙 T = _; simp) :
          Scheme.ProEt.mk i.openComplement.ι ⟶ Scheme.ProEt.mk (𝟙 T)).op
    rw [← evaluation_eq_ΓRes _
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T) A (R.obj G)] at hE
    rw [← evaluation_eq_ΓRes _ (Scheme.ProEt.isTerminalMkId T) A G] at hP
    simp only [e, AlgebraicGeometry.ProEtale.comparisonLowerStarCompGlobalSectionsIso,
      Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Category.id_comp,
      Category.assoc]
    change _ = eE.hom.app (R.obj G) ≫ eP.inv.app G ≫ _
    rw [← hP, ← Category.assoc (eP.inv.app G), Iso.inv_hom_id_app,
      Category.id_comp]
    exact hE.symm
  let b : R ⋙ globalSectionsWithSupport (C A) i ≅
      AlgebraicGeometry.ProEtale.globalSectionsWithSupport (C A) i :=
    PreservesKernel.iso W r ≪≫ kernel.mapIso (W.map r) r' e (Iso.refl _) he
  have hb : b.hom ≫ Sheaf.ΓSupportι (Scheme.ProEt.topology T) (C A)
      (op (Scheme.ProEt.mk i.openComplement.ι)) =
    Functor.whiskerLeft R (Sheaf.ΓSupportι T.smallEtaleTopology (C A)
      (op (Scheme.Etale.mk i.openComplement.ι))) ≫ e.hom := by
    dsimp only [b, Iso.trans_hom, Sheaf.ΓSupportι]
    rw [Category.assoc, kernel.mapIso_hom, kernel.lift_ι]
    rw [← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rfl
  refine ⟨b, fun G ↦ NatTrans.congr_app hb G, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext G
  apply (cancel_mono ((Sheaf.ΓSupportι (Scheme.ProEt.topology T) (C A)
    (op (Scheme.ProEt.mk i.openComplement.ι))).app G)).mp
  exact (hb' G).trans (NatTrans.congr_app hb G).symm

/-- The support-kernel comparison fixed by its inclusion equation.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def supportRestrictionIso (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :=
  (existsUnique_supportRestrictionIso A i).choose

/-- The Leray comparison for supported sections of comparison direct image.
Source: blueprint Step 2, finite comparison
(blueprint: lem-pur-finite-origin-forget-support). -/
def supportLeray (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :=
  letI := (AlgebraicGeometry.ProEtale.comparisonAdjunction (C A) T).preservesKInjectiveComplexes
  Functor.rightDerivedFunctorCompIso'
    (AlgebraicGeometry.ProEtale.comparisonLowerStar (C A) T)
    (globalSectionsWithSupport (C A) i) (supportRestrictionIso A i)

/-- The canonical support comparison: apply supported sections to the derived
comparison unit, then the support Leray isomorphism.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def supportComparison (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (L : DerivedCategory (Sheaf T.smallEtaleTopology (C A))) :=
  (rightDerivedSectionsWithSupport (C A) i).map
      ((AlgebraicGeometry.ProEtale.derivedComparisonAdjunction (C A) T).unit.app L) ≫
    (supportLeray A i).hom.app _

/-- The canonical comparison on global derived sections, with the same derived
adjunction unit as the support comparison. Source: blueprint Step 2
(blueprint: lem-pur-finite-origin-forget-support). -/
def globalComparison (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (L : DerivedCategory (Sheaf T.smallEtaleTopology (C A))) :=
  (rightDerivedGlobalSections (C A) T).map
      ((AlgebraicGeometry.ProEtale.derivedComparisonAdjunction (C A) T).unit.app L) ≫
    (AlgebraicGeometry.ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso
      (C A) T).hom.app _

/-- The pro-etale supported object, with the finite sheaf pulled back by nu^*.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev proSupported (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :=
  (AlgebraicGeometry.ProEtale.rightDerivedSectionsWithSupport (C P.Coefficient) (z S)).obj
    ((AlgebraicGeometry.ProEtale.comparisonUpperStar (C P.Coefficient)
      (𝔸(PUnit.{u + 1}; S))).mapDerivedCategory.obj (K P (𝔸(PUnit.{u + 1}; S))))

/-- The finite comparison presentation of compact support on the pro-etale site.
The extension-by-zero comparison identifies this with Rq_* j_! of nu^* A(1).
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev proCompact (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :=
  (AlgebraicGeometry.ProEtale.rightDerivedGlobalSections (C P.Coefficient)
      (ProjectiveLine S)).obj
    ((AlgebraicGeometry.ProEtale.comparisonUpperStar (C P.Coefficient)
      (ProjectiveLine S)).mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj
        ((openImmersionLowerShriek (C P.Coefficient) (j S)).obj
          (F P (𝔸(PUnit.{u + 1}; S))))))

/-- The projective finite comparison object on the pro-etale site.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev proProjective (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :=
  (AlgebraicGeometry.ProEtale.rightDerivedGlobalSections (C P.Coefficient)
      (ProjectiveLine S)).obj
    ((AlgebraicGeometry.ProEtale.comparisonUpperStar (C P.Coefficient)
      (ProjectiveLine S)).mapDerivedCategory.obj (K P (ProjectiveLine S)))

/-- Canonical finite comparison on the support object.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def cZ (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    supported P S ⟶ proSupported P S :=
  supportComparison P.Coefficient (z S) (K P (𝔸(PUnit.{u + 1}; S)))

/-- Canonical finite comparison on compact support.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def cC (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) : compact P S ⟶ proCompact P S :=
  globalComparison P.Coefficient (ProjectiveLine S)
    ((DerivedCategory.singleFunctor _ 0).obj
      ((openImmersionLowerShriek (C P.Coefficient) (j S)).obj
        (F P (𝔸(PUnit.{u + 1}; S)))))

/-- Canonical finite comparison on projective cohomology.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def cP (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    projective P S ⟶ proProjective P S :=
  globalComparison P.Coefficient (ProjectiveLine S) (K P (ProjectiveLine S))

/-- The canonical finite comparisons are invertible on these bounded-below finite
coefficient objects. Source: blueprint Step 2, final comparison paragraph.
Proof: each of the three objects is a sheaf placed in degree zero, hence bounded
below, so bounded-below full faithfulness of comparison inverse image makes the
derived comparison unit at it invertible. Each comparison is that unit followed by
supported, resp. global, derived sections and a canonical Leray isomorphism (the
support Leray isomorphism for cZ, the global-sections one for cC and cP), so each
is invertible. No noetherianity of S is required for this site step.
(blueprint: lem-pur-finite-origin-forget-support). -/
theorem finiteComparison_isIso (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    IsIso (cZ P S) ∧ IsIso (cC P S) ∧ IsIso (cP P S) := by
  have hunit (T : Scheme.{u}) (G : Sheaf T.smallEtaleTopology (C P.Coefficient)) :
      IsIso ((AlgebraicGeometry.ProEtale.derivedComparisonAdjunction
        (C P.Coefficient) T).unit.app ((DerivedCategory.singleFunctor _ 0).obj G)) :=
    AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app _ _ _
      ⟨0, inferInstance⟩
  have := hunit (𝔸(PUnit.{u + 1}; S)) (F P (𝔸(PUnit.{u + 1}; S)))
  have := hunit (ProjectiveLine S)
    ((openImmersionLowerShriek (C P.Coefficient) (j S)).obj
      (F P (𝔸(PUnit.{u + 1}; S))))
  have := hunit (ProjectiveLine S) (F P (ProjectiveLine S))
  dsimp only [cZ, supportComparison, cC, cP, globalComparison]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The compactification forget-supports arrow after finite site comparison.
The theorem below asserts invertibility of cZ; hence inv is its actual inverse.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def proForget (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    proSupported P S ⟶ proCompact P S :=
  letI := (finiteComparison_isIso P S).1
  inv (cZ P S) ≫ forget P S ≫ cC P S

/-- The projective coefficient inclusion on the pro-etale site, obtained by applying
nu^* to the actual ordinary coefficient inclusion. Source: blueprint Step 2
(blueprint: lem-pur-finite-origin-forget-support). -/
def proToProjective (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (hP : IsUnit (P.diagonalExponent : Γ(ProjectiveLine S, ⊤))) :
    proCompact P S ⟶ proProjective P S :=
  (AlgebraicGeometry.ProEtale.rightDerivedGlobalSections (C P.Coefficient)
    (ProjectiveLine S)).map
      ((AlgebraicGeometry.ProEtale.comparisonUpperStar (C P.Coefficient)
        (ProjectiveLine S)).mapDerivedCategory.map ((DerivedCategory.singleFunctor _ 0).map
          (coefficientInclusion P S t hP)))

/-- The projective trace transported by the specified finite comparison.
The theorem asserts that this comparison is invertible, so inv is its inverse.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def proTrace (P : PurityFiniteSetting.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates}
    {hS : IsUnit (P.diagonalExponent : Γ(Spec (.of Ω), ⊤))}
    (d : OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t (Spec (.of Ω)) hS) :
    (DerivedCategory.homologyFunctor (C P.Coefficient) 2).obj
        (proProjective P (Spec (.of Ω))) ⟶ ModuleCat.of P.Coefficient P.Coefficient :=
  letI := (finiteComparison_isIso P (Spec (.of Ω))).2.2
  inv ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
    (cP P (Spec (.of Ω)))) ≫ trace P Ω d

/-- The complete per-degree assertion, including the canonical maps and signs.
H2(u) is exactly P1CompactificationFibre.u. The two trace equations use the trace
of the normalized projective-line datum after the compactification identification.
The pro-etale formula uses the same maps after the specified finite comparisons.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def Conclusion (P : PurityFiniteSetting.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [Algebra P.field.k Ω]
    (hX : IsUnit (P.diagonalExponent : Γ(𝔸(PUnit.{u + 1}; Spec (.of Ω)), ⊤)))
    {t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates}
    {hS : IsUnit (P.diagonalExponent : Γ(Spec (.of Ω), ⊤))}
    (d : OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t (Spec (.of Ω)) hS) : Prop :=
  cl P (Spec (.of Ω)) hX =
    -(boundary P (Spec (.of Ω)) (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) t) ∧
  IsIso ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (forget P (Spec (.of Ω)))) ∧
  (∀ q : ℤ, q ≠ 2 → IsZero ((DerivedCategory.homologyFunctor (C P.Coefficient) q).obj
      (compact P (Spec (.of Ω))))) ∧
  IsIso ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (toProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine)) ∧
  ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (forget P (Spec (.of Ω)) ≫
        toProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine))
      (cl P (Spec (.of Ω)) hX) = h P (Spec (.of Ω)) d ∧
  ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (forget P (Spec (.of Ω)) ≫
        toProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine))
      (boundary P (Spec (.of Ω))
        (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) t) = -(h P (Spec (.of Ω)) d) ∧
  trace P Ω d (((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (forget P (Spec (.of Ω)) ≫
        toProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine))
      (cl P (Spec (.of Ω)) hX)) = 1 ∧
  trace P Ω d (((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (forget P (Spec (.of Ω)) ≫
        toProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine))
      (boundary P (Spec (.of Ω))
        (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) t)) = -1 ∧
  (∃ b : Module.Basis Unit P.Coefficient
      ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).obj
        (compact P (Spec (.of Ω)))),
      b () = ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
        (forget P (Spec (.of Ω)))) (boundary P (Spec (.of Ω))
        (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) t)) ∧
  IsIso (cZ P (Spec (.of Ω))) ∧ IsIso (cC P (Spec (.of Ω))) ∧
  IsIso (cP P (Spec (.of Ω))) ∧
  (IsIso ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (proForget P (Spec (.of Ω)))) ∧
    (∀ q : ℤ, q ≠ 2 → IsZero ((DerivedCategory.homologyFunctor (C P.Coefficient) q).obj
      (proCompact P (Spec (.of Ω))))) ∧
    IsIso ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (proToProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine)) ∧
    cZ P (Spec (.of Ω)) ≫ proForget P (Spec (.of Ω)) =
      forget P (Spec (.of Ω)) ≫ cC P (Spec (.of Ω)) ∧
    toProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine ≫
        cP P (Spec (.of Ω)) =
      cC P (Spec (.of Ω)) ≫
        proToProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine ∧
    ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (proForget P (Spec (.of Ω)) ≫
        proToProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine))
      (((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
        (cZ P (Spec (.of Ω)))) (cl P (Spec (.of Ω)) hX)) =
      ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
        (cP P (Spec (.of Ω)))) (h P (Spec (.of Ω)) d) ∧
    ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (proForget P (Spec (.of Ω)) ≫
        proToProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine))
      (((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
        (cZ P (Spec (.of Ω)))) (boundary P (Spec (.of Ω))
        (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) t)) =
      -(((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
        (cP P (Spec (.of Ω)))) (h P (Spec (.of Ω)) d)) ∧
    proTrace P Ω d (((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (forget P (Spec (.of Ω)) ≫
        toProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine ≫
          cP P (Spec (.of Ω)))) (cl P (Spec (.of Ω)) hX)) = 1 ∧
    proTrace P Ω d (((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
      (forget P (Spec (.of Ω)) ≫
        toProjective P (Spec (.of Ω)) t d.invertible_on_projectiveLine ≫
          cP P (Spec (.of Ω)))) (boundary P (Spec (.of Ω))
        (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) t)) = -1 ∧
    (∃ b : Module.Basis Unit P.Coefficient
      ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).obj
        (proCompact P (Spec (.of Ω)))),
      b () = ((DerivedCategory.homologyFunctor (C P.Coefficient) 2).map
        (forget P (Spec (.of Ω)) ≫ cC P (Spec (.of Ω))))
          (boundary P (Spec (.of Ω))
        (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) t)))

/-- Finite forget-supports comparison at the geometric affine-line fibre, with the
origin class, degree-one projective class, trace values and basis assertion.
The finite setting contains k=Fbar_q, ell different from its characteristic, a finite
coefficient extension, and an arbitrary positive quotient level. Omega/k is any
algebraically closed extension, with no finite-type assumption.

Source: blueprint sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2 (blueprint: lem-pur-finite-origin-forget-support).

Proof:
1. Apply lem-amb-affine-space-top-trace with d=1 over Spec Omega. It gives compact
cohomology concentrated in degree two and free of rank one.
2. The supported rank-one calculation gives the coordinate boundary as a generator.
The local-equation formula of lem-pur-divisor-class identifies cl(z)=-partial kappa(t).
Finite Cartier pullback transports that normalization from k to Omega.
3. Excision of lem-pur-p1-compactification-fibre followed by the actual support
inclusion is forget. The restriction and unit identities of
lem-asd-ordinary-supported-kummer identify its projective image with c1(O(zbar)).
The point divisor has line bundle O(1), so this is h. The trace normalization in
lem-asd-ordinary-finite-p1-adjunction gives trace(h)=1. Thus the boundary has image
-h and trace -1, and its image is a generator. This proves invertibility of u.
4. Finite Tate descent, extension-by-zero comparison, the direct-image canonical
mate, and bounded-below site-comparison full faithfulness transport the maps.
The support comparison is the derived unit followed by support Leray, fixing its
normalization on kernels. Therefore its square commutes with forgetting support;
the global comparison square commutes with the coefficient counit. These squares
transport all vanishing, sign, trace and basis assertions to the pro-etale site.
-/
theorem finite_origin_forget_support (P : PurityFiniteSetting.{u})
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω] :
    ∃ (t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates)
      (d : OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t (Spec (.of Ω))
          (P.diagonalExponent_isUnit (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))))),
      IsIso (forget P (Spec (.of Ω))) ∧
      Conclusion P Ω
        (P.diagonalExponent_isUnit
          ((𝔸(PUnit.{u + 1}; Spec (.of Ω)) ↘ Spec (.of Ω)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω)))) d := by
  sorry

end WeilConjectures.PurityFiniteSetting.FiniteOrigin
