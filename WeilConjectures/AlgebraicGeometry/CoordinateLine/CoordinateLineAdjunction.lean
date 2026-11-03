/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
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
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
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
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
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
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
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
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
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
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
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
public import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
public import Mathlib.Logic.Small.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleDiagonalCoefficientTriangles
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedDiagonalUnitSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization
public import WeilConjectures.AlgebraicGeometry.EtaleDiagonalTriangles
public import WeilConjectures.AlgebraicGeometry.EtaleProperSectionContraction
public import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
public import WeilConjectures.CategoryTheory.AdjunctionUnitTransport
public import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionIntegral
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
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
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
public import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
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
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedPairingPullback
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
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
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactProjectionFormula
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorIntegrationSiteComparison
import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineCounitTensor
import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAugmentationRealization
import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineConjugateExponents
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceCoordinateBoundaries
import WeilConjectures.Compactification.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Normalized coordinate-line adjunction and its actual counit

Source: main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, first sentences and final paragraph
(blueprint: lem-pur-coordinate-line-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor

namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

variable (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
variable (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)

/-- All normalized counit and transpose clauses in the source's finite-field domain.
Noetherianity is supplied from Geometry; invertibility of N is asserted here.
The positive exponent a is written r+1, covering exactly every a>=1.
Source: main-20261015, first sentences and final comparison paragraph
(blueprint: lem-pur-coordinate-line-adjunction). -/
def NormalizedAdjunction [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] : Prop :=
  ∃ hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)),
    NormalizedOrdinary (Ring P) (P.coefficients.l ^ (r + 1)) hA T
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT ∧
    ∀ (K : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
      (Ke : Etale.DerivedCategoryModule (Ring P) T)
      (hKe : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (Ring P)) T Ke)
      (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj),
      affineLinePurityComparison P T r hA aT K Ke hKe eK =
        comparedConjugate P T r hA hT K Ke eK ∧
      IsIso (affineLinePurityComparison P T r hA aT K Ke hKe eK)

/-- The source's geometric assertions for a single line, in the published models.
Source: polynomial-chart paragraph and proof Step 1
(blueprint: lem-pur-coordinate-line-adjunction). -/
def Geometry : Prop :=
  IsNoetherian T ∧ IsNoetherian (AffineSpace PUnit.{u + 1} T) ∧
    IsNoetherian (ProjectiveLine T) ∧
    (∃ dT dX dP : ℕ, topologicalKrullDim T ≤ (dT : WithBot ℕ∞) ∧
      topologicalKrullDim (AffineSpace PUnit.{u + 1} T) ≤ (dX : WithBot ℕ∞) ∧
      topologicalKrullDim (ProjectiveLine T) ≤ (dP : WithBot ℕ∞)) ∧
    IsSeparated (AffineSpace PUnit.{u + 1} T ↘ T) ∧
    LocallyOfFiniteType (AffineSpace PUnit.{u + 1} T ↘ T) ∧
    QuasiCompact (AffineSpace PUnit.{u + 1} T ↘ T) ∧
    IsOpenImmersion (ProjectiveLine.affineChart T) ∧
    IsProper (ProjectiveLine T ↘ T) ∧
    ProjectiveLine.affineChart T ≫ (ProjectiveLine T ↘ T) =
      (AffineSpace PUnit.{u + 1} T ↘ T)

/-- Canonical exponent comparison through the specified inverse-limit Tate line.
Source: independence of the annihilating exponent, proof Steps 2 and 6
(blueprint: lem-pur-coordinate-line-adjunction). -/
@[irreducible]
def sourceExponentIso (r' : ℕ)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
    (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P)))) :
    source P.coefficients.l P.extension (P.level - 1) T r hA K ≅
      source P.coefficients.l P.extension (P.level - 1) T r' hA' K := by
  exact tensorCoefficientIso (Ring P) T _ _
    (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r hA hP hX ≪≫
      (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r' hA' hP hX).symm) K

/-- All clauses of the coordinate-line statement, including universal Cartier geometry
and the canonical exponent comparison of the actual gamma maps.
Source: main-20261015, source paragraph (blueprint: lem-pur-coordinate-line-adjunction). -/
def CoordinateLineStatement (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] : Prop :=
  Geometry T ∧ (∀ d : ℕ, Geometry (iteratedAffineLine T d)) ∧
    (∀ (B : Scheme.{u}) (d : ℕ),
      iteratedAffineLineProj B (d + 1) =
        (AffineSpace PUnit.{u + 1} (iteratedAffineLine B d) ↘ iteratedAffineLine B d) ≫
          iteratedAffineLineProj B d ∧
      Scheme.Hom.toIteratedAffineLine (𝟙 B) (fun _ : Fin (d + 1) ↦ 0) =
        Scheme.Hom.toIteratedAffineLine (𝟙 B) (fun _ : Fin d ↦ 0) ≫
          AffineSpace.zeroSection PUnit.{u + 1} (iteratedAffineLine B d) ∧
      AffineSpace.zeroSection PUnit.{u + 1} (iteratedAffineLine B d) ≫
        (AffineSpace PUnit.{u + 1} (iteratedAffineLine B d) ↘ iteratedAffineLine B d) =
          𝟙 (iteratedAffineLine B d)) ∧
    (∀ (B : Scheme.{u}) (d : ℕ) (i : Fin d),
      (((iteratedAffineLine B d).zeroLocusSubschemeι
        {iteratedAffineLine.coord B d i}).ker).IsInvertible) ∧
    ((P.coefficients.l ^ P.level : ℕ) : Ring P) = 0 ∧
    (∀ (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0),
      ∀ [IsNoetherian T], NormalizedAdjunction P T r hA aT) ∧
    (∀ (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
      (U : Scheme.{u}) (aU : U ⟶ Spec (.of P.field.k)),
      LocallyOfFiniteType aU → QuasiCompact aU → IsSeparated aU →
      ∃ C : Scheme.Cover.{u} Scheme.etalePrecoverage U, ∀ (i : C.I₀) (m : ℤ),
        Nonempty ((Scheme.finiteEtaleTateSheaf (Ring P) (P.coefficients.l ^ (r + 1)) U hA m).over
          (C.etalePrecoverageToEtale i) ≅
          (constantSheaf (U.smallEtaleTopology.over (C.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} (Ring P))).obj (ModuleCat.of (Ring P) (Ring P)))) ∧
    (∀ (U : Scheme.{u}) (hU : IsUnit (P.coefficients.l : Γ(U, ⊤)))
      (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) (m : ℕ),
      Scheme.IsFiniteTateSiteComparison P.coefficients.l P.extension (P.level - 1) U r hA m
        (twistComparison P.coefficients.l P.extension (P.level - 1) U hU r hA m)) ∧
    ∀ (r r' : ℕ)
      (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
      (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
      (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
      (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
      (K : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
      (Ke : Etale.DerivedCategoryModule (Ring P) T)
      (hKe : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (Ring P)) T Ke)
      (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj),
      (sourceExponentIso P T r hA r' hA' hP hX K.obj).hom ≫
        affineLinePurityComparison P T r' hA' aT K Ke hKe eK =
      affineLinePurityComparison P T r hA aT K Ke hKe eK

private theorem geometry_of_finiteType
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] : Geometry T := by
  have : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  have : IsNoetherian (AffineSpace PUnit.{u + 1} T) :=
    isNoetherian_of_locallyOfFiniteType (AffineSpace PUnit.{u + 1} T ↘ T)
  have : IsNoetherian (ProjectiveLine T) :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine T ↘ T)
  obtain ⟨dT, hdT⟩ := exists_topologicalKrullDim_le aT
  obtain ⟨dX, hdX⟩ := exists_topologicalKrullDim_le
    ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)
  obtain ⟨dP, hdP⟩ := exists_topologicalKrullDim_le ((ProjectiveLine T ↘ T) ≫ aT)
  exact ⟨inferInstance, inferInstance, inferInstance,
    ⟨dT, dX, dP, hdT, hdX, hdP⟩, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ProjectiveLine.affineChart_over T⟩

private theorem level_annihilates (P : WeilConjectures.PurityFiniteSetting.{u}) :
    ((P.coefficients.l ^ (P.level) : ℕ) : Ring P) = 0 := by
  let O := Padic.coefficientExtensionIntegers P.coefficients.l P.extension
  let m := Padic.coefficientExtensionMaximalIdeal P.coefficients.l P.extension
  have hs := (Padic.coefficientExtensionIntegers_dvr P.coefficients.l P.extension).choose_spec
  have hm : (P.coefficients.l : O) ∈ m := by
    apply (hs.2.1 (P.coefficients.l : O)).2
    have he := spectralNorm_extends (K := Padic P.coefficients.l) (L := P.extension)
      (P.coefficients.l : Padic P.coefficients.l)
    change spectralNorm (Padic P.coefficients.l) P.extension (P.coefficients.l : P.extension) < 1
    simpa only [map_natCast] using
      he.trans_lt (Padic.norm_p_lt_one (p := P.coefficients.l))
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer
      P.coefficients.l P.extension} : Set O) = m := by
    exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  apply ULift.down_injective
  change ((P.coefficients.l ^ (P.level) : ℕ) :
    Padic.coefficientExtensionRing P.coefficients.l P.extension ((P.level - 1) + 1)) = 0
  rw [Nat.sub_add_cancel P.level_pos,
    ← map_natCast (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level)),
    Ideal.Quotient.eq_zero_iff_mem]
  change ((P.coefficients.l ^ (P.level) : ℕ) : O) ∈
    Ideal.span ({Padic.coefficientExtensionUniformizer P.coefficients.l P.extension} : Set O) ^
      P.level
  rw [hg, Nat.cast_pow]
  exact Ideal.pow_mem_pow hm P.level

private theorem specified_transpose_compatible
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).IsLeftAdjoint]
    (M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (W : Scheme.FixedEtaleOriginWitness X A M)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (Ke : Etale.DerivedCategoryModule A Y)
    (eK : (VectorIntegrationSite.comparison A Y).obj Ke ≅ K.obj)
    (ae : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj W.complex.obj ⟶ Ke)
    (ap : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj M.obj ⟶ K.obj)
    (h : (fixedCompactSupportComparisonIso A c).inv.app W.complex ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).map W.iso.hom ≫ ap =
      (VectorIntegrationSite.comparison A Y).map ae ≫ eK.hom) :
    specifiedExceptionalHomEquiv A c M W K ap =
      W.iso.inv ≫ (VectorIntegrationSite.comparison A X).map
        ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c)).homEquiv _ Ke ae) ≫
        boundedSiteRho A (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).rightAdjoint Ke ≫
        (sfFiniteExceptionalAt A c).map eK.hom := by
  dsimp only [specifiedExceptionalHomEquiv, Equiv.trans_apply, Iso.homFromEquiv_apply,
    Equiv.ofBijective_apply, Functor.mapIso_symm, Iso.symm_inv]
  change W.iso.inv ≫
    (VectorIntegrationSite.comparison A X).map
      ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c)).homEquiv _ _
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj
          ((fixedCompactSupportComparisonIso A c).inv.app W.complex ≫
            (rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} A) c).map W.iso.hom ≫ ap))) = _
  rw [h]
  have he : (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj
      ((VectorIntegrationSite.comparison A Y).map ae ≫ eK.hom) =
      ae ≫ (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app Ke ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor.map eK.hom := by
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
    rw [← Category.assoc]
    congr 1
    exact ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.naturality ae).symm
  rw [he, Adjunction.homEquiv_naturality_right]
  simp only [Functor.map_comp, boundedSiteRho, sfFiniteExceptionalAt,
    Functor.comp_map]

private theorem comparedConjugate_isIso
    [IsNoetherian T]
    (hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    IsIso (comparedConjugate P T r hA hT K Ke eK) := by
  have hplus : DerivedCategory.TStructure.t.plus Ke := by
    exact hKe.1.1.1
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (Ring P)) T Ke hplus
  unfold comparedConjugate boundedSiteRho
  infer_instance

private theorem comparison_counit
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hN : 0 < N) (hB : IsUnit (N : Γ(B, ⊤)))
    (K : Etale.DerivedCategoryModule A B) :
    (Etale.affineTraceLineLeft A B).map ((comparison A N hA B hN hB).hom.app K) ≫
      (exceptionalAdjunction A B).counit.app K =
        (adjunction A N hA B hN hB).counit.app K := by
  unfold comparison
  simpa using conjugateEquiv_counit (adjunction A N hA B hN hB)
    (exceptionalAdjunction A B) (𝟙 _) K

private theorem comparison_transpose
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hN : 0 < N) (hB : IsUnit (N : Γ(B, ⊤)))
    (K : Etale.DerivedCategoryModule A B) :
    (comparison A N hA B hN hB).hom.app K =
      (exceptionalAdjunction A B).homEquiv _ K
        ((adjunction A N hA B hN hB).counit.app K) := by
  apply ((exceptionalAdjunction A B).homEquiv _ K).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact comparison_counit A N hA B hN hB K

-- Keep the fixed comparison and the chosen adjunction abstract during unification.
attribute [local irreducible] Adjunction.ofIsLeftAdjoint Adjunction.homEquiv
  Functor.rightAdjoint fixedCompactSupportComparisonIso specifiedExceptionalHomEquiv
  boundedSiteRho derivedComparisonAdjunction

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sourceWitness exceptionalAdjunction
  affineTraceLineCompactification Etale.affineTraceOpenLeft sfFiniteExceptionalAt

private theorem comparison_realization
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    affineLinePurityComparison P T r hA aT K Ke hKe eK =
      comparedConjugate P T r hA hT K Ke eK := by
  let M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} T))
        (ModuleCat.{u + 1} (Ring P))) :=
    ⟨_, source_plus P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke hKe eK⟩
  let W : Scheme.FixedEtaleOriginWitness (AffineSpace PUnit.{u + 1} T) (Ring P) M :=
    { complex := ⟨etaleSource P.coefficients.l P.extension (P.level - 1) T r hA Ke,
        etaleSource_plus P.coefficients.l P.extension (P.level - 1) T r hA Ke hKe⟩
      iso := sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke eK }
  let ae : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Ring P)) (affineTraceLineCompactification T)).obj W.complex.obj ⟶
        Ke := ((Etale.affineTraceLineLeft (Ring P) T).map (sourceCoordinates P T r hA Ke).hom ≫
      (adjunction (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT).counit.app Ke)
  let ap := (augmentation P.coefficients.l P.extension (P.level - 1) T r hA
      (primeUnit P T aT) P.field.k aT K.obj Ke hKe eK)
  have ha := (coordinate_line_augmentation_realization P T aT r hA K Ke hKe eK)
  have hh := specified_transpose_compatible (Ring P) (affineTraceLineCompactification T)
    M W K Ke eK ae ap ha
  have he :
      (exceptionalAdjunction (Ring P) T).homEquiv _ Ke
        ((Etale.affineTraceLineLeft (Ring P) T).map
          (sourceCoordinates P T r hA Ke).hom ≫
          (adjunction (Ring P) (P.coefficients.l ^ (r + 1)) hA T
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT).counit.app Ke) =
      (sourceCoordinates P T r hA Ke).hom ≫
        (comparison (Ring P) (P.coefficients.l ^ (r + 1)) hA T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT).hom.app Ke := by
    rw [Adjunction.homEquiv_naturality_left, comparison_transpose]
  have ht := congrArg (fun z ↦
    (sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke eK).inv ≫
      (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map z ≫
      boundedSiteRho (Ring P)
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
          (affineTraceLineCompactification T)).rightAdjoint Ke ≫
      (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification T)).map eK.hom) he
  unfold affineLinePurityComparison comparisonFromOrigin comparedConjugate
  dsimp only [sourceWitness]
  exact hh.trans ht

/-- The normalized coordinate-line adjunction, its actual counit, and the precise
pro-etale comparison, at every finite coefficient level and annihilating exponent.
Source: main-20261015, cor-pur-affine-space-zero-section-purity.proof.md,
first sentences and final paragraph (blueprint: lem-pur-coordinate-line-adjunction).

Proof:
1. Polynomial charts give finite-type separated affine projection, standard open
chart and proper projective projection. Finite type over k makes all three schemes
Noetherian of finite dimension. The same applies at every coordinate stage.
2. Write ell=varpi*b in O_E; its level-th power vanishes in A. Any allowed exponent
is invertible on the base. The finite-twist pullback theorem supplies rank-one lines,
their tensor powers and exponent-compatible comparisons with the specified twists.
3. Compose the actual open adjunction with the trace-normalized P1 adjunction.
Exact inverse-image composition and tensor pullback give rightComparison. The
composite-adjunction formula expresses its counit as Rq_* of the open counit,
followed by the normalized projective counit.
4. The open tensor isomorphism identifies the open counit on q*K tensor F with
identity tensor e_F: transpose both maps and use the open triangle identity.
Naturality of the proper projection map with e_F, and factorization of the compact
projection map, then give the displayed inverse-projection tensor integration
formula. Finite Tor of K and bounded constructibility of the Tate line make PF
invertible. Use the specified symmetries; the only shifted line has even shift 2.
5. Conjugate the identity of Rp_! under this adjunction and its Brown right adjoint.
The mates theorem gives a natural isomorphism with component the transpose of the
actual counit; its counit equation fixes the adjunction-preserving normalization.
6. The augmentation-realization lemma carries the actual open/projective counit
through the specified compact-support comparison. Expand the restricted Hom chain;
comparison-adjunction unit naturality and Brown Hom naturality identify its transpose
with comparedConjugate. The comparison unit is invertible on the bounded-below Ke,
so every factor of this map is invertible. This works for each retained representative
in the statement. The exponent lemma identifies the ordinary conjugates in their
actual source coordinates; postcompose with the common unit and representative maps.
The resulting equality is exactly the stipulated exponent compatibility of gamma.
-/
theorem coordinateLineAdjunction (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] :
    CoordinateLineStatement P T aT := by
  have : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  change Geometry T ∧ _
  refine ⟨geometry_of_finiteType P T aT,
    (fun d ↦ geometry_of_finiteType P _ (iteratedAffineLineProj T d ≫ aT)),
    ?_, ?_, level_annihilates P, ?_, ?_, ?_, ?_⟩
  · intro B d
    refine ⟨rfl, ?_, AffineSpace.zeroSection_over _ _⟩
    simp only [Scheme.Hom.toIteratedAffineLine_succ, AffineSpace.zeroSection,
      AffineSpace.comp_homOfVector, Category.comp_id]
    congr 1
    funext i
    exact (map_zero _).symm
  · intro B d i
    exact AffineZeroPurity.coordinate_cartier B d i
  · intro r hA _
    let hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)) := by
      simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1)
    refine ⟨hT, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact coordinate_line_counit_tensor (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT
    · exact comparison_counit (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT
    · exact comparison_transpose (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT
    · intro K Ke hKe eK
      have he := comparison_realization P T r hA aT hT K Ke hKe eK
      refine ⟨he, ?_⟩
      rw [he]
      exact comparedConjugate_isIso P T r hA hT K Ke hKe eK
  · intro r hA U aU _ _ _
    obtain ⟨_, _, _, h, _⟩ := Scheme.etaleFiniteTwistPullback (Ring P)
      (P.coefficients.l ^ (r + 1)) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA
    exact h U (by simpa only [Nat.cast_pow] using (primeUnit P U aU).pow (r + 1))
  · exact (twistCompatibility P.coefficients.l P.extension (P.level - 1)).1
  · intro r r' hA hA' hP hX K Ke hKe eK
    let hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)) := by
      simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1)
    let hT' : IsUnit ((P.coefficients.l ^ (r' + 1) : ℕ) : Γ(T, ⊤)) := by
      simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r' + 1)
    rw [comparison_realization P T r hA aT hT K Ke hKe eK,
      comparison_realization P T r' hA' aT hT' K Ke hKe eK]
    unfold comparedConjugate sourceExponentIso
    have he := coordinate_line_conjugate_exponents P T aT r r' hA hA' hP hX
      K Ke hKe eK
    simpa only [Category.assoc] using congrArg
      (fun z ↦ z ≫ boundedSiteRho (Ring P)
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
          (affineTraceLineCompactification T)).rightAdjoint Ke ≫
        (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification T)).map eK.hom) he

end AlgebraicGeometry.ProEtale.CoordinateLine
