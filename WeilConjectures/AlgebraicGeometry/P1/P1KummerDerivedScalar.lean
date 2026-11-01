/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1.P1KummerScalarEndpointComposition
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
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
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
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
public import Mathlib.CategoryTheory.Adjunction.Basic
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
import WeilConjectures.AlgebraicGeometry.P1.P1KummerScalarEndpointExistence
import WeilConjectures.AlgebraicGeometry.P1.P1KummerChernScalar

/-! # Derived scalar transitivity for the projective-line Kummer class

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: the Kummer and diagonal classes over B
are the images of those over A; retained splitting Step 2
(blueprint: lem-sp-p1-kummer-derived-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The canonical ordinary-etale derived scalar comparison carries the fixed projective-line
Kummer Chern arrow from coefficients `A` to `B` through an arbitrary finite ring map.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts and retained splitting Step 2
(blueprint: lem-sp-p1-kummer-derived-scalar).

Proof steps:
1. Apply normalized endpoint existence to the residue-to-`A`, composite residue-to-`B`, and
   `A`-to-`B` maps on `ProjectiveLine S`, and apply the scalar Chern theorem to the same
   residue arrow and each residue endpoint.
2. Apply endpoint composition to obtain the unit and shifted Tate-line equations for the
   specified canonical composition comparison.
3. Apply naturality of the canonical composition isomorphism to the fixed residue Chern
   arrow. Precompose by extension of the unit endpoint isomorphism, expand `chernImage`,
   substitute the two component equations, and cancel inverse pairs. This gives the final
   derived equality. The endpoint records are canonical by their insertion-normalization
   fields, so the argument also covers the identity map, `N = 1`, an empty scheme, and
   non-flat coefficient maps. -/
theorem p1KummerDerivedScalar
    (S : Scheme.{u}) [IsNoetherian S] (N : ℕ) (hN : 0 < N)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (c : ordinaryFiniteUnit (p1KummerResidue.{u} N) (ProjectiveLine S) ⟶
      (ordinaryFiniteLine (p1KummerResidue.{u} N) N
        (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N)
          (ZMod.natCast_self N)) (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec (p1KummerResidue.{u} N) N
      (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N)
        (ZMod.natCast_self N)) S (ordinaryFiniteP1_isUnit N S hS) c) :
    ∃ (eA : P1KummerScalarEndpoints
        (p1KummerResidueMap N A hA) N
        (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N)
          (ZMod.natCast_self N)) hA (ProjectiveLine S))
      (eB : P1KummerScalarEndpoints
        (φ.comp (p1KummerResidueMap N A hA)) N
        (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N)
          (ZMod.natCast_self N)) hB (ProjectiveLine S))
      (e : P1KummerScalarEndpoints φ N hA hB (ProjectiveLine S)),
      ordinaryFiniteP1ChernSpec A N hA S (ordinaryFiniteP1_isUnit N S hS)
          (eA.chernImage c) ∧
        ordinaryFiniteP1ChernSpec B N hB S (ordinaryFiniteP1_isUnit N S hS)
          (eB.chernImage c) ∧
        ((scalarExtension φ (ProjectiveLine S)).map eA.unitIso.hom ≫ e.unitIso.hom =
          (ProEtale.pbcFixedScalarExtensionComp
            (ProjectiveLine S).smallEtaleTopology
            (p1KummerResidueMap N A hA) φ
            (φ.comp (p1KummerResidueMap N A hA)) rfl).hom.app
            (ordinaryFiniteUnit (p1KummerResidue.{u} N) (ProjectiveLine S)) ≫
            eB.unitIso.hom) ∧
        ((scalarExtension φ (ProjectiveLine S)).map eA.shiftedLineIso.hom ≫
            e.shiftedLineIso.hom =
          (ProEtale.pbcFixedScalarExtensionComp
            (ProjectiveLine S).smallEtaleTopology
            (p1KummerResidueMap N A hA) φ
            (φ.comp (p1KummerResidueMap N A hA)) rfl).hom.app
            ((ordinaryFiniteLine (p1KummerResidue.{u} N) N
              (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N)
                (ZMod.natCast_self N)) (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
            eB.shiftedLineIso.hom) ∧
        ((scalarExtension φ (ProjectiveLine S)).map (eA.chernImage c) ≫
            e.shiftedLineIso.hom = e.unitIso.hom ≫ eB.chernImage c) := by
  let P := ProjectiveLine S
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let hP : IsUnit (N : Γ(P, ⊤)) := ordinaryFiniteP1_isUnit N S hS
  let hRes : (N : p1KummerResidue.{u} N) = 0 :=
    congrArg ULift.up (ZMod.natCast_self N)
  obtain ⟨eA⟩ := p1KummerScalarEndpointExistence P N hN hP
    (p1KummerResidue.{u} N) A (p1KummerResidueMap N A hA) hRes hA
  obtain ⟨eB⟩ := p1KummerScalarEndpointExistence P N hN hP
    (p1KummerResidue.{u} N) B (φ.comp (p1KummerResidueMap N A hA)) hRes hB
  obtain ⟨e⟩ := p1KummerScalarEndpointExistence P N hN hP A B φ hA hB
  have hcA := p1KummerChernScalar hP eA c hc
  have hcB := p1KummerChernScalar hP eB c hc
  have hcomp := p1KummerScalarEndpointComposition eA eB e
  refine ⟨eA, eB, e, hcA, hcB, hcomp.1, hcomp.2, ?_⟩
  let k := ProEtale.pbcFixedScalarExtensionComp
      P.smallEtaleTopology (p1KummerResidueMap N A hA) φ
      (φ.comp (p1KummerResidueMap N A hA)) rfl
  have hn := k.hom.naturality c
  have hunit :
      (scalarExtension φ P).map eA.unitIso.inv ≫ k.hom.app
          (ordinaryFiniteUnit (p1KummerResidue.{u} N) P) =
        e.unitIso.hom ≫ eB.unitIso.inv := by
    apply (cancel_mono eB.unitIso.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hcomp.1]
    simp
  calc
    (scalarExtension φ P).map (eA.chernImage c) ≫ e.shiftedLineIso.hom =
        (scalarExtension φ P).map eA.unitIso.inv ≫
          ((scalarExtension φ P).map
            ((scalarExtension (p1KummerResidueMap N A hA) P).map c) ≫
            k.hom.app ((ordinaryFiniteLine (p1KummerResidue.{u} N) N hRes P)⟦(2 : ℤ)⟧)) ≫
          eB.shiftedLineIso.hom := by
      have hh := congrArg
        (fun z ↦ (scalarExtension φ P).map eA.unitIso.inv ≫
          (scalarExtension φ P).map
            ((scalarExtension (p1KummerResidueMap N A hA) P).map c) ≫ z)
        hcomp.2
      simpa only [P1KummerScalarEndpoints.chernImage, Functor.map_comp,
        Category.assoc] using hh
    _ = (scalarExtension φ P).map eA.unitIso.inv ≫
          (k.hom.app (ordinaryFiniteUnit (p1KummerResidue.{u} N) P) ≫
            (scalarExtension (φ.comp (p1KummerResidueMap N A hA)) P).map c) ≫
          eB.shiftedLineIso.hom := by
      have hh := congrArg
        (fun z ↦ (scalarExtension φ P).map eA.unitIso.inv ≫ z ≫ eB.shiftedLineIso.hom) hn
      simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using hh
    _ = e.unitIso.hom ≫ eB.unitIso.inv ≫
          (scalarExtension (φ.comp (p1KummerResidueMap N A hA)) P).map c ≫
          eB.shiftedLineIso.hom := by
      have hh := congrArg
        (fun z ↦ z ≫ (scalarExtension (φ.comp (p1KummerResidueMap N A hA)) P).map c ≫
          eB.shiftedLineIso.hom) hunit
      simpa only [Category.assoc] using hh
    _ = e.unitIso.hom ≫ eB.chernImage c := by
      simp [P1KummerScalarEndpoints.chernImage]

end AlgebraicGeometry.Etale
