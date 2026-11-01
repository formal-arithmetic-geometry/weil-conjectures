/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.CompactProjectionExchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
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
import Mathlib.AlgebraicGeometry.Pullbacks
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
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
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
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceLinePurity
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange

/-! # The normalized vector integration mate

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an, Steps 5--7.
This isolates the ordinary unbounded adjunction argument from coefficient descent,
bounded coefficient realization and the arithmetic choice of an annihilator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.setOption false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
attribute [local instance 20000] Etale.sheafBraidedCategory

/-- The adjunct of another right adjoint's counit is the canonical comparison. -/
private theorem adjunct_counit_isIso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F ⊣ H) (K : D) :
    IsIso (a.homEquiv (H.obj K) K (b.counit.app K)) := by
  have he : a.homEquiv (H.obj K) K (b.counit.app K) =
      (b.rightAdjointUniq a).hom.app K := by
    apply (a.homEquiv _ _).symm.injective
    simpa only [Equiv.symm_apply_apply] using
      (Adjunction.homEquiv_symm_rightAdjointUniq_hom_app b a K).symm
  rw [he]
  infer_instance

/-- A counit transported through a specified source isomorphism has invertible adjunct. -/
private theorem normalized_adjunct_isIso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F ⊣ H) (K : D)
    {X : C} (e : X ≅ H.obj K) (c : F.obj X ⟶ K)
    (hc : c = F.map e.hom ≫ b.counit.app K) :
    IsIso (a.homEquiv X K c) := by
  rw [hc, a.homEquiv_naturality_left]
  have := adjunct_counit_isIso a b K
  infer_instance

private theorem adjunct_isIso_of_iso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F ⊣ H) (K : D)
    {X : C} (e : X ≅ H.obj K) (c : F.obj X ⟶ K)
    [IsIso c] [IsIso (b.counit.app K)] : IsIso (a.homEquiv X K c) := by
  let z : K ⟶ K := inv (F.map e.hom ≫ b.counit.app K) ≫ c
  have hz : c = (F.map e.hom ≫ b.counit.app K) ≫ z := by
    simp [z]
  rw [hz, a.homEquiv_naturality_right]
  have ha := normalized_adjunct_isIso a b K e
    (F.map e.hom ≫ b.counit.app K) rfl
  have hz : IsIso z := by dsimp [z]; infer_instance
  exact IsIso.comp_isIso' ha (Functor.map_isIso G z)

private theorem derived_isIso_of_cover (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : I) (y : U i), (a i).base y = x)
    {M N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (φ : M ⟶ N)
    (h : ∀ i, IsIso ((upperStar (ModuleCat.{u + 1} A) (a i)).mapDerivedCategory.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} A)
    a ha _ fun i ↦ ?_
  exact (NatIso.isIso_map_iff
    ((upperStar (ModuleCat.{u + 1} A) (a i)).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (DerivedCategory.homologyFunctor _ n)
      ((upperStar (ModuleCat.{u + 1} A) (a i)).mapDerivedCategory.map φ))

private theorem mate_naturality
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    {V : C ⥤ C'} {U : D ⥤ D'} (a : F ⊣ G) (b : F' ⊣ G')
    (e : TwoSquare V F F' U) (X : C) (K : D) (c : F.obj X ⟶ K) :
    V.map (a.homEquiv X K c) ≫ (mateEquiv a b e).app K =
      b.homEquiv _ _ (e.natTrans.app X ≫ U.map c) := by
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Equiv.symm_apply_apply]
  rw [mateEquiv_counit]
  have hn := e.natTrans.naturality (a.homEquiv X K c)
  dsimp only [Functor.comp_map] at hn
  change F'.map (V.map (a.homEquiv X K c)) ≫
    e.natTrans.app (G.obj K) ≫ U.map (a.counit.app K) = _
  rw [reassoc_of% hn]
  rw [← U.map_comp]
  have hc := (a.homEquiv X K).symm_apply_apply c
  rw [Adjunction.homEquiv_counit] at hc
  rw [hc]

private def affineLeftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    (c : Compactification (affineTraceProjection S d)) →
    affineTraceLeft A S d ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Nat.rec (motive := fun n ↦ ∀ c : Compactification (affineTraceProjection S n),
      affineTraceLeft A S n ≅
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun c ↦
      (Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).symm ≪≫
        rightDerivedLowerShriekOfCompactificationIso A
          (Compactification.ofIsProper (𝟙 S)) c)
    (fun n ih c ↦
      let cp := HasCompactification.compactification (affineTraceProjection S n)
      let ce := c.ofComp cp
      Functor.isoWhiskerRight
          (rightDerivedLowerShriekOfCompactificationIso A
            (affineTraceLineCompactification (affineTraceTower S n)) ce.restrict) _ ≪≫
        Functor.isoWhiskerLeft _ (ih cp) ≪≫
        rightDerivedLowerShriekOfCompactificationCompIso A cp ce ≪≫
        rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c) d

private theorem integration_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :
    IsIso (vectorBundleIntegration N hN A hA S hS d M) := by
  classical
  obtain ⟨t, D, htD, htrace⟩ := exists_affineSpaceTopTrace N hN A hA
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := d)
  have hn : VectorIntegrationNormalization N hN A hA S hS d M
      (vectorBundleIntegration N hN A hA S hS d M) :=
    (existsUnique_vectorIntegrationGluing N hN A hA S hS d M).2.exists.choose_spec.2
  let := (vectorIntegration_geometry S d M).1
  let := (vectorIntegration_geometry S d M).2.1
  apply derived_isIso_of_cover A (fun i : I ↦ (V i).ι) ?_
  · intro i
    let : TopologicalSpace.NoetherianSpace (V i).toScheme :=
      (V i).ι.isOpenEmbedding.isInducing.noetherianSpace
    let : IsNoetherian (V i).toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    let hi := affineTracePullbackInvertible N (V i).ι hS
    let := (htrace (V i).toScheme hi d).2.2.1
    let := isIso_rightDerivedLowerShriekBaseChangeMap A
      (vectorIntegrationChart_isPullback S d M (V i) (e i).some)
    have hl : IsIso (vectorIntegrationLocalTrace N hN A hA t D S hS d M
        (V i) (e i).some) := by
      dsimp only [vectorIntegrationLocalTrace]
      infer_instance
    have heq := hn t D (V i) (e i).some
    rw [← heq] at hl
    apply (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (V i).ι) _).1
    exact (isIso_comp_right_iff _ (ordinaryFiniteUnitPullback A (V i).ι).hom).1 hl
  · intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ x) : x ∈ ⨆ i, V i)
    exact ⟨i, ⟨x, hi⟩, rfl⟩

private theorem affine_unit_adjunct_isIso (N : ℕ) (_hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (hc : IsIso (affineTraceCounit A N hA t D S hS d))
    {X : DerivedCategoryModule A (affineTraceTower S d)}
    (e : X ≅ (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
    (c : (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj X ⟶ ordinaryFiniteUnit A S) [IsIso c] :
    IsIso ((rightDerivedUpperShriekAdjunction A
      (affineTraceProjection S d)).homEquiv _ _ c) := by
  let b := (affineTraceAdjunction A N hA t D S hS d).ofNatIsoLeft
    (affineLeftIso A S d (HasCompactification.compactification (affineTraceProjection S d)))
  let : IsIso (b.counit.app (ordinaryFiniteUnit A S)) := by
    dsimp only [b, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app]
    let := hc
    change IsIso (_ ≫ affineTraceCounit A N hA t D S hS d)
    infer_instance
  exact adjunct_isIso_of_iso
    (rightDerivedUpperShriekAdjunction A
      (affineTraceProjection S d)) b _ e c

open scoped CategoryTheory.Functor

section UnitMate
attribute [local irreducible] rightDerivedLowerShriek rightDerivedUpperShriek
  rightDerivedUpperShriekAdjunction
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
set_option backward.isDefEq.respectTransparency true

private theorem integration_unit_adjunct_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :
    let : IsAffineHom (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).1
    let : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).2.1
    IsIso ((rightDerivedUpperShriekAdjunction A
      (VectorBundleZeroSection.π S d M)).homEquiv _ _
        (vectorBundleIntegration N hN A hA S hS d M)) := by
  classical
  let := (vectorIntegration_geometry S d M).1
  let := (vectorIntegration_geometry S d M).2.1
  have hi : IsIso (vectorBundleIntegration N hN A hA S hS d M) :=
    integration_isIso N hN A hA S hS d M
  let := (vectorIntegration_geometry S d M).2.2
  obtain ⟨t, D, htD, htrace⟩ := exists_affineSpaceTopTrace N hN A hA
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := d)
  apply derived_isIso_of_cover A
    (fun i : I ↦ vectorIntegrationChart S d M (V i) (e i).some) ?_
  · intro i
    let : TopologicalSpace.NoetherianSpace (V i).toScheme :=
      (V i).ι.isOpenEmbedding.isInducing.noetherianSpace
    let : IsNoetherian (V i).toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    let sq := vectorIntegrationChart_isPullback S d M (V i) (e i).some
    let := isIso_rightDerivedLowerShriekBaseChangeMap A sq
    have hbiso : IsIso (rightDerivedUpperShriekBaseChangeMap A sq) :=
      isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion A sq
    let : (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d M)).IsLeftAdjoint :=
      inferInstance
    let : (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection (V i).toScheme d)).IsLeftAdjoint :=
      inferInstance
    let a : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d M) ⊣
        rightDerivedUpperShriek A (VectorBundleZeroSection.π S d M) :=
      rightDerivedUpperShriekAdjunction A
        (VectorBundleZeroSection.π S d M)
    let b := rightDerivedUpperShriekAdjunction A
      (affineTraceProjection (V i).toScheme d)
    let c := (inv (rightDerivedLowerShriekBaseChangeMap A sq)).app
        (vectorIntegrationCoefficient A N hA S d M) ≫
      (ordinaryFinitePullback A (V i).ι).map
        (vectorBundleIntegration N hN A hA S hS d M)
    have hc : IsIso c := IsIso.comp_isIso'
      (Functor.map_isIso ((CategoryTheory.evaluation _ _).obj _)
        (inv (rightDerivedLowerShriekBaseChangeMap A sq)))
      (Functor.map_isIso (ordinaryFinitePullback A (V i).ι)
        (vectorBundleIntegration N hN A hA S hS d M))
    have hm := affine_unit_adjunct_isIso N hN A hA t D (V i).toScheme
      (affineTracePullbackInvertible N (V i).ι hS) d
      (htrace (V i).toScheme (affineTracePullbackInvertible N (V i).ι hS) d).2.2.1
      (vectorIntegrationChartCoefficient A N hA t S hS d M (V i) (e i).some)
      (c ≫ (ordinaryFiniteUnitPullback A (V i).ι).hom)
    rw [b.homEquiv_naturality_right] at hm
    have hm' : IsIso (b.homEquiv _ _ c) :=
      (isIso_comp_right_iff _ ((rightDerivedUpperShriek A
        (affineTraceProjection (V i).toScheme d)).map
          (ordinaryFiniteUnitPullback A (V i).ι).hom)).1 hm
    have he := mate_naturality a b
      (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap A sq)))
      (vectorIntegrationCoefficient A N hA S d M) (ordinaryFiniteUnit A S)
      (vectorBundleIntegration N hN A hA S hS d M)
    change _ ≫ (rightDerivedUpperShriekBaseChangeMap A sq).app _ = b.homEquiv _ _ c
      at he
    apply (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (vectorIntegrationChart S d M (V i) (e i).some)) _).1
    apply (isIso_comp_right_iff _
      ((rightDerivedUpperShriekBaseChangeMap A sq).app _)).1
    rw [he]
    exact hm'
  · intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ ((VectorBundleZeroSection.π S d M).base x)) :
        (VectorBundleZeroSection.π S d M).base x ∈ ⨆ i, V i)
    obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
      (vectorIntegrationChart_isPullback S d M (V i) (e i).some) x
      ⟨(VectorBundleZeroSection.π S d M).base x, hi⟩ rfl
    exact ⟨i, y, hy⟩

end UnitMate

open CategoryTheory.MonoidalCategory

private theorem three_squares
    {C : Type*} [Category C] {A B C₁ D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ C₁) (c : A ⟶ D) (d : D ⟶ C₁)
    (e : C₁ ⟶ E) (f : D ⟶ F) (g : F ⟶ E)
    (h : E ⟶ G) (i : F ⟶ H) (j : H ⟶ G)
    (ha : a ≫ b = c ≫ d) (hb : d ≫ e = f ≫ g) (hc : g ≫ h = i ≫ j) :
    a ≫ b ≫ e ≫ h = c ≫ f ≫ i ≫ j := by
  rw [reassoc_of% ha, reassoc_of% hb, hc]

private theorem affine_counit_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    IsIso ((affineTraceAdjunction A N hA t D S hS d).counit.app K) := by
  unfold affineTraceAdjunction
  apply affineTraceAdjunctionTower_counit_isIso
  intro e M
  let := affineTraceNoetherian S e
  exact affineTraceLineCounit_isIso A N hN hA t (affineTraceTower S e)
    (affineTraceInvertible N S hS e) (D _ _) M

@[irreducible]
private def affine_right_tensor_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    ((ordinaryFinitePullback A (affineTraceProjection S d)).obj K) ⊗
        (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅
      (affineTraceRight A N hA S d).obj K := by
  let X := affineTraceTower S d
  let P := ordinaryFinitePullback A (affineTraceProjection S d)
  let L := (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat A)) 0).obj
    (Scheme.finiteEtaleTateSheaf A N X hA (d : ℤ))
  let n : ℤ := 2 * (d : ℤ)
  let e := (affineTraceRight_normalForm A N hN hA S hS d).1.some
  let z : (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅ L⟦n⟧ :=
    e.app _ ≪≫ (shiftFunctor _ n).mapIso
      ((tensorRight L).mapIso
        (leftDerivedUpperStarUnitIso (ModuleCat A) (affineTraceProjection S d)) ≪≫ λ_ L)
  exact (tensorLeft (P.obj K)).mapIso z ≪≫
    ((tensorLeft (P.obj K)).commShiftIso n).app L ≪≫ (e.app K).symm

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
set_option backward.isDefEq.respectTransparency true

/-- The actual normalized integration counit has invertible adjunct for every unbounded K.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an, Steps 5(c), 6 and 7;
parent thm-amb-vector-bundle-purity, proof Steps 4--9.
(blueprint: lem-amb-vector-integration-mate)

Proof: compare the ordered affine-space compact-support functor with the ambient one
by induction using compactification independence and composition, starting with the
identity compactification in rank zero. The affine-space trace and frame normalization
first show that the actual vector integration is invertible. Consequently its tensor
with any K, after inverse projection and the unitor, is an invertible counit candidate.

Restrict its Brown adjunct to each frame. The actual exceptional base-change mate
against the open immersion is invertible, and mate naturality identifies this restriction
with the local adjunct of inverse compact-support exchange followed by the pulled-back
counit candidate. The affine right-functor Tate normal form, its value on the unit,
and the chart coefficient isomorphism identify the source with the affine right adjoint
at the pulled-back K. The affine counit is invertible for every K by the coordinate-tower
induction from affineTraceLineCounit_isIso. An invertible map with this source has invertible
Brown adjunct: compare right adjoints and factor off an automorphism of K. Finally detect
invertibility on the jointly surjective frame charts using derived cohomology. This proof
uses the affine adjunction and open base change, without general smooth tensor duality.
-/
theorem vectorIntegrationMate_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d]
    (K : DerivedCategoryModule A S) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).2.1
    ∀ [IsIso (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
        (vectorIntegrationCoefficient A N hA S d M))],
    IsIso ((rightDerivedUpperShriekAdjunction A
      (VectorBundleZeroSection.π S d M)).homEquiv _ K
        (inv (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
          (vectorIntegrationCoefficient A N hA S d M)) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
            (vectorBundleIntegration N hN A hA S hS d M) ≫
              (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S K).hom)) := by
  intro hp
  classical
  let := (vectorIntegration_geometry S d M).1
  let := (vectorIntegration_geometry S d M).2.1
  let := (vectorIntegration_geometry S d M).2.2
  let W := vectorIntegrationCoefficient A N hA S d M
  let f := VectorBundleZeroSection.π S d M
  let c := inv (compactProjectionMapCoeffFirst A f K W) ≫
    ((derivedTensor (ModuleCat A) S).obj K).map
      (vectorBundleIntegration N hN A hA S hS d M) ≫
    (derivedTensorRightUnitor (ModuleCat A) S K).hom
  let ht : IsIso (vectorBundleIntegration N hN A hA S hS d M) :=
    integration_isIso N hN A hA S hS d M
  let : IsIso (compactProjectionMapCoeffFirst A f K W) := hp
  have hm : IsIso (((derivedTensor (ModuleCat A) S).obj K).map
      (vectorBundleIntegration N hN A hA S hS d M)) := Functor.map_isIso _ _
  have hu := (derivedTensorRightUnitor (ModuleCat A) S K).isIso_hom
  let : IsIso c := IsIso.comp_isIso' (inferInstance : IsIso
    (inv (compactProjectionMapCoeffFirst A f K W))) (IsIso.comp_isIso' hm hu)
  obtain ⟨t, D, htD⟩ := exists_ordinaryFiniteP1Adjunction N hN A hA
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := d)
  apply derived_isIso_of_cover A
    (fun i : I ↦ vectorIntegrationChart S d M (V i) (e i).some) ?_
  · intro i
    let : TopologicalSpace.NoetherianSpace (V i).toScheme :=
      (V i).ι.isOpenEmbedding.isInducing.noetherianSpace
    let : IsNoetherian (V i).toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    let T := (V i).toScheme
    let hT := affineTracePullbackInvertible N (V i).ι hS
    let sq := vectorIntegrationChart_isPullback S d M (V i) (e i).some
    let := isIso_rightDerivedLowerShriekBaseChangeMap A sq
    have hbiso : IsIso (rightDerivedUpperShriekBaseChangeMap A sq) :=
      isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion A sq
    let a := rightDerivedUpperShriekAdjunction A f
    let b := (affineTraceAdjunction A N hA t D T hT d).ofNatIsoLeft
      (affineLeftIso A T d
        (HasCompactification.compactification (affineTraceProjection T d)))
    let J := ordinaryFinitePullback A (vectorIntegrationChart S d M (V i) (e i).some)
    let H := ordinaryFinitePullback A (V i).ι
    let P := ordinaryFinitePullback A (affineTraceProjection T d)
    let z : J.obj (((derivedTensor (ModuleCat A)
        (VectorBundleZeroSection.scheme S d M)).obj
          ((ordinaryFinitePullback A f).obj K)).obj W) ≅
        (affineTraceRight A N hA T d).obj (H.obj K) :=
      leftDerivedUpperStarTensorIso (ModuleCat A) _ _ _ ≪≫
        tensorIso
          ((derivedSquareUpperStarIso (ModuleCat A) sq.toCommSq).symm.app K)
          (vectorIntegrationChartCoefficient A N hA t S hS d M (V i) (e i).some) ≪≫
        affine_right_tensor_unit A N hN hA T hT d (H.obj K)
    let c' := (inv (rightDerivedLowerShriekBaseChangeMap A sq)).app
        (((derivedTensor (ModuleCat A) (VectorBundleZeroSection.scheme S d M)).obj
          ((ordinaryFinitePullback A f).obj K)).obj W) ≫ H.map c
    let : IsIso c' := by dsimp only [c']; infer_instance
    have hb : IsIso (b.counit.app (H.obj K)) := by
      dsimp only [b]
      rw [Adjunction.ofNatIsoLeft_counit]
      dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
      let := affine_counit_isIso A N hN hA t D T hT d (H.obj K)
      exact IsIso.comp_isIso' inferInstance inferInstance
    have hm := @adjunct_isIso_of_iso _ _ _ _ _ _ _
      (rightDerivedUpperShriekAdjunction A (affineTraceProjection T d))
      b (H.obj K) _ z c' inferInstance hb
    have he := mate_naturality a
      (rightDerivedUpperShriekAdjunction A (affineTraceProjection T d))
      (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap A sq))) _ K c
    change _ ≫ (rightDerivedUpperShriekBaseChangeMap A sq).app K =
      (rightDerivedUpperShriekAdjunction A (affineTraceProjection T d)).homEquiv
        _ _ c' at he
    apply (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A)
        (vectorIntegrationChart S d M (V i) (e i).some)) _).1
    apply (isIso_comp_right_iff _ ((rightDerivedUpperShriekBaseChangeMap A sq).app K)).1
    rw [he]
    exact hm
  · intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ ((VectorBundleZeroSection.π S d M).base x)) :
        (VectorBundleZeroSection.π S d M).base x ∈ ⨆ i, V i)
    obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
      (vectorIntegrationChart_isPullback S d M (V i) (e i).some) x
      ⟨(VectorBundleZeroSection.π S d M).base x, hi⟩ rfl
    exact ⟨i, y, hy⟩

end AlgebraicGeometry.Etale
