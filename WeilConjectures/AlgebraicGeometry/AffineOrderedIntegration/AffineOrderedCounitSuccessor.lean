/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
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
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionLocalComparisonData
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.Affine.AffineDualizingCoefficient
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
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
import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitDescentComparison
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.Compactification.Defs
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineCounitTensorNormalization

/-! # The ordinary ordered coefficient-counit induction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
open CategoryTheory.Limits
open scoped CategoryTheory.Functor

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.ordinaryFinitePullback._proof_1 Etale.ordinaryFinitePullback._proof_2
  Etale.ordinaryFinitePullback._proof_3 Etale.ordinaryFinitePullback._proof_4
  Etale.ordinaryFinitePullback._proof_5 Etale.ordinaryFinitePullback._proof_6
  Etale.ordinaryFinitePullback._proof_7 Etale.ordinaryFinitePullback._proof_8
  Etale.ordinaryFinitePullback._proof_9 Etale.ordinaryFinitePullback._proof_10
  Etale.ordinaryFinitePullback._proof_11 Etale.ordinaryFinitePullback._proof_12
  Etale.ordinaryFinitePullback._proof_13

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory.singleFunctors

attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  Etale.derivedTensorRight Etale.derivedTensorRightFunctor
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
attribute [local irreducible] Etale.affineTraceUnboundedCompactComparison
  Etale.rightDerivedLowerShriekOfCompactificationIso
  Etale.unboundedEtaleLowerShriekCompIso Etale.unboundedEtaleLowerShriekId
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso
  Etale.rightDerivedLowerShriekPlusCompIso Etale.upperStar

private theorem compactComparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    (M : DerivedCategory.Plus
      (Sheaf (affineTraceTower Y d).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ordinaryCompactComparison A Y d M =
      (Etale.affineTraceUnboundedCompactComparison A Y d).app M.obj := by
  apply Iso.ext
  change (Etale.affineTracePlusCompatibility A Y d).inv.app M ≫
    DerivedCategory.Plus.ι.map
      ((Etale.affineTraceCompactSupportComparison A Y d).hom.app M) ≫
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection Y d)).hom.app M =
    (Etale.affineTraceUnboundedCompactComparison A Y d).hom.app
      (DerivedCategory.Plus.ι.obj M)
  apply (cancel_epi ((Etale.affineTracePlusCompatibility A Y d).hom.app M)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (Etale.affineTraceUnboundedCompactComparison_restriction A Y d M).symm

private theorem unboundedComparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ) :
    Etale.affineTraceUnboundedCompactComparison A Y d =
      Etale.affineDualizingTowerComparison A Y d := by
  delta Etale.affineTraceUnboundedCompactComparison Etale.affineDualizingTowerComparison
  rfl

private theorem linearComparison_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    Etale.affineLinearCompactComparison N hN A hA Y hY d =
      (Etale.affineDualizingTowerComparison A Y d).app
        ((Etale.affineTraceRight A N hA Y d).obj (Etale.ordinaryFiniteUnit A Y)) := by
  change ordinaryCompactComparison A Y d _ = _
  rw [compactComparison_eq, unboundedComparison_eq]

private theorem normalization_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (TC : C ⥤ C) (TD : D ⥤ D)
    (pf : ∀ W : C, TD.obj (F.obj W) ⟶ F.obj (TC.obj W))
    (hp : ∀ {W V : C} (c : W ⟶ V), TD.map (F.map c) ≫ pf V =
      pf W ≫ F.map (TC.map c))
    {W V J : C} {K U : D} (c : W ≅ V) (eW : J ≅ TC.obj W)
    (eV : J ≅ TC.obj V) (he : eV = eW ≪≫ TC.mapIso c)
    (z : F.obj J ⟶ K) (tW : F.obj W ⟶ U) (tV : F.obj V ⟶ U)
    (ht : tV = F.map c.inv ≫ tW) (un : TD.obj U ⟶ K)
    (hn : pf V ≫ F.map eV.inv ≫ z = TD.map tV ≫ un) :
    pf W ≫ F.map eW.inv ≫ z = TD.map tW ≫ un := by
  have h := congrArg (TD.map (F.map c.hom) ≫ ·) hn
  simp only [he, ht, Iso.trans_inv, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc] at h
  rw [reassoc_of% (hp c.hom)] at h
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id] at h
  simpa only [TC.map_id, F.map_id, Category.id_comp] using h

private theorem trace_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {L W V : C} {K : D}
    (b : L ≅ W) (a : L ≅ V) (z : F.obj L ⟶ K) :
    F.map a.inv ≫ z = F.map (b.symm ≪≫ a).inv ≫ F.map b.inv ≫ z := by
  calc
    _ = F.map a.inv ≫ (F.map b.hom ≫ F.map b.inv) ≫ z := by
      rw [← F.map_comp, b.hom_inv_id, F.map_id, Category.id_comp]
    _ = _ := by
      simp only [Iso.trans_inv, Iso.symm_inv, F.map_comp, Category.assoc]

private theorem projection_forward {C : Type*} [Category C]
    {X Y Z : C} (q : X ≅ Y) {p : X ⟶ Y} {z z' : Y ⟶ Z} {t : X ⟶ Z}
    (hp : q.hom = p) (hz : z' = z) (h : z' = q.inv ≫ t) : p ≫ z = t := by
  rw [← hp, ← hz, h, Iso.hom_inv_id_assoc]

private theorem projection_paste {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a b c d e f : C}
    {x y z v : D} (l : x ⟶ y) (s : y ⟶ z) (s' : x ⟶ v)
    (p : z ⟶ F.obj a) (p' : v ⟶ F.obj b)
    (u : a ⟶ c) (u' : b ⟶ d) (t : c ⟶ e) (t' : d ⟶ f)
    (m : v ⟶ z) (r : b ⟶ a) (q : d ⟶ c) (n : f ⟶ e)
    (hs : l ≫ s = s' ≫ m) (hp : m ≫ p = p' ≫ F.map r)
    (hu : r ≫ u = u' ≫ q) (ht : q ≫ t = t' ≫ n) :
    l ≫ s ≫ p ≫ F.map u ≫ F.map t =
      (s' ≫ p' ≫ F.map u' ≫ F.map t') ≫ F.map n := by
  rw [reassoc_of% hs, reassoc_of% hp]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, hu, F.map_comp, Category.assoc,
    ← F.map_comp, ht, F.map_comp]

private theorem projection_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {W W' : Etale.DerivedCategoryModule A X} (c : W ⟶ W')
    (K : Etale.DerivedCategoryModule A Y) :
    ((Etale.ordinaryFiniteTensor A Y).obj K).map
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map c) ≫
      Etale.compactSupportProjectionMap A f W' K =
    Etale.compactSupportProjectionMap A f W K ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((Etale.ordinaryFiniteTensor A X).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).map c) := by
  let F := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let Q := Etale.ordinaryFinitePullback A f
  let U := (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  let T := Etale.derivedTensor (ModuleCat.{u + 1} A) X
  have hs := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).naturality
    (F.map c)
  have hp := NatTrans.naturality_app
    (Etale.projectionMap (ModuleCat.{u + 1} A) f) K c
  have he := ((T.map c).naturality
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)).symm
  have ht := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
    (U.obj K)).naturality c
  change ((Etale.ordinaryFiniteTensor A Y).obj K).map (F.map c) ≫
      (_ ≫ ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W').app K ≫
        F.map ((T.obj W').map _) ≫ F.map _) =
    (_ ≫ ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W).app K ≫
        F.map ((T.obj W).map _) ≫ F.map _) ≫ F.map _
  dsimp only [Functor.flip_obj_map, Functor.flip_map_app] at hs ht
  change ((T.map c).app (Q.obj K)) ≫ (T.obj W').map _ =
    (T.obj W).map _ ≫ (T.map c).app (U.obj K) at he
  change ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map (F.map c)).app K ≫
      ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W').app K =
    ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W).app K ≫
      F.map ((T.map c).app (Q.obj K)) at hp
  exact projection_paste F _ _ _ _ _ _ _ _ _ _ _ _ _ hs hp he ht

private theorem bifunctor_iso_transport {C D E : Type*}
    [Category C] [Category D] [Category E] (T : C ⥤ D ⥤ E)
    {K K' : D} {L M N : C} (u : K ≅ K') (v : L ≅ M) (a : L ≅ N) :
    (T.obj L).mapIso u ≪≫ (T.mapIso a).app K' =
      (T.mapIso v).app K ≪≫ (T.obj M).mapIso u ≪≫
        (T.mapIso (v.symm ≪≫ a)).app K' := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Functor.map_comp, NatTrans.comp_app]
  rw [← reassoc_of% ((T.map v.hom).naturality u.hom)]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, T.map_id, NatTrans.id_app, Category.id_comp]

private theorem tensorRightMapIso_refl (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (K : Etale.DerivedCategoryModule A X)
    {L M : Etale.DerivedCategoryModule A X} (c : L ≅ M) :
    Etale.ordinaryFiniteTensorRightMapIso A X (Iso.refl K) c =
      ((Etale.ordinaryFiniteTensor A X).obj K).mapIso c := by
  apply Iso.ext
  simp only [Etale.ordinaryFiniteTensorRightMapIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.refl_hom,
    (Etale.derivedTensorRight (ModuleCat.{u + 1} A) X L).map_id, Category.id_comp]
  rfl

private theorem natIso_refl_app {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (K : C) : (Iso.refl F).app K = Iso.refl (F.obj K) := rfl

private theorem reassociation_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) (d : ℕ) :
    Etale.OrdinaryAffineCounitTensorNormalization.reassociation
      (AffineLinePurity.Ring P) (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (transport P) Y (exponentUnit P Y aY) d K =
    ordinarySourceIso P Y aY K d ≪≫
      Etale.ordinaryFiniteTensorRightMapIso (AffineLinePurity.Ring P) (affineTraceTower Y d)
        (Iso.refl _) ((coefficientComparison P Y aY d).symm ≪≫
          Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P) (exponent P)
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
            (transport P) Y (exponentUnit P Y aY) d) := by
  unfold Etale.OrdinaryAffineCounitTensorNormalization.reassociation
  rw [normalized_source_descent]
  unfold ordinarySourceIso ordinarySourceIsoFixed coefficientComparison
  simp only [Iso.trans_assoc]
  congr 2
  unfold Etale.ordinaryFiniteTensorRightMapIso
  simpa only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl,
    Functor.mapIso_trans, NatIso.trans_app, natIso_refl_app, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc, Etale.derivedTensorRight,
    Etale.derivedTensorRightFunctor, Etale.ordinaryFinitePullback] using
    bifunctor_iso_transport
      (Etale.derivedTensorRightFunctor
        (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) (affineTraceTower Y d))
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
        (affineTraceProjection Y d)).app K)
      (Etale.vectorIntegrationBaseCoefficientPullback (AffineLinePurity.Ring P)
        (exponent P) (annihilates P) (transport P) (affineTraceProjection Y d)
        (exponentUnit P Y aY) d)
      ((Etale.affineLinearCoefficientDescent (AffineLinePurity.Ring P)
        (exponent P) (annihilates P) (transport P) Y (exponentUnit P Y aY) d).symm ≪≫
        Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P) (exponent P)
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
          (transport P) Y (exponentUnit P Y aY) d)

private theorem ordinaryCounit_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) (d : ℕ) :
    ordinaryCounit P Y aY K hK d =
      (Etale.affineDualizingTowerComparison (AffineLinePurity.Ring P) Y d).inv.app _ ≫
        (orderedAdjunction P Y aY d).counit.app K := by
  unfold ordinaryCounit
  rw [compactComparison_eq (AffineLinePurity.Ring P) Y d
    ⟨_, ordinarySource_plus P Y aY K hK d⟩, unboundedComparison_eq]
  rfl

private theorem normalizedCounit_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) (d : ℕ) :
    Etale.OrdinaryAffineCounitTensorNormalization.counit
      (AffineLinePurity.Ring P) (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) d K =
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (affineTraceProjection Y d)).map
        (Etale.OrdinaryAffineCounitTensorNormalization.reassociation
          (AffineLinePurity.Ring P) (exponent P)
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
          (transport P) Y (exponentUnit P Y aY) d K).inv ≫
      ordinaryCounit P Y aY K hK d := by
  rw [ordinaryCounit_eq]
  rfl

private theorem normalizedTrace_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    Etale.OrdinaryAffineCounitTensorNormalization.trace
      (AffineLinePurity.Ring P) (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) d =
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (affineTraceProjection Y d)).map
        ((coefficientComparison P Y aY d).symm ≪≫
          Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P) (exponent P)
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
            (transport P) Y (exponentUnit P Y aY) d).inv ≫
      ordinaryTraceRaw P Y aY d := by
  unfold Etale.OrdinaryAffineCounitTensorNormalization.trace ordinaryTraceRaw
  rw [linearComparison_eq]
  exact trace_transport _ (coefficientComparison P Y aY d)
    (Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P) (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (transport P) Y (exponentUnit P Y aY) d) _

/-- One-coordinate propagation of the ordinary coefficient-counit formula.
The hypothesis is the preceding rank formula for every finite-Tor coefficient input;
no assertion about the zero-coordinate normalization is included.
Source: current blueprint, projection-purity agreement proof, final paragraph;
expanded ordered-transpose argument, Steps 5 and 6.
(blueprint: lem-pur-affine-ordered-counit-successor).

Proof: apply the existing ordinaryAffineCounit_tensor_normalization in rank d+1.
Its source descent has the same zero clause as ordinarySourceDescent, by the tensor
trace formula at the identity. Naturality of inverse-image composition identifies
the successor clauses; uniqueness of the specified recursion identifies the families.
The bounded compact-support comparison is the restriction of the unbounded one, which
has the same recursion as affineDualizingTowerComparison. Thus their counit maps agree.
Change the coefficient from the ordered product to the shifted Tate object by
coefficientComparison inverse followed by towerTateIso. Tensor bifunctor naturality
identifies the source isomorphisms; cancellation identifies their traces. Naturality
of the actual compact-support projection transports the existing normalization back
to OrdinaryCounitEquation. This argument applies in every rank and does not need the
preceding-rank hypothesis. -/
theorem ordinary_counit_successor (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ)
    (ih : ∀ (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K),
    OrdinaryCounitEquation (AffineLinePurity.Ring P) (affineTraceProjection Y d)
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
        (affineTraceTower Y d) d) K _ (ordinarySourceIso P Y aY K d)
      (ordinaryCounit P Y aY K hK d) (ordinaryTraceRaw P Y aY d)) :
    ∀ (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K),
    OrdinaryCounitEquation (AffineLinePurity.Ring P) (affineTraceProjection Y (d + 1))
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
        (affineTraceTower Y (d + 1)) (d + 1)) K _ (ordinarySourceIso P Y aY K (d + 1))
      (ordinaryCounit P Y aY K hK (d + 1)) (ordinaryTraceRaw P Y aY (d + 1)) := by
  -- The existing normalization supplies the coefficient formula in every rank.
  clear ih
  intro K hK
  let n := d + 1
  let A := AffineLinePurity.Ring P
  let hN : 0 < exponent P := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  let F := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection Y n)
  let W := Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P)
    (affineTraceTower Y n) n
  let V := Etale.SectionLocalDualizingComparisons.tateObject A (exponent P)
    (annihilates P) (affineTraceTower Y n) n
  let TC := (Etale.ordinaryFiniteTensor A (affineTraceTower Y n)).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A)
      (affineTraceProjection Y n)).mapDerivedCategory.obj K)
  let TD := (Etale.ordinaryFiniteTensor A Y).obj K
  let c : W ≅ V := (coefficientComparison P Y aY n).symm ≪≫
    Etale.CoordinateCounitArrows.towerTateIso A (exponent P) hN (annihilates P)
      (transport P) Y (exponentUnit P Y aY) n
  let eV := Etale.OrdinaryAffineCounitTensorNormalization.reassociation
    A (exponent P) hN (annihilates P) (transport P) Y (exponentUnit P Y aY) n K
  have he : eV = ordinarySourceIso P Y aY K n ≪≫ TC.mapIso c := by
    simpa only [tensorRightMapIso_refl] using reassociation_eq P Y aY K n
  have hz : Etale.OrdinaryAffineCounitTensorNormalization.counit
      A (exponent P) hN (annihilates P) (transport P) (projectiveDatum P)
      Y (exponentUnit P Y aY) n K =
      F.map eV.inv ≫ ordinaryCounit P Y aY K hK n := by
    exact normalizedCounit_eq P Y aY K hK n
  have ht : Etale.OrdinaryAffineCounitTensorNormalization.trace
      A (exponent P) hN (annihilates P) (transport P) (projectiveDatum P)
      Y (exponentUnit P Y aY) n = F.map c.inv ≫ ordinaryTraceRaw P Y aY n := by
    exact normalizedTrace_eq P Y aY n
  obtain ⟨q, hq, hn⟩ := Etale.ordinaryAffineCounit_tensor_normalization
    (exponent P) hN A (annihilates P) (transport P) (projectiveDatum P)
    Y (exponentUnit P Y aY) n K
  have hn' : Etale.compactSupportProjectionMap A (affineTraceProjection Y n) V K ≫
      F.map eV.inv ≫ ordinaryCounit P Y aY K hK n =
      TD.map (Etale.OrdinaryAffineCounitTensorNormalization.trace
        A (exponent P) hN (annihilates P) (transport P) (projectiveDatum P)
        Y (exponentUnit P Y aY) n) ≫ (Etale.derivedTensorSingleUnitIso K).hom := by
    exact projection_forward q hq hz hn
  unfold OrdinaryCounitEquation
  rw [Etale.ordinaryFiniteTensorTrace_app]
  exact normalization_transport F TC TD
    (fun M ↦ Etale.compactSupportProjectionMap A (affineTraceProjection Y n) M K)
    (fun f ↦ projection_naturality A (affineTraceProjection Y n) f K)
    c (ordinarySourceIso P Y aY K n) eV he (ordinaryCounit P Y aY K hK n)
    (ordinaryTraceRaw P Y aY n) _ ht (Etale.derivedTensorSingleUnitIso K).hom hn'

attribute [local irreducible] ordinaryCompactComparison

attribute [local irreducible] ordinaryCounit ordinarySourceIso

attribute [local irreducible] Etale.OrdinaryAffineCounitTensorNormalization.reassociation
  Etale.OrdinaryAffineCounitTensorNormalization.counit
  Etale.OrdinaryAffineCounitTensorNormalization.trace

set_option linter.unusedVariables false in
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
