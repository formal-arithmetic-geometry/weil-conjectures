/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import all WeilConjectures.AlgebraicGeometry.EllAdicProperConstructibleCohomology
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization
import WeilConjectures.AlgebraicGeometry.FiniteTorsionProperFiniteness
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksBlueprint
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import WeilConjectures.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralSingle
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralStratum
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Max
import WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralDenominators
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientTelescope
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
import WeilConjectures.CategoryTheory.HomColimitExtension
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.HomColimitTruncation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Topology.StratificationDense
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Data.Int.Interval
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.GradedObject.Bifunctor
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.GradedObject.Trifunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.ContinuousMap.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceHomContinuity
import WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.CondensedLfpHomContinuity
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.LocallyFreeDerivedHomSupplement
import WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import WeilConjectures.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.IntegralLfpHomContinuity
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Grp.Adjunctions
import WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.AlgebraicGeometry.ContinuousLisseStratifiedLattices
import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.LisseLatticeEtaleLocal
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.LisseLatticeClassSheaf
import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import WeilConjectures.AlgebraicGeometry.LatticeSheafBasicSupplement
import WeilConjectures.AlgebraicGeometry.LatticeClassDescent
import WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
import WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
import WeilConjectures.AlgebraicGeometry.LatticePairDescentData
import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoversTop.Over
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
import WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.LargeSetSheafification
import WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
import WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Coset.Defs
import WeilConjectures.CategoryTheory.SiteModuleSheafGluing
import WeilConjectures.NumberTheory.Padics.LatticeStabilizerOpen
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.AlgebraicGeometry.LisseLatticePresentationTransport
import WeilConjectures.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.AlgebraicGeometry.LisseLatticeSliceTransport
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLattices
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLocalFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingSliceFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeFiniteCoproductSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteEtaleLatticeDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionLocalModel
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalModel
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitModel
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitData
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralRegularTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.CondensedUnderivedPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeKernelModel
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeDenominators
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalization
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import WeilConjectures.AlgebraicGeometry.IntegralMatrixKernelLocallyFree
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFiniteSupplement
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.CoefficientHeartTriangulated
import WeilConjectures.SixFunctors.RationalIntegralGenerators
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Ordinary condensed proper finiteness over a Noetherian base

Source: Bhatt--Scholze, Theorem 6.7.1 and Lemma 6.7.2, Proposition 6.8.14 and
Remark 6.8.15; Hemo--Richarz--Scholbach, Theorem 7.7 and Lemma 7.9
(blueprint: lem-fd-noetherian-proper-finiteness).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory upperStarFromPoint Mod.extendScalars

private theorem nppf_integral_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E Z))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Z K) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y
      ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E 1
  let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
    have h := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
    have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
    have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    simpa only [Padic.coefficientExtensionIdeal, pow_one, hg] using hm
  let : Field A := Ideal.Quotient.field _
  let : Finite A := Padic.finite_coefficientExtensionRing l E 1 le_rfl
  let : DiscreteTopology A := DerivedNakayama.quotientDiscrete l E 1
  let : CharP A l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).mpr
    (coefficientExtensionRing_one_natCast_self l E)
  have hsource := IntegralModelsStacks.internal_integral_criterion_forward l E Z K hK
  have hfinite := constantModelBoundedConstructible_derivedPushforward_of_isProper_finite_field
    l A p ((AdicCompletion.derivedReduction l E Z 0).obj K) hsource.2.1
  obtain ⟨hχ, hpush⟩ := internal_integral_direct_image_limits l E p
  let := hχ
  have hcomplete := (hpush K).1 hsource.1
  have hiso := (hpush K).2
  let e : (AdicCompletion.derivedReduction l E Y 0).obj
      ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) ≅
      (moduleObjectDerivedPushforward (DerivedNakayama.quotientRing l E 1) p).obj
        ((AdicCompletion.derivedReduction l E Z 0).obj K) :=
    @asIso _ _ _ _ _ hiso
  let := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.quotientRing l E 1) Y).2.1
  exact IntegralModelsStacks.internal_integral_criterion_reverse l E Y _ hcomplete
    ((constantModelBoundedConstructible _ Y).prop_of_iso e.symm hfinite)

private theorem nppf_transport
    {R S : Profinite.CondensedRing.{u}}
    [IsCommMonObj R.X] [IsCommMonObj S.X] (a : R ≅ S)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (hs : ∀ K, boundedConstructible (condensedRingObj S.X Z) K →
      boundedConstructible (condensedRingObj S.X Y)
        ((moduleObjectDerivedPushforward S.X p).obj K))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj R.X Z)))
    (hK : boundedConstructible (condensedRingObj R.X Z) K) :
    boundedConstructible (condensedRingObj R.X Y)
      ((moduleObjectDerivedPushforward R.X p).obj K) := by
  have ht := NormedCoefficientRealization.transport_property a
  obtain ⟨_, _, _, _, _, _, _, hZ, _⟩ := ht.1 Z
  obtain ⟨_, _, _, _, _, _, _, hY, _⟩ := ht.1 Y
  obtain ⟨γ, _⟩ := ht.2 Z Y p
  apply (hY _).mp
  exact (boundedConstructible _).prop_of_iso (γ.symm.app K) (hs _ ((hZ K).mpr hK))

private theorem nppf_integer_ring
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E Z))
    (hK : boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) Z) K) :
    boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) Y)
      ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) := by
  have hc (T : Scheme.{u}) [IsNoetherian T] :
      boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) T) =
        constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T := by
    funext M
    exact propext (and_congr Iff.rfl
      (forall_congr' fun q ↦ integerModel_comparison l E T _))
  rw [hc Z] at hK
  rw [hc Y]
  exact nppf_integral_model l E p K hK

private theorem nppf_integral
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]
    [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj l E) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E) Y)
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E) p).obj K) := by
  let : FiniteDimensional ℚ_[l] (ULift.{u} E) :=
    (ULift.moduleEquiv (R := ℚ_[l]) (M := E)).symm.finiteDimensional
  obtain ⟨e⟩ := integralCoefficientIso.{u} l E
  exact nppf_transport (e.symm ≪≫ integerLatticeIso l (ULift.{u} E)) p
    (nppf_integer_ring l (ULift.{u} E) p) K hK

private theorem nppf_integral_continuous
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) Z)))
    (hK : boundedConstructible (condensedRingObj (integralCoeff l E) Z) K) :
    boundedConstructible (condensedRingObj (integralCoeff l E) Y)
      ((moduleObjectDerivedPushforward (integralCoeff l E) p).obj K) := by
  let : FiniteDimensional ℚ_[l] (ULift.{u} E) :=
    (ULift.moduleEquiv (R := ℚ_[l]) (M := E)).symm.finiteDimensional
  exact nppf_transport (integerNormedIso l E) p
    (nppf_integer_ring l (ULift.{u} E) p) K hK

private theorem nppf_continuous
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).obj K) := by
  obtain ⟨M, ⟨e⟩⟩ := continuousConstructible_integral_model l E Z ⟨K, hK⟩
  let : ∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralScalarMap l E) T)) :=
    integralScalarExtension_exact l E
  have hb := boundedConstructible_leftDerivedExtendScalars_obj
    (condensedRingObj (integralCoeff l E) Y)
    (condensedRingObj (Profinite.continuousMapRingObj E) Y)
    (coefficientMap (integralScalarMap l E) Y) _
    (nppf_integral_continuous l E p M.obj M.property)
  exact (boundedConstructible _).prop_of_iso
    (@asIso _ _ _ _ _ (integralScalarPushHom_isIso l E p M) ≪≫
      (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).mapIso e) hb

private theorem nppf_algCl
    (l : ℕ) [Fact l.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y)
      ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj l) p).obj K) := by
  let P := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y)
  have heq := (adicConstructibilityPredicateComparison l Y
    (Profinite.padicAlgClRingObj l) .algebraicClosure).2
  obtain ⟨hiso, htri, hret⟩ := (constantModelBoundedConstructible_field_triangulated l Y).2
  let : P.IsClosedUnderIsomorphisms := by dsimp [P]; rw [heq]; exact hiso
  let : P.IsTriangulated := by dsimp [P]; rw [heq]; exact htri
  let : P.IsStableUnderRetracts := by dsimp [P]; rw [heq]; exact hret
  let G := (lowerStar (Profinite.padicAlgClRingObj l) p).rightDerivedFunctor
  let Q := P.inverseImage G
  let : Q.IsStableUnderRetracts := ⟨fun r h ↦ P.prop_of_retract (r.map G) h⟩
  have : Q.IsTriangulated := inferInstance
  have hgen : (WeilConjectures.SixFunctors.qlbarRationalIntegralGenerator l Z) ≤ Q := by
    rintro L ⟨F, M, hM, ⟨e⟩⟩
    let := PadicAlgCl.normedFieldOfAlgebra l F.1
    let : NormedAlgebra ℚ_[l] F.1 := ⟨fun c x ↦ by
      change ‖algebraMap F.1 (PadicAlgCl l) (c • x)‖ ≤
        ‖c‖ * ‖algebraMap F.1 (PadicAlgCl l) x‖
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
        PadicAlgCl.norm_extends]⟩
    let a := padicIntegersRingObjToContinuousMapRingObj l F
    let b := Profinite.padicSubfieldRingObjToPadicAlgCl l F
    let A := Mod.extendScalars (coefficientMap a Z)
    let B := Mod.extendScalars (coefficientMap b Z)
    have : PreservesFiniteLimits A := integralScalarExtension_exact l F.1 Z
    let N := A.leftDerivedFunctor.obj M
    have hN : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj F.1) Z)
        N := boundedConstructible_derivedExtendScalars_obj Z l F ⟨M, hM⟩
    have hPN := nppf_continuous l F.1 p N hN
    obtain ⟨q, hq⟩ := hN.1.1
    let : N.IsGE q := hq
    have hB := boundedConstructible_leftDerivedExtendScalars_obj
      (condensedRingObj (Profinite.continuousMapRingObj F.1) Y)
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)
      (coefficientMap b Y) _ hPN
    let ecomp : Mod.extendScalars (coefficientMap a Z ≫ coefficientMap b Z) ≅ A ⋙ B :=
      Mod.extendScalarsComp _ _
    let : PreservesFiniteLimits (Mod.extendScalars
        (coefficientMap a Z ≫ coefficientMap b Z)) :=
      preservesFiniteLimits_of_natIso ecomp.symm
    let : PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a ≫ b) Z)) :=
      preservesFiniteLimits_of_natIso
        (Mod.extendScalarsIsoOfEq (coefficientMap_comp a b Z)).symm
    let ec : (Mod.extendScalars (coefficientMap (a ≫ b) Z)).leftDerivedFunctor ≅
        A.leftDerivedFunctor ⋙ B.leftDerivedFunctor :=
      Functor.leftDerivedFunctorNatIso _
        (Mod.extendScalarsIsoOfEq (coefficientMap_comp a b Z)) ≪≫
      Functor.leftDerivedFunctorNatIso _ (Mod.extendScalarsComp _ _) ≪≫
      A.leftDerivedFunctorCompIso B
    let eL : L ≅ B.leftDerivedFunctor.obj N := e ≪≫ ec.app M
    exact P.prop_of_iso (@asIso _ _ _ _ _
      (isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE l p F N q) ≪≫
      G.mapIso eL.symm) hB
  exact ((ObjectProperty.triangEnvelope_le_iff
    (WeilConjectures.SixFunctors.qlbarRationalIntegralGenerator l Z)).mpr hgen) K
      ((WeilConjectures.SixFunctors.rationalIntegralGenerators l Z ⟨⊥, inferInstance⟩).2 K hK)

/-- Proper pushforward preserves the ordinary bounded constructible category for the three
condensed coefficient rings in the finite-extension and algebraic-closure family. The derived
pushforward is the total derived functor on module objects, and the conclusion imposes no
common field of definition, finite-dimensional base, or geometric base-change hypothesis.

Proof, following the six steps of this node:
1. For integral coefficients, the adic constructibility predicate comparison identifies the
cohomological predicate with the finite constant local model predicate on both Noetherian
schemes. The forward integral criterion gives derived completeness and bounded
constructibility of the first residue reduction. The integral direct-image-limits theorem,
with j = h and quotient index zero (exponent one), gives completeness of the direct image
and its coefficient-change isomorphism. Finite torsion proper finiteness gives bounded
constructibility of the direct image of the residue reduction. The reverse integral
criterion and predicate comparison give the integral conclusion, for every finite E.
The integer-lattice and normed unit-ball presentations of the integral coefficient (with
ULift) are related to this ring by coefficient-ring isomorphisms (the integral-coefficient
comparisons of the noetherian proper constructible cohomology module), and transport along
such isomorphisms preserves bounded constructibility and commutes with derived direct image
by the normed coefficient realization.
2. The integral-to-rational scalar extension preserves finite limits by continuous integral
scalar exactness. Extension from a finite subfield to the specified algebraic closure does
so by qlbar-flat. The exact scalar-extension theorem therefore gives preservation of
bounded constructibility for both scalar extensions.
3. Properness implies quasi-compactness by finite type and quasi-separatedness by
separatedness. The continuous integral push comparison identifies the pushforward of an
integral generator extended to E with the scalar extension of its integral pushforward.
Steps 1 and 2 make this bounded constructible. Every bounded constructible E-complex
has an integral model by continuousConstructible_integral_model, so this proves the
finite-extension case directly.
4. The coefficient map respects composition. Underived scalar-extension associativity
and the comparison between the left derived functor of a composite of exact functors
and the composite of their left derived functors identify extension along
O_F -> F -> Qlbar with the two successive derived extensions.
5. For a Qlbar integral generator, step 2 makes its intermediate F-extension bounded
constructible, hence lower bounded. The bounded finite-stage Qlbar push comparison for
the proper map h applies. Step 4 identifies the input; steps 3 and 2 make its image
bounded constructible.
6. The algebraic-closure part of rational-integral-generators reduces that case to generators.
The total right derived pushforward is triangulated, additive and preserves retract
diagrams. On Noetherian Y the predicate comparison identifies the target cohomological
category with the finite constant model category, which is thick by the coefficient-heart
triangulated theorem. Thus the class of inputs with bounded constructible image is closed
under isomorphisms, finite sums, shifts, cones and retracts. Steps 3 and 5 put all generators
in that class, proving the algebraic-closure case and completing all three cases.
These are the arguments of Bhatt--Scholze 6.7.1, 6.7.2 and 6.8.14, with
Hemo--Richarz--Scholbach 7.7 and 7.9 for the finite-subextension coefficient.
(blueprint: lem-fd-noetherian-proper-finiteness).
-/
theorem proper_pushforward_mem_boundedConstructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : Λ = Mon.mk (Profinite.padicIntegersRingObj ℓ E) ∨
      Λ = Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (Profinite.padicSubfieldCondensedRing ℓ E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (h : Z ⟶ Y) [IsProper h] :
    ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj Λ.X Z)),
      boundedConstructible (condensedRingObj Λ.X Z) K →
        boundedConstructible (condensedRingObj Λ.X Y)
          ((moduleObjectDerivedPushforward Λ.X h).obj K) := by
  rcases hΛ with rfl | rfl | rfl
  · exact nppf_integral ℓ E h
  · let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    let : NormedAlgebra ℚ_[ℓ] E := ⟨fun c x ↦ by
      change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
        ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
        PadicAlgCl.norm_extends]⟩
    exact nppf_continuous ℓ E h
  · exact nppf_algCl ℓ h

end AlgebraicGeometry.ProEtale.CondensedRing
