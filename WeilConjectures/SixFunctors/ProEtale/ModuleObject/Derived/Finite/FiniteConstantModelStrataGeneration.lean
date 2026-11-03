/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import all Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Types.Filtered
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.ConstructibleSheaf.FreeLifting
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import all Mathlib.Topology.MetricSpace.Ultra.Basic
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Analysis.Normed.Group.Ultra
import all Mathlib.Data.Finset.Max
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all Mathlib.Algebra.Field.ULift
import all WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import all WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all Mathlib.Data.Fin.Tuple.Basic
import all WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralDenominators
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientTelescope
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
import all WeilConjectures.CategoryTheory.HomColimitExtension
import all Mathlib.CategoryTheory.Triangulated.Pretriangulated
import all Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.Algebra.Category.Grp.Colimits
import all Mathlib.CategoryTheory.Filtered.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.CategoryTheory.Triangulated.Yoneda
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import all Mathlib.CategoryTheory.Category.ULift
import all WeilConjectures.CategoryTheory.HomColimitTruncation
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all Mathlib.Algebra.Homology.QuasiIso
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import all WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import all WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.Topology.StratificationDense
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import all WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import all Mathlib.Algebra.Homology.CochainComplexPlus
import all Mathlib.Data.Int.Interval
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import all WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import all Mathlib.Algebra.Homology.TotalComplex
import all Mathlib.CategoryTheory.Abelian.Basic
import all WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import all WeilConjectures.CategoryTheory.Triangulated.Recollement
import all Mathlib.Algebra.Category.Grp.Zero
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import all Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.AlgebraicGeometry.Pullbacks
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Adjunction.Triple
import all Mathlib.CategoryTheory.EffectiveEpi.Comp
import all Mathlib.CategoryTheory.Extensive
import all Mathlib.CategoryTheory.GradedObject.Bifunctor
import all Mathlib.CategoryTheory.GradedObject.Monoidal
import all Mathlib.CategoryTheory.GradedObject.Trifunctor
import all Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import all Mathlib.CategoryTheory.Limits.Preserves.Filtered
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import all Mathlib.CategoryTheory.Monad.Adjunction
import all Mathlib.CategoryTheory.Monoidal.Action.Basic
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.CommMon_
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Monoidal.Mon
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.CategoryTheory.Sites.Coherent.Basic
import all Mathlib.CategoryTheory.Sites.Coherent.Comparison
import all Mathlib.CategoryTheory.Sites.ConcreteSheafification
import all Mathlib.CategoryTheory.Sites.Grothendieck
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.Combinatorics.Quiver.ReflQuiver
import all Mathlib.Data.Int.ConditionallyCompleteOrder
import all Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import all Mathlib.Geometry.RingedSpace.PresheafedSpace
import all Mathlib.Geometry.RingedSpace.SheafedSpace
import all Mathlib.Topology.Category.CompHausLike.Basic
import all Mathlib.Topology.Category.CompHausLike.Limits
import all Mathlib.Topology.Category.Profinite.Basic
import all Mathlib.Topology.Category.Profinite.Limits
import all Mathlib.Topology.Category.TopCat.Basic
import all Mathlib.Topology.ContinuousMap.Defs
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceHomContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.AlgebraicGeometry.CondensedLfpHomContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import all WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import all WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
import all WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import all WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.IntegralLfpHomContinuity
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import all WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import all WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import all Mathlib.CategoryTheory.Sites.Adjunction
import all Mathlib.Algebra.Category.Grp.Adjunctions
import all WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all WeilConjectures.ConstructibleSheaf.Devissage
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteModelStratumFiltration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Generation using a fixed ordered reduced stratification -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp lowerStarComp
  openImmersionLowerShriek

/-- Localization on the successive closed tails places a module in the finite
extension closure of its restrictions to a fixed stratification.
Source: Stacks Tags 09AH and 09Y5; blueprint det-lem-int-ext-formula, step 6.
(blueprint: lem-finite-constant-model-fixed-strata-generation).

Proof: the closed tails have images complementary to the open prefixes. Reducedness
factors each next tail through the preceding one, and this factor is a closed
immersion. Its complement is the specified open stratum. Apply the open/closed
short exact sequence to the restriction of the module to that tail. Exact closed
pushforward gives a distinguished triangle on X. Reverse induction starts with
the empty last tail and adds the stratum extensions. The first tail has full image;
the closed adjunction unit identifies its restriction and pushforward with the
original module. This also handles the empty stratification and zero module. -/
theorem finiteConstantModel_fixedStrata_generation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (R : X.FiniteLocallyClosedStratification)
    (Z : Fin (R.n + 1) → Scheme.{u}) (i : ∀ k, Z k ⟶ X)
    (v : ∀ a : Fin R.n, R.domain a ⟶ Z a.castSucc)
    (hi : ∀ k, IsClosedImmersion (i k) ∧ IsReduced (Z k))
    (hv : ∀ a, IsOpenImmersion (v a) ∧ v a ≫ i a.castSucc = R.immersion a)
    (hr : ∀ k, Set.range (i k) =
      (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a)ᶜ)
    (Q : ObjectProperty (DerivedCategory (supportModules Λ X)))
    [Q.IsClosedUnderIsomorphisms]
    (hzero : ∀ M, IsZero M → Q M)
    (hext : ∀ T ∈ distTriang (DerivedCategory (supportModules Λ X)),
      Q T.obj₁ → Q T.obj₃ → Q T.obj₂)
    (M : supportModules Λ X)
    (hpieces : ∀ a : Fin R.n, letI := (hv a).1;
      Q ((DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar Λ (i a.castSucc)).obj
          ((openImmersionLowerShriek Λ (v a)).obj
            ((upperStar Λ (R.immersion a)).obj M))))) :
    Q ((DerivedCategory.singleFunctor _ 0).obj M) := by
  classical
  have hci (k : Fin (R.n + 1)) : IsClosedImmersion (i k) := (hi k).1
  have hZi (k : Fin (R.n + 1)) : IsReduced (Z k) := (hi k).2
  have hvi (a : Fin R.n) : IsOpenImmersion (v a) := (hv a).1
  have hnoeth (k : Fin (R.n + 1)) : TopologicalSpace.NoetherianSpace (Z k) :=
    (i k).isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let N (k : Fin (R.n + 1)) := (upperStar Λ (i k)).obj M
  let H (k : Fin (R.n + 1)) :=
    (DerivedCategory.singleFunctor _ 0).obj ((lowerStar Λ (i k)).obj (N k))
  have hH (k : Fin (R.n + 1)) : Q (H k) := by
    induction k using Fin.reverseInduction with
    | last =>
      have he : IsEmpty (Z (Fin.last R.n)) := by
        refine ⟨fun z ↦ ?_⟩
        have hz : i (Fin.last R.n) z ∈ Set.range (i (Fin.last R.n)) :=
          Set.mem_range_self z
        rw [hr] at hz
        apply hz
        have hc := R.iUnion_stratum_eq_univ
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hc.symm ▸ Set.mem_univ (i _ z))
        exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨a.isLt, ha⟩⟩
      exact hzero _ ((DerivedCategory.singleFunctor _ 0).map_isZero
        ((lowerStar Λ (i _)).map_isZero (module_zero_of_empty _ (N _))))
    | cast a ih =>
      have hs : Set.range (i a.succ) ⊆ Set.range (i a.castSucc) := by
        rw [hr, hr]
        intro x hx hx'
        apply hx
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx'
        obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
        exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨by
          simpa only [Fin.val_castSucc, Fin.val_succ] using Nat.lt_succ_of_lt hb, hxb⟩⟩
      obtain ⟨t, ht⟩ :=
        (reduced_source_factors_through_closed_subscheme (i a.castSucc) (i a.succ)).1.mpr hs
      have : IsClosedImmersion (t ≫ i a.castSucc) := by rw [ht]; infer_instance
      have : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t (i a.castSucc)
      have hcomp : Set.range (v a) = (Set.range t)ᶜ := by
        ext z
        constructor
        · rintro ⟨s, rfl⟩ ⟨z', hz'⟩
          have hz : (R.immersion a) s ∈ Set.range (i a.succ) := by
            refine ⟨z', ?_⟩
            rw [← ht, Scheme.Hom.comp_apply, hz', ← Scheme.Hom.comp_apply, (hv a).2]
          rw [hr] at hz
          exact hz (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
            ⟨by simp, R.range_immersion a ▸ Set.mem_range_self s⟩⟩)
        · intro hz
          have hnot : i a.castSucc z ∉ Set.range (i a.succ) := by
            rintro ⟨z', hz'⟩
            apply hz
            refine ⟨z', (i a.castSucc).isClosedEmbedding.injective ?_⟩
            simpa only [← Scheme.Hom.comp_apply, ht] using hz'
          have hmem : i a.castSucc z ∈ R.stratum a := by
            have hz0 : i a.castSucc z ∈ Set.range (i a.castSucc) := Set.mem_range_self z
            rw [hr] at hz0
            rw [hr] at hnot
            have hx := Classical.not_not.mp hnot
            obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
            obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
            have hba : b = a := by
              apply Fin.ext
              have hb' : b.val < a.val + 1 := by simpa only [Fin.val_succ] using hb
              by_contra hne
              exact hz0 (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr
                ⟨by simpa only [Fin.val_castSucc] using (show b.val < a.val by omega), hxb⟩⟩)
            simpa only [hba] using hxb
          obtain ⟨s, hs⟩ := (R.range_immersion a).symm ▸ hmem
          refine ⟨s, (i a.castSucc).isClosedEmbedding.injective ?_⟩
          simpa only [← Scheme.Hom.comp_apply, (hv a).2] using hs
      have : IsImmersion (R.immersion a) := R.isImmersion a
      have : TopologicalSpace.NoetherianSpace (R.domain a) :=
        (R.immersion a).isEmbedding.isInducing.noetherianSpace
      have : QuasiCompact (v a) :=
        ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
      obtain ⟨e⟩ := natural_open_closed_quotient Λ (v a) t hcomp
      let ε := (openImmersionLowerShriekUpperStarAdjunction Λ (v a)).counit.app (N a.castSucc)
      have : Mono ε := mono_condensed_counit Λ (v a) _
      let SC := ShortComplex.mk ε (cokernel.π ε) (cokernel.condition ε)
      have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel ε }
      have hcok : cokernel ε ≅ (lowerStar Λ t).obj ((upperStar Λ t).obj (N a.castSucc)) :=
        (PreservesCokernel.iso ((evaluation _ _).obj (N a.castSucc))
          (openImmersionLowerShriekUpperStarAdjunction Λ (v a)).counit).symm ≪≫
            e.app (N a.castSucc)
      let G := lowerStar Λ (i a.castSucc)
      let O : X.Opens := ⟨(Set.range (i a.castSucc))ᶜ,
        (i a.castSucc).isClosedEmbedding.isClosed_range.isOpen_compl⟩
      have : TopologicalSpace.NoetherianSpace O.toScheme :=
        O.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
      have : QuasiCompact O.ι := noetherian_qc O.ι
      have := closedSupport_lowerStarExact Λ (i a.castSucc) O.ι (by
        rw [Scheme.Opens.range_ι]
        change Set.range (i a.castSucc) = (Set.range (i a.castSucc))ᶜᶜ
        exact (compl_compl _).symm)
      have hmap := (hSC.map_of_exact G)
      have e₁ := (DerivedCategory.singleFunctor _ 0).mapIso
        (G.mapIso ((openImmersionLowerShriek Λ (v a)).mapIso
          ((upperStarComp Λ (v a) (i a.castSucc)).symm.app M ≪≫
            (upperStarCongr Λ (hv a).2).app M)))
      have e₃ := (DerivedCategory.singleFunctor _ 0).mapIso
        (G.mapIso hcok ≪≫
          (G.mapIso ((lowerStar Λ t).mapIso
            ((upperStarComp Λ t (i a.castSucc)).symm.app M ≪≫
              (upperStarCongr Λ ht).app M))) ≪≫
          (lowerStarComp Λ t (i a.castSucc)).app ((upperStar Λ (i a.succ)).obj M) ≪≫
          (lowerStarCongr Λ ht).app ((upperStar Λ (i a.succ)).obj M))
      exact hext hmap.singleTriangle hmap.singleTriangle_distinguished
        (Q.prop_of_iso e₁.symm (hpieces a)) (Q.prop_of_iso e₃.symm ih)
  have : QuasiCompact (⊥ : X.Opens).ι := by
    have : TopologicalSpace.NoetherianSpace (⊥ : X.Opens).toScheme :=
      (⊥ : X.Opens).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    exact ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hfirst : IsIso ((upperStarLowerStarAdjunction Λ (i 0)).unit.app M) := by
    apply supported_unit Λ (i 0) (⊥ : X.Opens).ι
    · rw [Scheme.Opens.range_ι, hr]
      simp
    · have : IsEmpty (⊥ : X.Opens).toScheme :=
        ⟨fun x ↦ (show False from x.property)⟩
      exact module_zero_of_empty _ _
  exact Q.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
    (asIso ((upperStarLowerStarAdjunction Λ (i 0)).unit.app M))).symm (hH 0)

end AlgebraicGeometry.ProEtale.CondensedRing
