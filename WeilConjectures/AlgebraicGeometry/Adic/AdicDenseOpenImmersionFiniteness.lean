/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperConstructibleCohomology
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import all WeilConjectures.AlgebraicGeometry.IntegralOpenDirectImage.IntegralOpenDirectImage
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Open.OpenDirectImageFiniteCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
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
import WeilConjectures.CategoryTheory.RingObjects.Ab
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
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
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
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
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
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
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
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
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
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
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
import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
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
import WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Grp.Adjunctions
import WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.AlgebraicGeometry.ContinuousLisseStratifiedLattices
import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.LisseLatticeEtaleLocal
import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
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
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
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
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.CompactOpen
import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLocalFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingSliceFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeFiniteCoproductSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteEtaleLatticeDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionLocalModel
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ContinuousLatticeIntersectionSupplement
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralLocalizationSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralRegularTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.CategoryTheory.ProperBaseChange.CondensedUnderivedPushforwardContinuitySupplement
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
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.AlgebraicGeometry.QlbarDirectImageComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstructibleHeart
import WeilConjectures.AlgebraicGeometry.Native.NativeAdicConstructibilityEncoding

/-!
# Adic finiteness for a dense open immersion with affine source

This is the open-immersion input for the affine compactification reduction of
`sk-prop-sf-finiteness`. It concerns ordinary direct image, including its boundary stalks.
-/

@[expose] public section

universe u

set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local irreducible] Sheaf.monObj_sheafCompose_obj Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.rightAdjoint Mod.extendScalars upperStarFromPoint ProEtale.CondensedRing.upperStar
  derivedPushHom derivedComapLowerStarIso Mod.derivedExtendMapDerivedCategoryAdjunction
  ProEtale.FiniteDiscreteOrdinary.Encoding.fixedDerived
  ProEtale.FiniteDiscreteOrdinary.Encoding.ordinaryDerived

private theorem open_finite_field_tor
    (F : Type (u + 1)) [Field F] (X : Scheme.{u})
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X K) :
    Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X K := by
  obtain ⟨hb, _⟩ := hK
  refine _root_.DerivedCategory.prop_of_bounded
    (Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X) ⊤ ?_ K hb
    (fun _ ↦ trivial)
  intro G _
  refine ⟨0, 0, Etale.torAmplitudeIn_singleFunctor_zero_of_flat _ G ?_⟩
  exact (Etale.flat_iff_forall_flat_sheafFiber_obj G).2 fun _ ↦
    (ModuleCat.flat_iff_flat _).2 inferInstance
private theorem open_finiteFixed_bounded
    (l : ℕ) [Fact l.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ l)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (A : Type u) [Field A] [Finite A]
    (hA : (l : A) = 0)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hK : ProEtale.FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Z K) :
    ProEtale.FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Y
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).rightDerivedFunctor.obj K) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).rightDerivedFunctor.obj
          K) := by
  let B := ULift.{u + 1} A
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := ProEtale.fixedDerivedOrigin Z B K
    (fun q ↦ (ProEtale.ordinary_constructible_iff A Z _).mp (hK.2 q)) a b (by
      intro q hq
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ a q hq (hX := ha)
      · exact DerivedCategory.isZero_of_isLE _ b q hq (hX := hb))
  have hk : IsUnit (l : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (p := ringChar k)
      (Fact.out : l.Prime) (Fact.out : ringChar k ≠ l)).isUnit
  have hcoeff : Etale.IsSmoothBaseChangeCoefficients l B (Spec (.of k)) :=
    ⟨(Fact.out : l.Prime).pos, inferInstance, by exact congrArg ULift.up hA,
      by simpa only [map_natCast] using hk.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  have hFJ := Etale.isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion
    k B l hcoeff t p J hJ
  obtain ⟨aJ, bJ, _, hvJ⟩ := hJ.2
  let Jp : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat B)) :=
    ⟨J, ⟨aJ, (DerivedCategory.isGE_iff J aJ).2
      (fun q hq ↦ hvJ q (Or.inl hq))⟩⟩
  let νY := ProEtale.comparisonUpperStar (ModuleCat B) Y
  let F := Etale.lowerStar (ModuleCat B) p
  let G := ProEtale.lowerStar (ModuleCat B) p
  let e : νY.mapDerivedCategory.obj (F.rightDerivedFunctor.obj J) ≅
      G.rightDerivedFunctor.obj K :=
    ((ProEtale.rightDerivedLowerStarComparisonIso (ModuleCat B) p).app Jp).symm ≪≫
      G.rightDerivedFunctor.mapIso eJ
  obtain ⟨c, d, _, hv⟩ := hFJ.2
  have hge : (F.rightDerivedFunctor.obj J).IsGE c :=
    (DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hv q (Or.inl hq)
  have hle : (F.rightDerivedFunctor.obj J).IsLE d :=
    (DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hv q (Or.inr hq)
  have := νY.isGE_mapDerivedCategory_obj (F.rightDerivedFunctor.obj J) c
  have := νY.isLE_mapDerivedCategory_obj (F.rightDerivedFunctor.obj J) d
  constructor
  · refine ⟨⟨⟨c, DerivedCategory.TStructure.t.isGE_of_iso e c⟩,
      ⟨d, DerivedCategory.TStructure.t.isLE_of_iso e d⟩⟩, ?_⟩
    intro q
    apply (ProEtale.ordinary_constructible_iff A Y _).mpr
    have : Scheme.IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ q).obj (F.rightDerivedFunctor.obj J)) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hFJ.1 q)
    exact ProEtale.isConstructible_of_iso
      ((νY.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso e)
      (ProEtale.isConstructible_comparisonUpperStar_obj _)
  · have hbc : Etale.DerivedCategory.boundedConstructible (ModuleCat B) Y
        (F.rightDerivedFunctor.obj J) := by
      refine ⟨⟨⟨c, hge⟩, ⟨d, hle⟩⟩, fun q ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hFJ.1 q)⟩
    obtain ⟨r, s, ht⟩ :=
      open_finite_field_tor B Y hbc
    exact ⟨r, s, (_root_.DerivedCategory.torAmplitudeIn _ r s).prop_of_iso e
      ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff r s _).2 ht)⟩
private theorem open_finiteInternal_bounded
    (l : ℕ) [Fact l.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ l)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (A : Type u) [Field A] [Finite A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    (hA : (l : A) = 0)
    (K : DerivedCategory (ProEtale.FiniteDiscreteOrdinary.Internal A Z))
    (hK : ProEtale.constantModelBoundedConstructible
      (ProEtale.FiniteDiscreteOrdinary.coefficient A) Z K) :
    ProEtale.constantModelBoundedConstructible
      (ProEtale.FiniteDiscreteOrdinary.coefficient A) Y
      (R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧).obj K) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        (R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧).obj K) := by
  classical
  let E (T : Scheme.{u}) : ProEtale.FiniteDiscreteOrdinary.Encoding A T :=
    (ProEtale.FiniteDiscreteOrdinary.encoding_exists A T).some
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let e : (E Y).fixedDerived.functor.obj
      (R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧).obj K) ≅
      (ProEtale.lowerStar B p).rightDerivedFunctor.obj ((E Z).fixedDerived.functor.obj K) :=
    (ProEtale.FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A p (E Y) (E Z)).app K
  have hsource := (ProEtale.FiniteDiscreteOrdinary.encoding_constructibility A Z (E Z)).2 K
  have himage := open_finiteFixed_bounded l t p A hA _ (hsource.mp hK)
  have hb : ProEtale.FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Y
      ((E Y).fixedDerived.functor.obj
        (R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧).obj K)) := by
    refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm himage.1.1, ?_⟩
    intro q
    exact (ProEtale.FiniteDiscreteOrdinary.constructible_iso A Y
      ((DerivedCategory.homologyFunctor _ q).mapIso e.symm)).mp (himage.1.2 q)
  refine ⟨(ProEtale.FiniteDiscreteOrdinary.encoding_constructibility A Y (E Y)).2 _ |>.mpr hb,
    ?_⟩
  obtain ⟨a, b, ht⟩ := himage.2
  have ht := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht
  exact ⟨min a b, b,
    ((ProEtale.FiniteDiscreteOrdinary.encoding_tensor_tor A Y (E Y)).2.2 _ _ _
      (min_le_right a b)).mpr (ht.mono (min_le_left a b) le_rfl)⟩
private theorem open_integralModel_bounded
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ l)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (K : DerivedCategory (ProEtale.AdicCompletion.Modules l E Z))
    (hK : ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing l E) Z K) :
    ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing l E) Y
      (R((p)_*⟦ProEtale.DerivedNakayama.integerRing l E⟧).obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E 1
  let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal :=
    by
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
  let : DiscreteTopology A := ProEtale.DerivedNakayama.quotientDiscrete l E 1
  have hsource := (ProEtale.internal_integral_residue_criterion l E Z).1 K |>.mp hK
  have hfinite := open_finiteInternal_bounded l t p A
    (ProEtale.IntegralOpenDirectImage.residue_killed l E)
    ((ProEtale.AdicCompletion.derivedReduction l E Z 0).obj K) hsource.2.1
  have hlimits := ProEtale.internal_integral_direct_image_limits l E p
  have hχ := hlimits.choose
  have hpush := hlimits.choose_spec
  let := hχ
  have hcomplete := (hpush K).1 hsource.1
  have hiso := (hpush K).2
  let e : (ProEtale.AdicCompletion.derivedReduction l E Y 0).obj
      (R((p)_*⟦ProEtale.DerivedNakayama.integerRing l E⟧).obj K) ≅
      R((p)_*⟦ProEtale.DerivedNakayama.quotientRing l E 1⟧).obj
        ((ProEtale.AdicCompletion.derivedReduction l E Z 0).obj K) :=
    @asIso _ _ _ _ _ hiso
  have hc := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
    (ProEtale.DerivedNakayama.quotientRing l E 1) Y).2.1
  have ht := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
    (ProEtale.DerivedNakayama.quotientRing l E 1) Y).2.2.2.1
  let := hc
  let := ht
  exact (ProEtale.internal_integral_residue_criterion l E Y).1 _ |>.mpr
    ⟨hcomplete, (ProEtale.constantModelBoundedConstructible _ Y).prop_of_iso e.symm hfinite.1,
      (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm hfinite.2⟩
private theorem open_integral_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (ProEtale.DerivedNakayama.integerRing l E))
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ l)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK : boundedConstructible (condensedRingObj Λ Z) K) :
    boundedConstructible (condensedRingObj Λ Y) (R((p)_*⟦Λ⟧).obj K) := by
  let φ := e.inv.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
  let F (X : Scheme.{u}) : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (ProEtale.DerivedNakayama.integerRing l E) X) :=
    Mod.comap (coefficientMap φ X)
  have (X : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ X)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  have hFK : ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing l E) Z ((F Z).mapDerivedCategory.obj K) := by
    constructor
    · exact (F Z).bounded_mapDerivedCategory_obj hK.1
    intro q
    apply (integerModel_comparison l E Z _).mp
    exact _root_.constructible_of_iso
      (((F Z).mapDerivedCategoryHomologyFunctorIso q).app K)
      (_root_.constructible_comap (coefficientMap φ Z) (hK.2 q))
  have hP := open_integralModel_bounded l E t p _ hFK
  let hi : (F Y).mapDerivedCategory.obj (R((p)_*⟦Λ⟧).obj K) ≅
      R((p)_*⟦ProEtale.DerivedNakayama.integerRing l E⟧).obj
        ((F Z).mapDerivedCategory.obj K) := (derivedComapLowerStarIso φ p).app K
  refine ⟨(F Y).bounded_of_bounded_mapDerivedCategory_obj
    ((DerivedCategory.TStructure.t.bounded).prop_of_iso hi.symm hP.1), ?_⟩
  intro q
  have hH := (integerModel_comparison l E Y _).mpr (hP.2 q)
  have hF : IsConstructibleModuleObject
      (condensedRingObj (ProEtale.DerivedNakayama.integerRing l E) Y)
      ((F Y).obj ((DerivedCategory.homologyFunctor _ q).obj (R((p)_*⟦Λ⟧).obj K))) :=
    _root_.constructible_of_iso
      (((DerivedCategory.homologyFunctor _ q).mapIso hi).symm ≪≫
        ((F Y).mapDerivedCategoryHomologyFunctorIso q).symm.app _) hH
  let ψ := coefficientMap φ Y
  exact _root_.constructible_of_iso
    (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapId _).app _)
    (_root_.constructible_comap (inv ψ) hF)
private theorem open_continuous_of_integral
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (hint : ∀ M : integralConstructible ℓ E Z,
      boundedConstructible (condensedRingObj (integralCoeff ℓ E) Y)
        (R((p)_*⟦integralCoeff ℓ E⟧).obj M.obj))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj K) := by
  -- Cache the module tensor structures used by the scalar-change adjunction.
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Z)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Z)) := inferInstance
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  obtain ⟨M, ⟨e⟩⟩ := continuousConstructible_integral_model ℓ E Z ⟨K, hK⟩
  have := integralScalarPushHom_isIso ℓ E p M
  let φ := coefficientMap (integralScalarMap ℓ E) Y
  let e' : (Mod.extendScalars φ).leftDerivedFunctor.obj
      (R((p)_*⟦integralCoeff ℓ E⟧).obj M.obj) ≅
      R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj K :=
    asIso ((derivedPushHom (integralScalarMap ℓ E) p).app M.obj) ≪≫
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧)).mapIso e
  have hs := ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ φ _ (hint M)
  exact ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e' hs.1,
    fun q ↦ _root_.constructible_of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e') (hs.2 q)⟩
private theorem open_qbar_of_finite
    (ℓ : ℕ) [Fact ℓ.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (hfinite : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (M : PadicSubfieldConstructible Z ℓ E),
      boundedConstructible (padicSubfieldRingObj Y ℓ E)
        (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj M.obj))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (padicAlgClRingObj Z ℓ)))
    (hK : boundedConstructible (padicAlgClRingObj Z ℓ) K) :
    boundedConstructible (padicAlgClRingObj Y ℓ)
      (R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K) := by
  obtain ⟨E, M, ⟨e⟩⟩ := constructibleCocone_essSurjObj Z ℓ ⟨K, hK⟩
  obtain ⟨N, hN⟩ := M.property.1.1
  have : M.obj.IsGE N := hN
  have := isIso_derivedPushHom_padicAlgCl_of_boundedBelow ℓ E p ⟨M.obj, ⟨N, hN⟩⟩
  let e₀ := (boundedConstructible (padicAlgClRingObj Z ℓ)).ι.mapIso e
  let φ := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y
  let e' : (Mod.extendScalars φ).leftDerivedFunctor.obj
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj M.obj) ≅
      R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K :=
    asIso ((derivedPushHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p).app M.obj) ≪≫
      (R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso e₀
  have hs := ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ φ _ (hfinite E M)
  exact ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e' hs.1,
    fun q ↦ _root_.constructible_of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e') (hs.2 q)⟩
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- A constructible adic sheaf on a dense affine open has bounded constructible direct image.

Source: SGA 4½, *Théorème de finitude*, Theorem 1.1 and the open-immersion paragraph of
`sk-prop-sf-finiteness`; Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.7.2,
Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-dense-open-direct-image-finiteness)

Proof: the finite-type target is noetherian and quasi-excellent, and ℓ is invertible on it.
On this target and its open subscheme, local constructibility is equivalent to a finite
lisse stratification. By Proposition 6.8.14, the sheaf in degree zero descends to a bounded
constructible complex over a finite extension E of Q_ℓ and is the rationalization of an
integral constructible complex C over O_E. This passage does not require a global lisse
lattice: Lemma 6.8.13 supplies constructible integral structures and the proof of
Proposition 6.8.14 glues them by the localization of extension groups.

For each power of a uniformizer of O_E, the reduction of C has finite torsion coefficients.
The open-immersion finiteness theorem makes its derived direct image constructible.
The torsion direct-image functor has a finite cohomological-dimension bound independent
of that power (Theorem 6.7.1); together with the two-term resolution of each coefficient
quotient, this gives a uniform finite interval for all the derived direct images of the
reductions. The complete direct image of C is derived complete, and reduction commutes
with direct image, by Lemmas 6.5.9 and 6.5.11. Lemma 6.7.2 consequently makes this integral
direct image constructible. Proposition 6.8.11 identifies this with boundedness and
constructible cohomology. Rationalization and passage to Q̄_ℓ carry this computation to
the ambient derived direct image of modules over the adic coefficient sheaf, as in
Remark 6.8.15. Thus the displayed right derived functor is bounded and all of its
cohomology sheaves are constructible. No bound by the dimensions of the fibres of the
open immersion is asserted. -/
theorem bounded_constructible_rightDerivedFunctor_adicLowerStar_of_denseOpenImmersion
    (hK : ringChar K ≠ l) {Z W : Scheme.{u}} [IsAffine Z]
    (t : W ⟶ Spec (.of K)) [LocallyOfFiniteType t] [QuasiCompact t]
    (j : Z ⟶ W) [IsOpenImmersion j] [QuasiCompact j] (hj : DenseRange j.base)
    (F : AdicSheaf l Z) (hF : IsAdicConstructibleSheaf F) :
    (_root_.DerivedCategory.TStructure.t.bounded ⊓
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l W))
      ((j)_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  classical
  have _ : IsAlgClosed K := inferInstance
  have _ := hj
  have : Fact (ringChar K ≠ l) := ⟨hK⟩
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsNoetherian W := isNoetherian_of_locallyOfFiniteType t
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType j
  let A := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let p := j
  have hA := (DerivedCategory.adicConstructibleHeart_singleFunctor_obj hF).1.1
  have hX := NativeEncoding.encoding_exact_derived l Z
  have hY := NativeEncoding.encoding_exact_derived l W
  let := hX.1
  let := hX.2.1
  let := hY.1
  let := hY.2.1
  have hencoded : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) Z)
      ((NativeEncoding.derivedEncoding l Z).obj A) := by
    refine ⟨(NativeEncoding.encoding l _).bounded_mapDerivedCategory_obj hA.1, ?_⟩
    intro q
    exact _root_.constructible_of_iso
      (((NativeEncoding.encoding l _).mapDerivedCategoryHomologyFunctorIso q).app A)
      ((encoding_constructible_iff _).mp (hA.2 q))
  have hint (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (M : CondensedRing.integralConstructible l E Z) :
      boundedConstructible (condensedRingObj (CondensedRing.integralCoeff l E) W)
        ((CondensedRing.lowerStar (CondensedRing.integralCoeff l E) p).rightDerivedFunctor.obj
          M.obj) := by
    let : FiniteDimensional ℚ_[l] (ULift.{u} E) :=
      (ULift.moduleEquiv (R := ℚ_[l]) (M := E)).symm.finiteDimensional
    exact CondensedRing.open_integral_of_iso l (ULift.{u} E) _
      (CondensedRing.integerNormedIso l E) t p M.obj M.property
  have hp := CondensedRing.open_qbar_of_finite l t p
    (fun E M ↦ CondensedRing.open_continuous_of_integral l E t p
      (hint E) M.obj M.property) _ hencoded
  have himage : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) W)
      ((NativeEncoding.derivedEncoding l W).obj ((adicLowerStar l p).rightDerivedFunctor.obj A)) :=
    ⟨(_root_.DerivedCategory.TStructure.t.bounded).prop_of_iso
      ((NativeEncoding.derivedPushComparison l p).app A).symm hp.1,
      fun q ↦ _root_.constructible_of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
          ((NativeEncoding.derivedPushComparison l p).app A).symm) (hp.2 q)⟩
  refine ⟨(NativeEncoding.encoding l W).bounded_of_bounded_mapDerivedCategory_obj himage.1,
    fun q ↦ ?_⟩
  apply (encoding_constructible_iff _).mpr
  exact _root_.constructible_of_iso
    (((NativeEncoding.encoding l W).mapDerivedCategoryHomologyFunctorIso q).app
      ((adicLowerStar l p).rightDerivedFunctor.obj A)).symm (himage.2 q)

end AlgebraicGeometry.ProEtale
