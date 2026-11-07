/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Submission.WeilConjectures.AlgebraicGeometry.Integral.IntegralModelSurjectiveClosedReflection
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all Submission.WeilConjectures.ConstructibleSheaf.Pullback
import all Submission.WeilConjectures.ConstructibleSheaf.OpenClosed
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Submission.WeilConjectures.AlgebraicGeometry.CondensedConstructibleOpenClosedImages
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import Submission.WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Submission.WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Data.Int.Interval
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import Submission.WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import Submission.WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology
import Submission.WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import Submission.WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
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
import Mathlib.CategoryTheory.Monoidal.Mod
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
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.ContinuousMap.Defs
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all Submission.WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Submission.WeilConjectures.ConstructibleSheaf.Refinement
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Submission.WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all Submission.WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Submission.WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all Submission.WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all Submission.WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Submission.WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all Submission.WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all Submission.WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all Submission.WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all Submission.WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all Submission.WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all Submission.WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import all Mathlib.Topology.MetricSpace.Ultra.Basic
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Analysis.Normed.Group.Ultra
import all Mathlib.Data.Finset.Max
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import all Submission.WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all Mathlib.Data.Fin.Tuple.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all Submission.WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all Submission.WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import all Submission.WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import all Mathlib.CategoryTheory.Sites.Adjunction
import all Mathlib.Algebra.Category.Grp.Adjunctions
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all Submission.WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import all Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Submission.WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
import Submission.WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import Submission.WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Submission.WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import Submission.WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Submission.WeilConjectures.Topology.StratificationDense
import Submission.WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Module.Shrink
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Integral constructibility under immersions and generation by strata

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-tensor,
`det-lem-int-tensor-shriek.md` and its proof; Stacks Project, Tags 09AA, 09BM, 09BP
(blueprint: det-lem-int-tensor-shriek).

The coefficient ring is the existing continuous condensed valuation ring. Local complex
models are pulled back from finite free complexes on the point, so their differentials
are scalar matrices over the valuation ring, rather than arbitrary sheaf morphisms.
Generation is expressed by membership in every isomorphism-closed full subcategory
satisfying all three two-out-of-three conditions and containing the specified generators.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

/-- Pull a bounded finite free complex on the coefficient point to a scheme, term by
term. This is the model P tensor O_{E,X}: maps between finite copies of the regular
module on the point are scalar matrices over O_E.
Source: blueprint det-lem-int-tensor-shriek, clause (2)
(blueprint: det-lem-int-tensor-shriek). -/
noncomputable def integralTensorShriek_pointComplex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (Q : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (integralModelCondensedCoefficients l E).X) ℤ) :
    CochainComplex
      (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X X) ℤ :=
  letI : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
  letI : (upperStarFromPoint X).IsLeftAdjoint :=
    inferInstanceAs ((pointUpperStar ⋙ upperStar Ab.{u + 1} (toSpecZ X)).IsLeftAdjoint)
  (Functor.mapHomologicalComplex
    ((upperStarFromPoint X).mapMod (integralModelCondensedCoefficients l E).X)
    (ComplexShape.up ℤ)).obj Q

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  upperStar lowerStar upperStarFromPoint CondensedRing.upperStarComp upperStarFromPointComp
  Mod.extendScalarsIsoComapInv

open MonoidalCategory MonObj CondensedRing
open CategoryTheory.Pretriangulated

private theorem freeZero {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] (R : C) [MonObj R] [PreservesFiniteColimits (tensorLeft R)]
    {M : Mod C R} (hM : IsZero M) : Mod.IsFree R M := by
  have hzero : IsZero (Mod.finiteFree R 0) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro i
    exact Fin.elim0 i
  exact ⟨0, ⟨hM.iso hzero⟩⟩

private theorem freeFromPoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) (n : ℕ) :
    Nonempty (Mod.finiteFree (condensedRingObj Λ Y) n ≅
      ((upperStarFromPoint Y).mapMod Λ).obj (Mod.finiteFree Λ n)) := by
  let : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
  let : (upperStarFromPoint Y).IsLeftAdjoint :=
    inferInstanceAs ((pointUpperStar ⋙ ProEtale.upperStar Ab.{u + 1} (toSpecZ Y)).IsLeftAdjoint)
  have : PreservesFiniteColimits (upperStarFromPoint Y) := by
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint Y).mapMod Λ
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : PreservesBiproductsOfShape (Fin n) F :=
    preservesBiproductsOfShape_of_preservesCoproductsOfShape F
  let e : F.obj (Mod.regular Λ) ≅ Mod.regular (condensedRingObj Λ Y) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  exact ⟨(F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    biproduct.mapIso (fun _ ↦ e)).symm⟩

private theorem continuousCoefficientIso
    (A : Type) (B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (ei : A ≃+* B) (hc : Continuous ei) (hc' : Continuous ei.symm) :
    Nonempty (Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf B) := by
  refine ⟨{
      hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        change ei.symm (ei (f.down x)) = f.down x
        exact ei.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        change ei (ei.symm (f.down x)) = f.down x
        exact ei.apply_symm_apply _ }⟩

private theorem coefficientSmallIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃ (F : Type) (_ : NormedField F) (_ : NormedAlgebra ℚ_[l] F)
      (_ : FiniteDimensional ℚ_[l] F),
      Nonempty (Mon.mk (integralModelCondensedCoefficients l E).X ≅
        Mon.mk (integralCoeff.{u} l F)) := by
  let := spectralNorm.normedField (Padic l) E
  let := spectralNorm.normedAlgebra (Padic l) E
  let : Small.{0} E := Module.Finite.small (Padic l) E
  let F := Shrink.{0} E
  let e : F ≃ₐ[Padic l] E := Shrink.algEquiv (Padic l) E
  let : NormedField F := NormedField.induced F E e.toRingHom e.injective
  let : NormedAlgebra ℚ_[l] F := ⟨fun a x ↦ by
    change ‖e (a • x)‖ ≤ ‖a‖ * ‖e x‖
    change ‖e.toLinearMap (a • x)‖ ≤ ‖a‖ * ‖e x‖
    rw [e.toLinearMap.map_smul]
    exact norm_smul_le a (e x)⟩
  let : FiniteDimensional ℚ_[l] F := e.symm.toLinearEquiv.finiteDimensional
  refine ⟨F, inferInstance, inferInstance, inferInstance, ?_⟩
  have hm (x : E) : x ∈ Padic.coefficientExtensionIntegers l E ↔ ‖x‖ ≤ 1 := Iff.rfl
  have hmem (x : F) : x ∈ continuousIntegers l F ↔ e x ∈
      Padic.coefficientExtensionIntegers l E := by
    rw [hm]
    change ‖x‖₊ ≤ 1 ↔ ‖e x‖ ≤ 1
    exact NNReal.coe_le_coe.symm
  let ei : continuousIntegers l F ≃+* Padic.coefficientExtensionIntegers l E :=
    { toFun := fun x ↦ ⟨e x, (hmem x).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x, (hmem _).mpr (by
        simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }
  have hei : Isometry ei := fun _ _ ↦ rfl
  have heis : Isometry ei.symm := hei.right_inv ei.right_inv
  let : CommRing (continuousIntegers l F) := inferInstance
  let : CommRing (Padic.coefficientExtensionIntegers l E) := inferInstance
  obtain ⟨er⟩ := continuousCoefficientIso (continuousIntegers l F)
    (Padic.coefficientExtensionIntegers l E) ei hei.continuous heis.continuous
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨(Mon.mkIso ea).symm⟩

end AlgebraicGeometry.ProEtale
