/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.IntegralModelSurjectiveClosedReflection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleOpenClosedImages
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
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
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.Algebra.Category.Grp.FilteredColimits
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
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
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
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
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
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import all WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import all Mathlib.Topology.MetricSpace.Ultra.Basic
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Analysis.Normed.Group.Ultra
import all Mathlib.Data.Finset.Max
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import all WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import all WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all Mathlib.Data.Fin.Tuple.Basic
import all WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import all WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import all Mathlib.CategoryTheory.Sites.Adjunction
import all Mathlib.Algebra.Category.Grp.Adjunctions
import all WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRingSupplement
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Topology.StratificationDense
import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Module.Shrink
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

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

/-- Open extension by zero, closed direct image, and their locally closed composites
preserve integral bounded constructibility.
Source: blueprint det-lem-int-tensor-shriek, clause (1)
(blueprint: det-lem-int-tensor-shriek).

Proof: use exact derived homology comparison and the existing constructible-image
results for open extension by zero and closed direct image. The bounded-map theorem
preserves bounds. For closed direct image, the open complement supplies exactness via
condensed recollement, and the right-derived/map-derived comparison identifies the image.
Apply the two assertions successively for a locally closed immersion. -/
theorem integralTensorShriek_preserves
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsNoetherian X]
    : (∀ (U : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j]
        (M : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X
          U)),
        boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X U) M →
          boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X X)
            ((CondensedRing.openImmersionLowerShriek (integralModelCondensedCoefficients l E).X
              j).mapDerivedCategory.obj M)) ∧
      (∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
        (M : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X
          Z)),
        boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X Z) M →
          boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X X)
            ((CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
              i).rightDerivedFunctor.obj M)) ∧
      (∀ (S Z : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X)
        [IsOpenImmersion v] [IsClosedImmersion i]
        (M : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X
          S)),
        boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X S) M →
          boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X X)
            (((CondensedRing.openImmersionLowerShriek (integralModelCondensedCoefficients l E).X
              v).mapDerivedCategory ⋙
              (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
                i).rightDerivedFunctor).obj M)) := by
  let Λ := (integralModelCondensedCoefficients l E).X
  have hopen (Y : Scheme.{u}) [IsNoetherian Y] (U : Scheme.{u})
      (j : U ⟶ Y) [IsOpenImmersion j]
      (M : DerivedCategory (pulledBackModuleObjects Λ U))
      (hM : boundedConstructible (condensedRingObj Λ U) M) :
      boundedConstructible (condensedRingObj Λ Y)
        ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj M) := by
    refine ⟨(CondensedRing.openImmersionLowerShriek Λ j).bounded_mapDerivedCategory_obj
      hM.1, fun n ↦ ?_⟩
    exact _root_.constructible_of_iso
      (((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso
        n).app M)
      (CondensedRing.isConstructibleModuleObject_openImmersionLowerShriek Λ j _ (hM.2 n))
  have hclosed (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      (M : DerivedCategory (pulledBackModuleObjects Λ Z))
      (hM : boundedConstructible (condensedRingObj Λ Z) M) :
      boundedConstructible (condensedRingObj Λ X)
        ((CondensedRing.lowerStar Λ i).rightDerivedFunctor.obj M) := by
    let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hij : Set.range U.ι = (Set.range i)ᶜ := U.range_ι
    obtain ⟨hex, _⟩ := CondensedRing.condensed_open_closed_recollement Λ i U.ι hij
    let := hex
    let e := (CondensedRing.lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app M
    refine ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e.symm
      ((CondensedRing.lowerStar Λ i).bounded_mapDerivedCategory_obj hM.1), fun n ↦ ?_⟩
    exact _root_.constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e.symm)
      (_root_.constructible_of_iso
        (((CondensedRing.lowerStar Λ i).mapDerivedCategoryHomologyFunctorIso n).app M)
        ((CondensedRing.constructible_open_closed_images Λ U.ι i hij).2 _ (hM.2 n)))
  refine ⟨hopen X, hclosed, ?_⟩
  intro S Z v i hv hi M hM
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  let : IsNoetherian Z := ⟨⟩
  exact hclosed Z i _ (hopen Z S v M hM)


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

private theorem locallyFreeSingleModel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u})
    (M : pulledBackModuleObjects (integralModelCondensedCoefficients l E).X Y)
    (hM : (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ b : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f b)).obj
        (condensedRingObj (integralModelCondensedCoefficients l E).X Y))
        (((ProEtale.upperStar Ab.{u + 1} (C.f b)).mapMod _).obj M))) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ b : C.I₀,
      ∃ Q : CochainComplex
        (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (integralModelCondensedCoefficients l E).X) ℤ,
        (∃ r s : ℤ, ∀ n : ℤ, n < r ∨ s < n → IsZero (Q.X n)) ∧
        (∀ n : ℤ, Mod.IsFree (integralModelCondensedCoefficients l E).X (Q.X n)) ∧
        Nonempty ((CondensedRing.upperStar (integralModelCondensedCoefficients l E).X
          (C.f b)).mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
            DerivedCategory.Q.obj (integralTensorShriek_pointComplex l E (C.X b) Q)) := by
  let Λ := (integralModelCondensedCoefficients l E).X
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun b ↦ ?_⟩
  let F := (upperStarFromPoint (C.X b)).mapMod Λ
  let α := condensedPullbackHom Λ (C.f b)
  have hfree : Mod.IsFree (condensedRingObj Λ (C.X b))
      ((CondensedRing.upperStar Λ (C.f b)).obj M) := by
    exact free_of_iso (free_comap (inv α) (hC b))
      ((Mod.extendScalarsIsoComapInv α).app _).symm
  obtain ⟨n, ⟨e⟩⟩ := hfree
  let A := Mod.finiteFree Λ n
  let Q := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A
  refine ⟨Q, ⟨0, 0, fun q hq ↦ ?_⟩, fun q ↦ ?_, ?_⟩
  · exact HomologicalComplex.isZero_single_obj_X _ 0 A q (by omega)
  · by_cases hq : q = 0
    · subst q
      exact ⟨n, ⟨HomologicalComplex.singleObjXSelf _ 0 A⟩⟩
    · exact freeZero Λ (HomologicalComplex.isZero_single_obj_X _ 0 A q hq)
  · obtain ⟨ep⟩ := freeFromPoint Λ (C.X b) n
    let : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
    let : (upperStarFromPoint (C.X b)).IsLeftAdjoint :=
      inferInstanceAs ((pointUpperStar ⋙
        ProEtale.upperStar Ab.{u + 1} (toSpecZ (C.X b))).IsLeftAdjoint)
    exact ⟨((CondensedRing.upperStar Λ (C.f b)).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (e ≪≫ ep) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (F.obj A) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app A).symm⟩

-- Construct the sheaf isomorphism with abstract coefficient rings, so that typeclass
-- search does not repeatedly expand the induced normed-field structures.
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
  have hm (x : E) : x ∈ Padic.coefficientExtensionIntegers l E ↔ ‖x‖ ≤ 1 := by
    exact (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 x
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

private theorem modelResolution (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : pulledBackModuleObjects (integralModelCondensedCoefficients l E).X X)
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (integralModelCondensedCoefficients l E).X X) P) :
    ∃ S : ShortComplex (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X X),
      S.ShortExact ∧ Nonempty (S.X₃ ≅ P) ∧
      ResolutionLF (condensedRingObj (integralModelCondensedCoefficients l E).X X) S.X₁ ∧
      ResolutionLF (condensedRingObj (integralModelCondensedCoefficients l E).X X) S.X₂ := by
  obtain ⟨F, nf, na, fd, ⟨e⟩⟩ := coefficientSmallIso l E
  let := nf
  let := na
  let := fd
  let φ : condensedRingObj (integralModelCondensedCoefficients l E).X X ⟶
      condensedRingObj (integralCoeff l F) X := (upperStarFromPoint X).map e.hom.hom
  have : IsMonHom e.hom.hom := inferInstance
  have : IsMonHom φ := inferInstance
  let G : pulledBackModuleObjects (integralCoeff l F) X ⥤
      pulledBackModuleObjects (integralModelCondensedCoefficients l E).X X := Mod.comap φ
  obtain ⟨F₁, F₀, f, g, w, hs, h₁, h₀⟩ := integral_lfp_locallyFree_resolution X l F
    ((Mod.comap (inv φ)).obj P) (lfp_comap (inv φ) hP)
  refine ⟨(ShortComplex.mk f g w).map G, hs.map_of_exact G,
    ⟨(Mod.comapEquivalenceOfIsIso φ).counitIso.app P⟩, ?_, ?_⟩
  · exact locally_free_comap φ h₁
  · exact locally_free_comap φ h₀

@[reducible] private noncomputable def stratumPresentation
    {X Z U : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ Z) [IsOpenImmersion j] : X.FiniteLocallyClosedStratification := by
  let V := j.opensRange
  let S := Scheme.Stratification.ofClosedImmersionOpens i V
  exact
    { n := 3
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := ![(Scheme.openComplementOfIsClosedImmersion i).toScheme, U,
        (Scheme.IdealSheafData.vanishingIdeal ⟨(V : Set Z)ᶜ,
          V.isOpen.isClosed_compl⟩).subscheme]
      immersion a := match a with
        | 0 => (Scheme.openComplementOfIsClosedImmersion i).ι
        | 1 => j ≫ i
        | 2 => V.closedComplement ≫ i
      isImmersion a := by fin_cases a <;> dsimp <;> infer_instance
      range_immersion a := by
        fin_cases a
        · exact S.range_immersion ⟨0, by exact Nat.zero_lt_succ 2⟩
        · change Set.range (j ≫ i) = i '' (V : Set Z)
          simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
            Set.range_comp]
          rfl
        · exact S.range_immersion ⟨2, by exact Nat.lt_succ_self 2⟩ }

private theorem triangulatedOfThree
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulatedClosed₁] [P.IsTriangulatedClosed₂] [P.IsTriangulatedClosed₃] :
    P.IsTriangulated := by
  have hup (X : C) (hX : P X) : P (X⟦(1 : ℤ)⟧) :=
    P.ext_of_isTriangulatedClosed₃ _ (contractible_distinguished₂ X) hX (P.prop_zero)
  have hdown (X : C) (hX : P X) : P (X⟦(-1 : ℤ)⟧) := by
    apply P.ext_of_isTriangulatedClosed₁ _ (contractible_distinguished₂ (X⟦(-1 : ℤ)⟧))
      P.prop_zero
    exact P.prop_of_iso ((shiftFunctorAdd' C (-1) 1 0 (by omega)).symm.app X ≪≫
      (shiftFunctorZero C ℤ).app X).symm hX
  have hs (n : ℤ) (X : C) (hX : P X) : P (X⟦n⟧) := by
    induction n using Int.induction_on with
    | zero => exact P.prop_of_iso ((shiftFunctorZero C ℤ).app X).symm hX
    | succ n ih =>
      exact P.prop_of_iso ((shiftFunctorAdd C (n : ℤ) 1).symm.app X) (hup _ ih)
    | pred n ih =>
      exact P.prop_of_iso ((shiftFunctorAdd C (-(n : ℤ)) (-1)).symm.app X)
        (hdown _ ih)
  let : P.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨fun X hX ↦ hs n X hX⟩⟩
  exact {}


/-- Every integral bounded constructible complex is generated by extensions, with the
source's explicit two-out-of-three meaning, and isomorphisms from extensions by zero of
stratum complexes locally obtained from bounded finite free scalar complexes.
Source: blueprint det-lem-int-tensor-shriek, clause (2)
(blueprint: det-lem-int-tensor-shriek).

Proof: first treat sheaves in degree zero. A locally finite free sheaf has the
required point-complex model: on a free cover use the single complex on the corresponding
finite free module at the coefficient point. Put any open immersion into a closed
subscheme into an explicit three-stratum stratification of X, so the generator hypothesis
applies. Transport the integral locally finite free resolution theorem to the stated
coefficient ring using the spectral norm, a small equivalent field and its isometric
integer-ring isomorphism. Its short exact sequence and the exact derived extension functor
show that every locally finitely presented single-sheaf piece belongs to P. The finite
open/closed extension tower then gives every constructible sheaf in degree zero. In
particular P contains zero. Contractible triangles give closure under shifts by 1 and -1,
and integer induction gives all shifts. Finally apply bounded derived-category devissage,
using the finite canonical truncation triangles and the constructible homology of K.
The construction includes zero ranks, zero sheaves and empty strata. -/
theorem integralTensorShriek_generated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsNoetherian X]
    (K : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X X))
    (hK : boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X X) K)
    (P : ObjectProperty (DerivedCategory (pulledBackModuleObjects
      (integralModelCondensedCoefficients l E).X X)))
    [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulatedClosed₁] [P.IsTriangulatedClosed₂] [P.IsTriangulatedClosed₃]
    (hgen : ∀ (T : X.FiniteLocallyClosedStratification) (a : Fin T.n)
      (Z : Scheme.{u}) (v : T.domain a ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i],
      v ≫ i = T.immersion a →
      ∀ M : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X
        (T.domain a)),
        boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X
          (T.domain a)) M →
        (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (T.domain a), ∀ b : C.I₀,
          ∃ Q : CochainComplex
            (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
              (integralModelCondensedCoefficients l E).X) ℤ,
            (∃ r s : ℤ, ∀ n : ℤ, n < r ∨ s < n → IsZero (Q.X n)) ∧
            (∀ n : ℤ, Mod.IsFree (integralModelCondensedCoefficients l E).X (Q.X n)) ∧
            Nonempty
              ((CondensedRing.upperStar (integralModelCondensedCoefficients l E).X (C.f
                b)).mapDerivedCategory.obj M ≅
                DerivedCategory.Q.obj
                  (integralTensorShriek_pointComplex l E (C.X b) Q))) →
        P (((CondensedRing.openImmersionLowerShriek (integralModelCondensedCoefficients l E).X
          v).mapDerivedCategory ⋙
          (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
            i).rightDerivedFunctor).obj M)) :
    P K := by
  classical
  let Λ := (integralModelCondensedCoefficients l E).X
  have hsingle (Y : Scheme.{u}) (M : pulledBackModuleObjects Λ Y)
      (hM : IsConstructibleModuleObject (condensedRingObj Λ Y) M) :
      boundedConstructible (condensedRingObj Λ Y)
        ((DerivedCategory.singleFunctor _ 0).obj M) := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun q ↦ ?_⟩
    rcases lt_trichotomy q 0 with hq | rfl | hq
    · exact constructible_of_isZero _ _ (DerivedCategory.isZero_of_isGE _ 0 q hq)
    · exact _root_.constructible_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
    · exact constructible_of_isZero _ _ (DerivedCategory.isZero_of_isLE _ 0 q hq)
  have hlfconstructible (Y : Scheme.{u}) (M : pulledBackModuleObjects Λ Y)
      (hM : ResolutionLF (condensedRingObj Λ Y) M) :
      IsConstructibleModuleObject (condensedRingObj Λ Y) M := by
    have hfp : IsLocallyFinitelyPresented (condensedRingObj Λ Y) M := by
      obtain ⟨C, hC⟩ := hM
      exact ⟨C, fun b ↦ fp_of_free (hC b)⟩
    exact ⟨Scheme.Stratification.trivial Y,
      fun a ↦ localFinitePresentation_pullback _ hfp⟩
  have hfree (Z U : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      (j : U ⟶ Z) [IsOpenImmersion j]
      (M : pulledBackModuleObjects Λ U)
      (hM : ResolutionLF (condensedRingObj Λ U) M) :
      P (((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (CondensedRing.lowerStar Λ i).rightDerivedFunctor).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) := by
    exact hgen (stratumPresentation i j) (1 : Fin 3) Z j i rfl _
      (hsingle U M (hlfconstructible U M hM)) (locallyFreeSingleModel l E U M hM)
  have hpiece : condensedLocallyClosedPiece Λ X ≤ P := by
    intro L hL
    obtain ⟨Z, U, i, j, hi, hj, hqc, M, hM, ⟨eL⟩⟩ := hL
    let := hi
    let := hj
    let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    let : IsNoetherian Z := ⟨⟩
    let : TopologicalSpace.NoetherianSpace U :=
      j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    let V : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨hex, _⟩ := CondensedRing.condensed_open_closed_recollement Λ i V.ι V.range_ι
    let := hex
    let F := (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
      (CondensedRing.lowerStar Λ i).mapDerivedCategory
    have hcomparison (N : DerivedCategory (pulledBackModuleObjects Λ U)) :
        F.obj N ≅ ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
          (CondensedRing.lowerStar Λ i).rightDerivedFunctor).obj N :=
      ((CondensedRing.lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app _).symm
    have hfree' (N : pulledBackModuleObjects Λ U)
        (hN : ResolutionLF (condensedRingObj Λ U) N) :
        P (F.obj ((DerivedCategory.singleFunctor _ 0).obj N)) :=
      P.prop_of_iso (hcomparison _).symm (hfree Z U i j N hN)
    obtain ⟨S, hs, ⟨eS⟩, h₁, h₂⟩ := modelResolution l E U M hM
    have hthird : P (F.obj ((DerivedCategory.singleFunctor _ 0).obj S.X₃)) :=
      P.ext_of_isTriangulatedClosed₃ _
        (F.map_distinguished _ hs.singleTriangle_distinguished)
        (hfree' S.X₁ h₁) (hfree' S.X₂ h₂)
    have hM' : P (F.obj ((DerivedCategory.singleFunctor _ 0).obj M)) :=
      P.prop_of_iso (F.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso eS)) hthird
    let eF : F.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar Λ i).obj
            ((CondensedRing.openImmersionLowerShriek Λ j).obj M)) :=
      (CondensedRing.lowerStar Λ i).mapDerivedCategory.mapIso
        (((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategorySingleFunctor 0).app M)
        ≪≫ ((CondensedRing.lowerStar Λ i).mapDerivedCategorySingleFunctor 0).app _
    exact P.prop_of_iso (eF ≪≫ eL.symm) hM'
  have hheart (M : pulledBackModuleObjects Λ X)
      (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
      P ((DerivedCategory.singleFunctor _ 0).obj M) := by
    obtain ⟨r, hr⟩ := exists_condensedLocallyClosed_extension_tower X Λ M hM
    exact (condensedLocallyClosedPiece Λ X).extensionProductIter_le_of_isTriangulatedClosed₂
      hpiece r _ hr
  let : P.ContainsZero := ⟨(DerivedCategory.singleFunctor _ 0).obj 0,
    (DerivedCategory.singleFunctor _ 0).map_isZero (isZero_zero _),
    hheart 0 (constructible_of_isZero _ _ (isZero_zero _))⟩
  let : P.IsTriangulated := triangulatedOfThree P
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructibleModuleObject (condensedRingObj Λ X)) :=
    ⟨fun e hM ↦ _root_.constructible_of_iso e hM⟩
  exact DerivedCategory.prop_of_bounded P
    (IsConstructibleModuleObject (condensedRingObj Λ X)) hheart K hK.1 hK.2


end AlgebraicGeometry.ProEtale
