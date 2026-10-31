/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixCtfGenerators
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedCoefficientData
import all WeilConjectures.SixFunctors.ScalarSixFieldGeneration
import all WeilConjectures.AlgebraicGeometry.IntegralConstantModelLocalResolution
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
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
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
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
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
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
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
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
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
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
import all WeilConjectures.SixFunctors.LocallyClosedGeneratorTensorIntersection
import all WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
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
import Mathlib.Algebra.Category.Grp.AB
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
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
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
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Integral generation from locally free resolutions

Source: blueprint latest, scalar-six-ctf proof (1), integral coefficients.
(blueprint: lem-sfb-native-integral-scalar-generation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

private theorem nonfiniteFiniteHull_closed
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (G : ObjectProperty C) :
    let H : ObjectProperty C := ⨆ n : ℕ, (G.shiftClosure ℤ).extensionProductIter n
    H.IsClosedUnderIsomorphisms ∧ H.IsStableUnderShift ℤ ∧
      H.IsTriangulatedClosed₁ ∧ H.IsTriangulatedClosed₂ ∧ H.IsTriangulatedClosed₃ := by
  let B := G.shiftClosure ℤ
  let H : ObjectProperty C := ⨆ n : ℕ, B.extensionProductIter n
  have : ∀ n, (B.extensionProductIter n).IsClosedUnderIsomorphisms := by
    intro n
    cases n with
    | zero => exact inferInstanceAs B.IsClosedUnderIsomorphisms
    | succ n => rw [B.extensionProductIter_succ]; infer_instance
  have : H.IsClosedUnderIsomorphisms := inferInstanceAs
    (⨆ n : ℕ, B.extensionProductIter n).IsClosedUnderIsomorphisms
  have : H.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro X hX
    obtain ⟨m, hm⟩ := (ObjectProperty.prop_iSup_iff _ _).mp hX
    exact (ObjectProperty.prop_iSup_iff _ _).mpr
      ⟨m, (B.extensionProductIter m).le_shift n X hm⟩⟩⟩
  have : H.IsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃
    obtain ⟨n, hn⟩ := (ObjectProperty.prop_iSup_iff _ _).mp h₁
    obtain ⟨m, hm⟩ := (ObjectProperty.prop_iSup_iff _ _).mp h₃
    apply (ObjectProperty.prop_iSup_iff _ _).mpr
    refine ⟨n + 1 + m, ?_⟩
    rw [B.extensionProductIter_add (show n + 1 = n + 1 from rfl)]
    exact ⟨_, _, _, _, _, hT, hn, hm⟩)
  have : H.IsTriangulatedClosed₁ := .mk' (by
    intro T hT h₂ h₃
    exact H.ext_of_isTriangulatedClosed₂ _
      (Pretriangulated.inv_rot_of_distTriang _ hT) (H.le_shift _ _ h₃) h₂)
  have : H.IsTriangulatedClosed₃ := .mk' (by
    intro T hT h₁ h₂
    exact H.ext_of_isTriangulatedClosed₂ _
      (Pretriangulated.rot_of_distTriang _ hT) h₂ (H.le_shift _ _ h₁))
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem factorization_extension_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} [IsNoetherian X]
    {a : S ⟶ X} (A B : GeneratorFactorization a)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    Nonempty ((generatorExtension Λ A).obj M ≅ (generatorExtension Λ B).obj M) := by
  have hr := generatorRestriction_isIso Λ A
  obtain ⟨e⟩ := generatorExtension_reconstruct Λ B ((generatorExtension Λ A).obj M)
    (fun g hg ↦ generatorExtension_support Λ A g hg M)
  exact ⟨e ≪≫ (generatorExtension Λ B).mapIso ((asIso (generatorRestriction Λ A)).app M)⟩

private theorem resolution_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U : Scheme.{u}}
    (M : ModuleRingedComparison.internalModules Λ U)
    (hM : ResolutionLF (condensedRingObj Λ U) M) : IsLisseCoefficientModule Λ M := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun b ↦ ?_⟩
  let α := condensedPullbackHom Λ (C.f b)
  exact free_of_iso (free_comap (inv α) (hC b))
    ((Mod.extendScalarsIsoComapInv α).app _).symm

private theorem factorization_canonical_extension_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z U : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (M : ModuleRingedComparison.internalModules Λ U) :
    Nonempty ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ j).obj M) ≅
      (coefficientHeartLocallyClosedExtension Λ (j ≫ i) (by infer_instance)).obj M) := by
  have : IsImmersion (j ≫ i) := inferInstance
  have : TopologicalSpace.NoetherianSpace U :=
    (j ≫ i).isEmbedding.isInducing.noetherianSpace
  let A : GeneratorFactorization (j ≫ i) :=
    .inr ⟨Z, j, i, rfl, inferInstance, inferInstance⟩
  let B : GeneratorFactorization (j ≫ i) :=
    .inr ⟨(j ≫ i).image, (j ≫ i).toImage, (j ≫ i).imageι,
      (j ≫ i).toImage_imageι, inferInstance, inferInstance⟩
  have hA : generatorExtension Λ A = openImmersionLowerShriek Λ j ⋙ lowerStar Λ i := rfl
  have hB : generatorExtension Λ B =
      coefficientHeartLocallyClosedExtension Λ (j ≫ i) (by infer_instance) := rfl
  change Nonempty ((openImmersionLowerShriek Λ j ⋙ lowerStar Λ i).obj M ≅ _)
  rw [← hA, ← hB]
  exact factorization_extension_iso Λ A B M

private theorem scalarGenerator_of_iso (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {K L : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)}
    (e : K ≅ L) (hL : sfbPerfectScalarGenerator Λ X L) : sfbPerfectScalarGenerator Λ X K := by
  obtain ⟨S, a, ha, P, hP, ⟨q⟩⟩ := hL
  exact ⟨S, a, ha, P, hP, ⟨e ≪≫ q⟩⟩

private theorem free_factorization_generator (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsNoetherian X.left]
    {Z U : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (j : U ⟶ Z) [IsOpenImmersion j]
    (M : ModuleRingedComparison.internalModules Λ.X U)
    (hM : ResolutionLF (condensedRingObj Λ.X U) M) :
    sfbPerfectScalarGenerator Λ X ((DerivedCategory.singleFunctor _ 0).obj
      ((lowerStar Λ.X i).obj ((openImmersionLowerShriek Λ.X j).obj M))) := by
  obtain ⟨e⟩ := factorization_canonical_extension_iso Λ.X i j M
  apply scalarGenerator_of_iso Λ X ((DerivedCategory.singleFunctor _ 0).mapIso e)
  exact single_extension_generator Λ X U (j ≫ i) inferInstance M (resolution_lisse Λ.X M hM)

/-- Bounded constant-model integral complexes have finite scalar-perfect extension
witnesses. Source: scalar-six-ctf proof (1), integral tensor-shriek generation proof.
(blueprint: lem-sfb-native-integral-scalar-generation).

Proof: finite constant local models are locally finitely presented. The finite
open/closed extension tower reduces constructible sheaves to locally finitely
presented stratum modules. Their existing two-term locally free resolutions reduce
these pieces to locally free modules in degree zero. On a free chart use the
single complex on the finite free scalar module; zero terms use rank zero. Support
and restriction identify each open/closed factorization with the canonical image
factorization. Exact extension preserves the short exact resolution triangle.
The union of finite extensions of shifts is closed under all three triangle
operations. Bounded derived devissage therefore gives the same assertion for each
bounded constructible complex. Take its identity retract. -/
theorem sfbNativeIntegralGeneration
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (k : Type u) [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (K : ConstantModelConstructibleFiniteTor (CondensedRing.integralCoefficientRing ell E)
      X.left) :
    ∃ n : ℕ, (((sfbPerfectScalarGenerator
        ⟨(CondensedRing.integralCoefficientRing ell E)⟩ X).shiftClosure ℤ).extensionProductIter n
      ).retractClosure K.obj := by
  classical
  let Λ : ScalarSixRing.{u} := ⟨(CondensedRing.integralCoefficientRing ell E)⟩
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  let P : ObjectProperty (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)) :=
    ⨆ n : ℕ, ((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
  obtain ⟨hi, hs, ht₁, ht₂, ht₃⟩ := nonfiniteFiniteHull_closed
    (sfbPerfectScalarGenerator Λ X)
  have : P.IsClosedUnderIsomorphisms := hi
  have : P.IsStableUnderShift ℤ := hs
  have : P.IsTriangulatedClosed₁ := ht₁
  have : P.IsTriangulatedClosed₂ := ht₂
  have : P.IsTriangulatedClosed₃ := ht₃
  have hgen : sfbPerfectScalarGenerator Λ X ≤ P := by
    intro M hM
    apply (ObjectProperty.prop_iSup_iff _ _).mpr
    exact ⟨0, (ObjectProperty.le_shiftClosure (A := ℤ) _) M hM⟩
  have hpiece : condensedLocallyClosedPiece Λ.X X.left ≤ P := by
    intro L hL
    obtain ⟨Z, U, i, j, hi, hj, hqc, M, hM, ⟨eL⟩⟩ := hL
    have := hi
    have := hj
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    have : IsNoetherian Z := ⟨⟩
    have : TopologicalSpace.NoetherianSpace U :=
      j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    let V : X.left.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨hex, _⟩ := condensed_open_closed_recollement Λ.X i V.ι V.range_ι
    have := hex
    let F := (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙
      (lowerStar Λ.X i).mapDerivedCategory
    have hfree (N : ModuleRingedComparison.internalModules Λ.X U)
        (hN : ResolutionLF (condensedRingObj Λ.X U) N) :
        P (F.obj ((DerivedCategory.singleFunctor _ 0).obj N)) := by
      let e : F.obj ((DerivedCategory.singleFunctor _ 0).obj N) ≅
          (DerivedCategory.singleFunctor _ 0).obj
            ((lowerStar Λ.X i).obj ((openImmersionLowerShriek Λ.X j).obj N)) :=
        (lowerStar Λ.X i).mapDerivedCategory.mapIso
          (((openImmersionLowerShriek Λ.X j).mapDerivedCategorySingleFunctor 0).app N) ≪≫
          ((lowerStar Λ.X i).mapDerivedCategorySingleFunctor 0).app _
      exact P.prop_of_iso e.symm (hgen _ (free_factorization_generator Λ X i j N hN))
    obtain ⟨T, ht, ⟨eT⟩, h₁, h₂⟩ := localModelResolution ell E U M hM
    have hthird : P (F.obj ((DerivedCategory.singleFunctor _ 0).obj T.X₃)) :=
      P.ext_of_isTriangulatedClosed₃ _ (F.map_distinguished _ ht.singleTriangle_distinguished)
        (hfree T.X₁ h₁) (hfree T.X₂ h₂)
    have hM' : P (F.obj ((DerivedCategory.singleFunctor _ 0).obj M)) :=
      P.prop_of_iso (F.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso eT)) hthird
    let eF : F.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((lowerStar Λ.X i).obj ((openImmersionLowerShriek Λ.X j).obj M)) :=
      (lowerStar Λ.X i).mapDerivedCategory.mapIso
        (((openImmersionLowerShriek Λ.X j).mapDerivedCategorySingleFunctor 0).app M) ≪≫
        ((lowerStar Λ.X i).mapDerivedCategorySingleFunctor 0).app _
    exact P.prop_of_iso (eF ≪≫ eL.symm) hM'
  have hheart (M : ModuleRingedComparison.internalModules Λ.X X.left)
      (hM : IsConstructibleModuleObject (condensedRingObj Λ.X X.left) M) :
      P ((DerivedCategory.singleFunctor _ 0).obj M) := by
    obtain ⟨r, hr⟩ := exists_condensedLocallyClosed_extension_tower X.left Λ.X M hM
    exact (condensedLocallyClosedPiece Λ.X X.left).extensionProductIter_le_of_isTriangulatedClosed₂
      hpiece r _ hr
  have : P.ContainsZero := ⟨(DerivedCategory.singleFunctor _ 0).obj 0,
    (DerivedCategory.singleFunctor _ 0).map_isZero (isZero_zero _),
    hheart 0 (constructible_of_isZero _ _ (isZero_zero _))⟩
  have : P.IsTriangulated := {}
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructibleModuleObject (condensedRingObj Λ.X X.left)) :=
    ⟨fun e hM ↦ _root_.constructible_of_iso e hM⟩
  have hK : P K.obj := by
    apply DerivedCategory.prop_of_bounded P
      (IsConstructibleModuleObject (condensedRingObj Λ.X X.left)) hheart K.obj K.property.1.1
    intro q
    apply constructible_of_finiteConstantStratified Λ.X X.left
    have hq := K.property.1.2 q
    simpa only [IsConstantModelConstructible,
      if_pos (show CompactSpace X.left ∧ QuasiSeparatedSpace X.left from
        ⟨inferInstance, inferInstance⟩)]
      using hq
  obtain ⟨n, hn⟩ := (ObjectProperty.prop_iSup_iff _ _).mp hK
  exact ⟨n, _, hn, ⟨Retract.refl K.obj⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
