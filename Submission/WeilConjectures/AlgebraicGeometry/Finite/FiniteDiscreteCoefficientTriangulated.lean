/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
import all Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Submission.WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import Submission.WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Condensed.TopComparison
import Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import Submission.WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import Submission.WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import Submission.WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import Submission.WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import Submission.WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Max
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import Submission.WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.Algebra.Category.ModuleCat.Basic
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import Submission.WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Submission.WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import Submission.WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Field.ULift
import Submission.WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import Submission.WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.Tuple.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import Submission.WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Submission.WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Submission.WeilConjectures.ConstructibleSheaf.Refinement
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Submission.WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import Submission.WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import Submission.WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import Submission.WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Free
import Submission.WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import Submission.WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleKernels

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!

# Bounded constructible module objects over `T̲` and `O̲` form triangulated subcategories

This file is the counterpart, for the two coefficient rings of the module
`FiniteDiscreteCoefficient`
in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitBallRingObj`,
of the instances
`ProEtale.isTriangulated_boundedConstructible_padicIntegersRingObj`,
`ProEtale.isTriangulated_boundedConstructible_continuousMapRingObj` and
`ProEtale.isTriangulated_boundedConstructible_padicAlgClRingObj` of
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`: on a topologically noetherian
scheme `X`, the bounded constructible complexes of module objects over

* `T̲ = Profinite.continuousMapRingObj T`, `T` a finite discrete ring
  (`ProEtale.isTriangulated_boundedConstructible_finiteDiscreteRingObj`), and over
* `O̲ = Profinite.continuousMapRingObj O`, `O` the closed unit ball of a finite normed extension
  `E` of `ℚ_ℓ` (`ProEtale.isTriangulated_boundedConstructible_unitBallRingObj`),

form a triangulated subcategory of the derived category. As there, this follows from the
constructible module objects being closed under kernels, cokernels and extensions: for `T` by the
finite discrete kernel theorem `finiteDiscrete_constructible_kernel`, for `O` by the integral Serre
theorem `integralConstructible_serre` for the valuation ring `continuousIntegers ℓ E`, which is the
closed unit ball.

-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CondensedRing

variable (X : Scheme.{u})

/-- For a finite discrete ring `T`, the bounded constructible complexes of `T_X`-modules on a
topologically noetherian scheme form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_finiteDiscreteRingObj
    [TopologicalSpace.NoetherianSpace X] (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [DiscreteTopology T] [Finite T] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X)).IsTriangulated := by
  obtain ⟨hc, he⟩ := constructible_cokernels_extensions X
    (condensedRingObj (Profinite.continuousMapRingObj T) X)
  exact isTriangulated_boundedConstructible_of_serre _
    (fun M N f hM hN ↦ ⟨finiteDiscrete_constructible_kernel T X M N f hM hN,
      ObjectProperty.prop_cokernel _ f hM hN⟩)
    (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)

-- The prime `ℓ` occurs only in the instance `NormedAlgebra ℚ_[ℓ] E`; it is found from the
-- local instance `Fact ℓ.Prime`, so the synthesis order is not the default one.
set_option synthInstance.checkSynthOrder false in
/-- For the closed unit ball `O` of a finite normed extension `E` of `ℚ_ℓ`, the bounded
constructible complexes of `O_X`-modules on a topologically noetherian scheme form a triangulated
subcategory. -/
instance isTriangulated_boundedConstructible_unitBallRingObj
    [TopologicalSpace.NoetherianSpace X] (ℓ : ℕ) [Fact ℓ.Prime] {E : Type} [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (O : Subring E)
    [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} O) X)).IsTriangulated := by
  obtain rfl : O = continuousIntegers ℓ E := by
    ext x
    rw [hO.out]
    change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
    simpa only [NNReal.coe_one, coe_nnnorm] using
      (NNReal.coe_le_coe : (‖x‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1)
  obtain ⟨hker, hcok, hext⟩ := integralConstructible_serre ℓ E X
  exact isTriangulated_boundedConstructible_of_serre _
    (fun M N f hM hN ↦ ⟨ObjectProperty.prop_kernel _ f hM hN,
      ObjectProperty.prop_cokernel _ f hM hN⟩)
    (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)


end AlgebraicGeometry.ProEtale
