/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LfpTensorSingleSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
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
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Submission.WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all Submission.WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all Submission.WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all Submission.WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
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
import all Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
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
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorSingle

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # BoundedConstructibleTensorSingle

The remaining local tensor calculation on constructible sheaves in degree zero.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] {k : Type u} [Field k]
variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

variable {X}

namespace ContinuousMapRingObj

end ContinuousMapRingObj

namespace PadicIntegersRingObj

end PadicIntegersRingObj

namespace UnitBallRingObj

/-- The tensor calculation for two constructible sheaves in degree zero, `O̲` coefficients for
`O` the closed unit ball of a finite normed extension `E` of `ℚ_ℓ`.
(blueprint: lem-sfb-dc-tensor-single) -/
theorem boundedConstructible_tensor_single
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] {E : Type} [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) [Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj O) X.left)
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G) :=
  boundedConstructible_tensor_single_of_lfp _ X
    (fun Y _ F G hF hG ↦ UnitBallRingObj.lfp_tensor_single Y ℓ O F G hF hG) F G hF hG

end UnitBallRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
