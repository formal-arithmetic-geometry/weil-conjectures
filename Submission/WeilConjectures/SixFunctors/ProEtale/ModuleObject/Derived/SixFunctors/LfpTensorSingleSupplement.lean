/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.NoetherianSpace

import Submission.WeilConjectures.AlgebraicGeometry.LocallyFreeTensorSingle
import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import Submission.WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Submission.WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Sites.EpiMono
import Submission.WeilConjectures.ConstructibleSheaf.Refinement
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
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
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import Submission.WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
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
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import Submission.WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import Submission.WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
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
import all Submission.WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all Mathlib.Data.Fin.Tuple.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all Submission.WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all Submission.WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import Submission.WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Grp.Adjunctions
import Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import Submission.WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Constructible

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Local tensor calculations over ell-adic coefficients

Source: Bhatt--Scholze, Proposition 6.8.11(3), using locally finite free resolutions.
(blueprint: lem-sfb-lfp-tensor-single)
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj ZeroObject
open CategoryTheory Limits MonoidalCategory MonObj Opposite Pretriangulated
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory.TStructure.t

private lemma locallyFinitelyPresented_of_isZero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (hM : IsZero M) :
    IsLocallyFinitelyPresented R M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, 0, 𝟙 _, ⟨?_⟩⟩
  exact (((ProEtale.upperStar Ab.{u + 1} _).mapMod R).map_isZero hM).iso
    (isZero_cokernel_of_epi (𝟙 _))

private theorem integral_tensor_single
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (hF : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) F)
    (hG : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
          (DerivedCategory.singleFunctor _ 0).obj G)) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :=
    IsLocallyFinitelyPresented R
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ localFinitePresentation_of_iso e h⟩
  have : P.ContainsZero :=
    ⟨0, isZero_zero _, locallyFinitelyPresented_of_isZero R (isZero_zero _)⟩
  have hpivot : IntegralMatrixPivots.{u} ℓ E := integralMatrix_pivot_cover ℓ E
  have hmatrix : IntegralMatrixKernels.{u} ℓ E := integralMatrixKernels_of_pivots ℓ E hpivot
  have hrational : RationalMatrixKernels.{u} ℓ E :=
    rationalMatrixKernels_of_integral ℓ E hmatrix
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, c, hc, hf⟩
    apply localFinitePresentation_of_iso (limit.isoLimitCone ⟨c, hc⟩)
    exact integral_lfp_kernel_of_rational ℓ E hrational X f hf.1 hf.2⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, c, hc, hf⟩
    exact localFinitePresentation_of_iso (colimit.isoColimitCocone ⟨c, hc⟩)
      (lfp_cokernel f hf.1 hf.2)⟩
  have : P.IsClosedUnderExtensions := ⟨fun hs h₁ h₃ ↦ lfp_extension _ hs h₁ h₃⟩
  let Q := DerivedCategory.homologyProperty P
  have : Q.IsTriangulated := inferInstance
  obtain ⟨F₁, F₀, f, g, w, hs, h₁, h₀⟩ := integral_lfp_locallyFree_resolution X ℓ E F hF
  let T := (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)).mapTriangle.obj
    hs.singleTriangle
  have hT : T ∈ distTriang _ :=
    (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)).map_distinguished _
      hs.singleTriangle_distinguished
  have h₁' : DerivedCategory.TStructure.t.IsGE T.obj₁ 0 :=
    (locallyFree_tensor_single (integralCoeff ℓ E) X F₁ G h₁ hG).1
  have h₀' : DerivedCategory.TStructure.t.IsGE T.obj₂ 0 :=
    (locallyFree_tensor_single (integralCoeff ℓ E) X F₀ G h₀ hG).1
  constructor
  · change DerivedCategory.TStructure.t.IsGE T.obj₃ (-1)
    have hb : DerivedCategory.TStructure.t.IsGE T.obj₂ (-1) :=
      DerivedCategory.TStructure.t.isGE_of_ge T.obj₂ (-1) 0 (by decide)
    have ha : DerivedCategory.TStructure.t.IsGE (T.obj₁⟦(1 : ℤ)⟧) (-1) :=
      DerivedCategory.TStructure.t.isGE_shift T.obj₁ 0 1 (-1) (by decide)
    exact DerivedCategory.TStructure.t.isGE₂ T.rotate
      (rot_of_distTriang _ hT) (-1) hb ha
  · change Q T.obj₃
    exact Q.ext_of_isTriangulatedClosed₃ T hT
      (locallyFree_tensor_single (integralCoeff ℓ E) X F₁ G h₁ hG).2
      (locallyFree_tensor_single (integralCoeff ℓ E) X F₀ G h₀ hG).2

variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

/-- The field case of `lfp_tensor_single` for `E̲`, `E` a finite normed extension of `ℚ_ℓ`. -/
private theorem continuous_tensor_single
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hF : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X) F)
    (hG : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G)) := by
  have hfree : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod _).obj F) := by
    let E' := ULift.{u} E
    let : NormedField E' :=
      { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
        norm_mul a b := norm_mul a.down b.down }
    have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
      Sheaf.isCommMonObj_sheafCompose_obj
        (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
        (by
          intro S a b
          apply ULift.ext
          change (a.down * b.down : C(S.unop, E')) = b.down * a.down
          exact mul_comm a.down b.down)
    let e := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
    let φ := (upperStarFromPoint X).map e.hom
    have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map
      (coherentTopology Profinite.{u}) (liftCoefficientIso E).hom
    have : IsMonHom φ := inferInstance
    have hf := exists_finiteFree_cover_of_condensedField_lfp ℓ E' X
      ((Mod.comap (inv φ)).obj F) (lfp_comap (inv φ) hF)
    exact locally_free_of_iso (locally_free_comap φ hf)
      ((Mod.comapEquivalenceOfIsIso φ).counitIso.app F)
  obtain ⟨hb, hl⟩ := locallyFree_tensor_single _ X F G hfree hG
  have := hb
  exact ⟨DerivedCategory.TStructure.t.isGE_of_ge _ (-1) 0 (by decide), hl⟩

/-- The tensor of two locally finitely presented ell-adic module sheaves has
no cohomology below degree -1, and its cohomology is locally finitely presented.
Source: Bhatt--Scholze, Proposition 6.8.11(3), expanded using the library's
integral locally finite free resolution.
Proof: in the field cases local triviality makes the first factor locally finite free,
so the finite free tensor calculation gives the assertion (and a stronger lower bound 0).
For integral coefficients take the short exact two-term locally finite free resolution
of the first factor, and tensor its distinguished triangle with the second factor.
Both resolved terms have cohomology in degree zero and locally finite presentation.
The rotated triangle gives the lower bound -1. The upper bound 0 is the general
right t-exactness of derived tensor. Locally finitely presented integral module sheaves
are closed under kernels, cokernels and extensions; hence their homology property is
triangulated and the third term has locally finitely presented cohomology.
(blueprint: lem-sfb-lfp-tensor-single) -/
theorem lfp_tensor_single (ℓ : ℕ) [Fact ℓ.Prime]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hF : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) F)
    (hG : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G)) := by
  obtain ⟨hb, hl⟩ := locallyFree_tensor_single _ X F G (algcl_lf ℓ X F hF) hG
  have := hb
  exact ⟨DerivedCategory.TStructure.t.isGE_of_ge _ (-1) 0 (by decide), hl⟩

namespace ContinuousMapRingObj

/-- `lfp_tensor_single` for `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`.
(blueprint: lem-sfb-lfp-tensor-single) -/
theorem lfp_tensor_single (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hF : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X) F)
    (hG : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G)) := by
  exact continuous_tensor_single X ℓ E F G hF hG

end ContinuousMapRingObj

namespace PadicIntegersRingObj

/-- `lfp_tensor_single` for `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`.
(blueprint: lem-sfb-lfp-tensor-single) -/
theorem lfp_tensor_single (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    (hF : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) F)
    (hG : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact integral_tensor_single ℓ E X F G hF hG

end PadicIntegersRingObj

namespace UnitBallRingObj

/-- `lfp_tensor_single` for `O̲`, `O` the closed unit ball of a finite normed extension `E`
of `ℚ_ℓ`. (blueprint: lem-sfb-lfp-tensor-single) -/
theorem lfp_tensor_single (ℓ : ℕ) [Fact ℓ.Prime] {E : Type} [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj O) X))
    (hF : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj O) X) F)
    (hG : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj O) X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj O) X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G)) := by
  have hO := hO.out
  have he : O = continuousIntegers ℓ E := by
    ext x
    rw [hO]
    change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
    simpa only [NNReal.coe_one, coe_nnnorm] using
      (NNReal.coe_le_coe : (‖x‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1)
  subst O
  exact integral_tensor_single ℓ E X F G hF hG

end UnitBallRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
