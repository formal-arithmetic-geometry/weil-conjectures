/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Submission.WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
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
import Submission.WeilConjectures.ConstructibleSheaf.Defs
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
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
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
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all Submission.WeilConjectures.ConstructibleSheaf.OpenClosed
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
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

/-! # Shared proof API for finite coefficient descent

The private factorization, exact derived composition, and bounded constructibility
helpers formerly lived in the two-colimit and flat-coefficient proofs. They are kept
here so their earlier support-induction dependencies can reuse them without a cycle.
This module introduces no new mathematical obligation.
-/

@[expose] public section

universe u wC wD wE vC vD vE uC uD uE
open CategoryTheory Limits MonoidalCategory MonObj Abelian ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

section HomFactorization
set_option linter.unusedSectionVars false
universe v w uI vI
open CategoryTheory.Pretriangulated Preadditive
namespace CategoryTheory
variable {D : Type w} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {I : Type uI} [Category.{vI} I] [IsFiltered I] {N : I ⥤ D} (c : Cocone N)

private def factors (K : D) : Prop :=
  ∀ f : K ⟶ c.pt, ∃ (i : I) (g : K ⟶ N.obj i), f = g ≫ c.ι.app i
private lemma factors_iso {K L : D} (e : K ≅ L) (h : factors c K) : factors c L := by
  intro f
  obtain ⟨i, g, hg⟩ := h (e.hom ≫ f)
  refine ⟨i, e.inv ≫ g, ?_⟩
  rw [Category.assoc, ← hg]
  simp
private def shiftFactors : ObjectProperty D :=
  fun K ↦ ∀ n : ℤ, factors c (K⟦n⟧)

private lemma shiftFactors_of_hom_colimit
    {A : Type*} [Category A] {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (S : D)
    (h : ∀ n : ℤ, IsIso (colimit.desc _
      ((Q ⋙ shiftFunctor D n ⋙ preadditiveCoyoneda.obj (Opposite.op S)).mapCocone
        (colimit.cocone N)))) :
    shiftFactors (Q.mapCocone (colimit.cocone N)) S := by
  intro n f
  let F := Q ⋙ shiftFunctor D (-n) ⋙ preadditiveCoyoneda.obj (Opposite.op S)
  let t := F.mapCocone (colimit.cocone N)
  let p := colimit.desc (N ⋙ F) t
  have : IsIso p := h (-n)
  let adj := (shiftEquiv D n).toAdjunction
  let ff := adj.homEquiv S _ f
  let z := (inv p) ff
  obtain ⟨i, g, hg⟩ := Concrete.colimit_exists_rep (N ⋙ F) z
  have hfg : p ((colimit.ι (N ⋙ F) i) g) = ff := by
    rw [hg]
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id p) ff
  have he : g ≫ (Q.map (colimit.ι N i))⟦-n⟧' = ff := by
    change (colimit.ι (N ⋙ F) i ≫ p) g = ff at hfg
    rw [colimit.ι_desc] at hfg
    exact hfg
  refine ⟨i, (adj.homEquiv S _).symm g, ?_⟩
  apply (adj.homEquiv S _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact he.symm
private lemma factors_of_colimit_cocone
    {A : Type*} [Category A] {J : Type*} [Category J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (c : Cocone N) (hc : IsColimit c) (K : D)
    (h : factors (Q.mapCocone (colimit.cocone N)) K) : factors (Q.mapCocone c) K := by
  let e := (colimit.isColimit N).coconePointUniqueUpToIso hc
  have he (i : J) : colimit.ι N i ≫ e.hom = c.ι.app i :=
    (colimit.isColimit N).comp_coconePointUniqueUpToIso_hom hc i
  intro f
  obtain ⟨i, g, hg⟩ := h (f ≫ Q.map e.inv)
  change f ≫ Q.map e.inv = g ≫ Q.map (colimit.ι N i) at hg
  refine ⟨i, g, ?_⟩
  calc
    f = (f ≫ Q.map e.inv) ≫ Q.map e.hom := by simp
    _ = (g ≫ Q.map (colimit.ι N i)) ≫ Q.map e.hom := by rw [hg]
    _ = g ≫ Q.map (c.ι.app i) := by rw [Category.assoc, ← Q.map_comp, he]
end CategoryTheory
end HomFactorization
namespace CategoryTheory.Functor
section DerivedCompositionAPI
variable {C : Type uC} {D : Type uD} {E : Type uE}
  [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wE} E]
  {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
end DerivedCompositionAPI
section TransportAPI
variable {C D E : Type*} [Category C] [Category D] [Category E]
  {F F' : C ⥤ D} {G G' : D ⥤ E} {FG FG' : C ⥤ E}
end TransportAPI
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section LeftTransport
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

end LeftTransport
end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl
variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
  (ℓ : ℕ) [Fact ℓ.Prime]

-- Build the specific condensed-field triangulated structures from their Serre closure
-- statements; no arbitrary-coefficient closure assertion is used.
end AlgebraicGeometry.ProEtale
