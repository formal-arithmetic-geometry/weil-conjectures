/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.Triangulated.TExactTruncationComparison
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-! # Standard truncations on the ordinary bounded constructible derived category

Source: current blueprint prop-constructible-truncations. The categories here are full
subcategories of the ordinary derived categories of pulled-back condensed modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v uC vC uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

/-- The cohomology endofunctor specified by the proposition: truncate to degree i,
then shift by i. Its value is a degree-zero heart object.
Source: blueprint prop-constructible-truncations, cohomology display
(blueprint: prop-constructible-truncations). -/
def constructibleTruncationCohomology
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) (i : ℤ) : C ⥤ C :=
  (t.truncLE i ⋙ t.truncGE i) ⋙ shiftFunctor C i

/-- The compatibility clause, including the characterizing counit and unit equations.
Uniqueness fixes the comparisons and hence their coherence with scalar tower associators.
This is a package of the proposition's clauses, not a new truncation construction.
Source: blueprint prop-constructible-truncations, scalar and automorphism paragraphs
(blueprint: prop-constructible-truncations). -/
def ConstructibleTruncationCompatibility
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    (t : TStructure C) (s : TStructure B) (F : C ⥤ B) : Prop :=
  (∀ m : ℤ,
    (∃! α : t.truncLE m ⋙ F ≅ F ⋙ s.truncLE m,
      ∀ K : C, α.hom.app K ≫ (s.truncLEι m).app (F.obj K) =
        F.map ((t.truncLEι m).app K)) ∧
    (∃! α : t.truncGE m ⋙ F ≅ F ⋙ s.truncGE m,
      ∀ K : C, F.map ((t.truncGEπ m).app K) ≫ α.hom.app K =
        (s.truncGEπ m).app (F.obj K))) ∧
  ∀ i : ℤ, Nonempty (constructibleTruncationCohomology t i ⋙ F ≅
    F ⋙ constructibleTruncationCohomology s i)

private theorem compatibility_of_tExact
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
    (t : TStructure C) (s : TStructure B) (ht : ∀ K, t.bounded K)
    (hs : ∀ K, s.bounded K) (F : C ⥤ B)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t s] :
    ConstructibleTruncationCompatibility t s F := by
  have ht' : t.bounded = ⊤ := top_unique (fun K _ ↦ ht K)
  have hs' : s.bounded = ⊤ := top_unique (fun K _ ↦ hs K)
  constructor
  · intro m
    have h := t.texact_truncation_comparison.{uC, vC, uB, vB, uB, vB} s ht' hs' F m
    exact ⟨⟨F.eTruncLTIso t s (m + 1 : ℤ), fun K ↦ (h.1 K).1,
      fun a ha ↦ h.2.1 a ha⟩,
      ⟨F.eTruncGEIso t s m, fun K ↦ (h.1 K).2, fun a ha ↦ h.2.2.1 a ha⟩⟩
  · intro i
    exact ⟨Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (F.commShiftIso i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (F.eTruncGEIso t s i) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (F.eTruncLTIso t s (i + 1 : ℤ)) _ ≪≫
          Functor.associator _ _ _) _ ≪≫
      Functor.associator _ _ _⟩


end WeilConjectures

namespace AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

private theorem restricted_standard
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [ht : (DerivedCategory.TStructure.t.bounded ⊓
      DerivedCategory.homologyProperty P).IsTriangulated] :
    let Q := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
    ∃ ht : Q.IsTriangulated,
      letI := ht
      ∃ t : TStructure Q.FullSubcategory,
        (∀ (K : Q.FullSubcategory) (n : ℤ),
          t.IsLE K n ↔ DerivedCategory.TStructure.t.IsLE K.obj n) ∧
        (∀ (K : Q.FullSubcategory) (n : ℤ),
          t.IsGE K n ↔ DerivedCategory.TStructure.t.IsGE K.obj n) ∧
        (∀ K, t.bounded K) ∧
        (∀ K, t.heart K ↔ ∀ i : ℤ, i ≠ 0 →
          IsZero ((DerivedCategory.homologyFunctor A i).obj K.obj)) ∧
        Nonempty (t.Heart P.FullSubcategory) ∧
        (∀ n : ℤ,
          Nonempty (t.truncLE n ⋙ Q.ι ≅ Q.ι ⋙ DerivedCategory.TStructure.t.truncLE n) ∧
          Nonempty (t.truncGE n ⋙ Q.ι ≅ Q.ι ⋙ DerivedCategory.TStructure.t.truncGE n)) := by
  let Q := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
  have htr (K : DerivedCategory A) (hK : Q K) (n : ℤ) :
      Q ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      Q ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hK⟩ := hK
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
        DerivedCategory.homologyProperty_truncLE hK n⟩,
      ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
        DerivedCategory.homologyProperty_truncGE hK n⟩⟩
  have : Q.HasInducedTStructure DerivedCategory.TStructure.t :=
    ObjectProperty.HasInducedTStructure.mk' htr
  let t := Q.tStructure DerivedCategory.TStructure.t
  refine ⟨ht, t, fun K n ↦ Q.tStructure_isLE_iff _ K n,
    fun K n ↦ Q.tStructure_isGE_iff _ K n, ?_, ?_, ?_, ?_⟩
  · intro K
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
    exact ⟨⟨a, (Q.tStructure_isGE_iff _ K a).mpr ha⟩,
      ⟨b, (Q.tStructure_isLE_iff _ K b).mpr hb⟩⟩
  · intro K
    rw [t.mem_heart_iff, Q.tStructure_isLE_iff, Q.tStructure_isGE_iff]
    change K.obj.IsLE 0 ∧ K.obj.IsGE 0 ↔ _
    rw [DerivedCategory.isLE_iff, DerivedCategory.isGE_iff]
    constructor
    · rintro ⟨hle, hge⟩ i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact hge i hi
      · exact hle i hi
    · intro h
      exact ⟨fun i hi ↦ h i (by omega), fun i hi ↦ h i (by omega)⟩
  · have hS (M : P.FullSubcategory) : Q ((DerivedCategory.singleFunctor A 0).obj M.obj) := by
      refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
      intro i
      by_cases hi : i = 0
      · subst i
        exact P.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app
          M.obj).symm M.property
      · apply P.prop_of_isZero
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE _ 0 i hi
        · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    let S := Q.lift (P.ι ⋙ DerivedCategory.singleFunctor A 0) hS
    refine ⟨{ ι := S, essImage_eq_heart := ?_ }⟩
    ext K
    constructor
    · rintro ⟨M, ⟨e⟩⟩
      apply t.heart.prop_of_iso e
      rw [t.mem_heart_iff, Q.tStructure_isLE_iff, Q.tStructure_isGE_iff]
      constructor
      · change DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.singleFunctor A 0).obj M.obj) 0
        infer_instance
      · change DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.singleFunctor A 0).obj M.obj) 0
        infer_instance
    · intro hK
      obtain ⟨hle, hge⟩ := (t.mem_heart_iff K).mp hK
      have : K.obj.IsLE 0 := (Q.tStructure_isLE_iff _ K 0).mp hle
      have : K.obj.IsGE 0 := (Q.tStructure_isGE_iff _ K 0).mp hge
      obtain ⟨M, ⟨e⟩⟩ := K.obj.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
      have hM : P M := P.prop_of_iso
        ((DerivedCategory.homologyFunctor A 0).mapIso e ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app M) (K.property.2 0)
      exact ⟨⟨M, hM⟩, ⟨Q.isoMk e.symm⟩⟩
  · have : Q.ι.IsTExact t DerivedCategory.TStructure.t :=
      { isLE := fun K n h ↦ (Q.tStructure_isLE_iff _ K n).mp h
        isGE := fun K n h ↦ (Q.tStructure_isGE_iff _ K n).mp h }
    intro n
    exact ⟨⟨Q.ι.eTruncLTIso t _ (n + 1 : ℤ)⟩, ⟨Q.ι.eTruncGEIso t _ n⟩⟩

section Ordinary

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

/-- The standard bounded t-structure on the actual full constructible subcategory.
Its heart is the category of constructible module objects; the final comparisons identify
its truncations with the ambient canonical truncations, including their triangles.
Source: current blueprint prop-constructible-truncations, first paragraph
(blueprint: prop-constructible-truncations). -/
def OrdinaryConstructibleTruncations [(boundedConstructible R).IsTriangulated]
    (t : TStructure (BoundedConstructible R)) : Prop :=
  (∀ (K : BoundedConstructible R) (n : ℤ),
    t.IsLE K n ↔ DerivedCategory.TStructure.t.IsLE K.obj n) ∧
  (∀ (K : BoundedConstructible R) (n : ℤ),
    t.IsGE K n ↔ DerivedCategory.TStructure.t.IsGE K.obj n) ∧
  (∀ K, t.bounded K) ∧
  (∀ K, t.heart K ↔ ∀ i : ℤ, i ≠ 0 →
    IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj)) ∧
  Nonempty (t.Heart (ObjectProperty.FullSubcategory (IsConstructibleModuleObject R))) ∧
  (∀ n : ℤ,
    Nonempty (t.truncLE n ⋙ (boundedConstructible R).ι ≅
      (boundedConstructible R).ι ⋙ DerivedCategory.TStructure.t.truncLE n) ∧
    Nonempty (t.truncGE n ⋙ (boundedConstructible R).ι ≅
      (boundedConstructible R).ι ⋙ DerivedCategory.TStructure.t.truncGE n))

omit [IsCommMonObj R] in
private theorem constructible_zero_class :
    ObjectProperty.ContainsZero (IsConstructibleModuleObject R) := by
  obtain ⟨K, hK, hc⟩ := ObjectProperty.exists_prop_of_containsZero (boundedConstructible R)
  exact ⟨(DerivedCategory.homologyFunctor _ 0).obj K,
    (DerivedCategory.homologyFunctor _ 0).map_isZero hK, hc.2 0⟩

omit [IsCommMonObj R] in
private theorem ordinary_exists [(boundedConstructible R).IsTriangulated] :
    ∃ t : TStructure (BoundedConstructible R), OrdinaryConstructibleTruncations R t := by
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject R) := constructible_zero_class R
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e h ↦ h.of_iso e⟩
  have : (DerivedCategory.TStructure.t.bounded ⊓
      DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsTriangulated := by
    change (boundedConstructible R).IsTriangulated
    infer_instance
  obtain ⟨ht, t, h⟩ := restricted_standard (IsConstructibleModuleObject R)
  exact ⟨t, h⟩

omit [IsCommMonObj R] in
private theorem constructible_abelian
    (hk : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : M ⟶ N),
      IsConstructibleModuleObject R M → IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧
      IsConstructibleModuleObject R (cokernel f))
    (he : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
      IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    Nonempty (Abelian (ObjectProperty.FullSubcategory (IsConstructibleModuleObject R))) := by
  let P : ObjectProperty _ := IsConstructibleModuleObject R
  have : P.ContainsZero := constructible_zero_class R
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ h.of_iso e⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, h, hMN⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso h)
      (hk _ _ f hMN.1 hMN.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, h, hMN⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso h)
      (hk _ _ f hMN.1 hMN.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨he _⟩
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨D, hD⟩
    exact P.prop_of_iso ((biprod.isoProd _ _) ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair D)).symm)
      (P.prop_biprod (hD ⟨.left⟩) (hD ⟨.right⟩)))
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact ⟨inferInstance⟩

end Ordinary

/-- Standard truncations and bounded t-structures on the ordinary derived categories
of finite-extension and algebraic-closure condensed modules, with the abelian constructible
categories as hearts. Source: current blueprint prop-constructible-truncations, first paragraph
(blueprint: prop-constructible-truncations).

Proof: canonical truncations retain the original homology in their surviving degrees and
have zero homology elsewhere. Thus they preserve bounded constructibility and induce the
standard bounded t-structure. The fully faithful single functor identifies the heart with
constructible module objects. The field-coefficient Serre lemmas supply kernel, cokernel
and extension closure, giving the abelian full subcategory, also on the empty scheme. -/
theorem condensedConstructibleTruncations_exists
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (∃ t : TStructure (BoundedConstructible (padicSubfieldRingObj X ℓ E)),
        OrdinaryConstructibleTruncations _ t) ∧
      Nonempty (Abelian (ObjectProperty.FullSubcategory
        (IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E))))) ∧
    (∃ t : TStructure (BoundedConstructible (padicAlgClRingObj X ℓ)),
      OrdinaryConstructibleTruncations _ t) ∧
    Nonempty (Abelian (ObjectProperty.FullSubcategory
      (IsConstructibleModuleObject (padicAlgClRingObj X ℓ)))) := by
  constructor
  · intro E
    obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicSubfield X ℓ E
    exact ⟨ordinary_exists _, constructible_abelian _ hk he⟩
  · obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicAlgCl X ℓ
    exact ⟨ordinary_exists _, constructible_abelian _ hk he⟩

section Exchange

variable {X Y : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
  (S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
  [(boundedConstructible R).IsTriangulated] [(boundedConstructible S).IsTriangulated]

/-- The restriction of an ambient functor commutes with the standard truncations and
cohomology by the counit and unit characterizations. Source: current blueprint
prop-constructible-truncations, scalar and automorphism sentences
(blueprint: prop-constructible-truncations). -/
def OrdinaryConstructibleExchange
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)) : Prop :=
  ∃ hG : ∀ K : BoundedConstructible R, boundedConstructible S (G.obj K.obj),
    ∀ (t : TStructure (BoundedConstructible R)) (s : TStructure (BoundedConstructible S)),
      OrdinaryConstructibleTruncations R t → OrdinaryConstructibleTruncations S s →
      WeilConjectures.ConstructibleTruncationCompatibility t s
        ((boundedConstructible S).lift ((boundedConstructible R).ι ⋙ G) hG)

omit [IsCommMonObj R] [IsCommMonObj S] in
private theorem exchange_of_exact_iso
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S))
    (e : G ≅ F.mapDerivedCategory)
    (hG : ∀ K : BoundedConstructible R, boundedConstructible S (G.obj K.obj)) :
    OrdinaryConstructibleExchange R S G := by
  let : G.CommShift ℤ := Functor.CommShift.ofIso e.symm ℤ
  have : NatTrans.CommShift e.symm.hom ℤ := Functor.CommShift.ofIso_compatibility e.symm ℤ
  have : G.IsTriangulated := Functor.isTriangulated_of_iso e.symm
  refine ⟨hG, fun t s ht hs ↦ ?_⟩
  let H := (boundedConstructible S).lift ((boundedConstructible R).ι ⋙ G) hG
  have : H.IsTExact t s := by
    constructor
    · intro K n hK
      apply (hs.1 _ n).mpr
      have h : K.obj.IsLE n := (ht.1 _ n).mp hK
      have h' := F.isLE_mapDerivedCategory_obj K.obj n
      exact DerivedCategory.TStructure.t.isLE_of_iso (e.app K.obj).symm n
    · intro K n hK
      apply (hs.2.1 _ n).mpr
      have h : K.obj.IsGE n := (ht.2.1 _ n).mp hK
      have h' := F.isGE_mapDerivedCategory_obj K.obj n
      exact DerivedCategory.TStructure.t.isGE_of_iso (e.app K.obj).symm n
  exact WeilConjectures.compatibility_of_tExact t s ht.2.2.1 hs.2.2.1 H

end Exchange

/-- Finite scalar extension commutes with standard constructible truncations and cohomology.
Source: current blueprint prop-constructible-truncations, scalar-extension sentence
(blueprint: prop-constructible-truncations).

Proof: flatness makes extension exact, so its total left derived functor is the termwise
one. Exactness preserves both homological bounds, and the existing constructibility theorem
restricts the functor. The t-exact comparison gives the normalized isomorphisms. -/
theorem condensedConstructibleTruncations_scalar
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    OrdinaryConstructibleExchange (padicSubfieldRingObj X ℓ E)
      (padicSubfieldRingObj X ℓ F) (derivedExtendScalarsSubfield X ℓ h) := by
  exact exchange_of_exact_iso _ _
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) _
    (Functor.leftDerivedFunctorIsoMapDerivedCategory _)
    (boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h)

/-- Extension into the condensed algebraic closure commutes with standard constructible
truncations and cohomology. Source: current blueprint prop-constructible-truncations,
scalar-extension sentence (blueprint: prop-constructible-truncations).

Proof: the algebraic-closure flatness theorem makes extension exact. Its derived functor
is termwise extension, preserving both bounds and constructibility. Apply the t-exact
comparison to the restriction, and compose with the shift comparison for cohomology. -/
theorem condensedConstructibleTruncations_algCl
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    OrdinaryConstructibleExchange (padicSubfieldRingObj X ℓ E)
      (padicAlgClRingObj X ℓ) (derivedExtendScalarsToPadicAlgCl X ℓ E) := by
  exact exchange_of_exact_iso _ _
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)) _
    (Functor.leftDerivedFunctorIsoMapDerivedCategory _)
    (boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E)

/-- Actual derived pullback commutes with standard constructible truncations and cohomology.
Source: current blueprint prop-constructible-truncations, automorphism sentence
(blueprint: prop-constructible-truncations).

Proof: exact module pullback has its total left derived functor canonically isomorphic
to termwise pullback. Pulling back the stratification and finite-presentation covers
preserves constructibility; exactness preserves bounds. The restriction is t-exact. -/
theorem condensedConstructibleTruncations_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(boundedConstructible (condensedRingObj Λ X)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ Y)).IsTriangulated] :
    OrdinaryConstructibleExchange (condensedRingObj Λ Y) (condensedRingObj Λ X)
      (CondensedRing.upperStar Λ f).leftDerivedFunctor := by
  exact exchange_of_exact_iso _ _ (CondensedRing.upperStar Λ f) _
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f)
    (fun K ↦ CondensedRing.boundedConstructible_leftDerivedUpperStar_obj_of_scheme
      Λ f K.obj K.property)

private theorem ambient_cohomology_iso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (q : ℤ) :
    Nonempty (WeilConjectures.constructibleTruncationCohomology
        (DerivedCategory.TStructure.t (C := A)) q ≅
      DerivedCategory.homologyFunctor A q ⋙ DerivedCategory.singleFunctor A 0) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let Φ := t.truncLE q ⋙ t.truncGE q
  let S := DerivedCategory.singleFunctor A q
  have hΦ : ∀ X, S.essImage (Φ.obj X) := by
    intro X
    obtain ⟨M, ⟨e⟩⟩ :=
      DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (Φ.obj X) q
    exact ⟨M, ⟨e.symm⟩⟩
  let L := S.essImage.lift Φ hΦ
  let Φ' := L ⋙ S.toEssImage.inv
  let e₁ : Φ' ⋙ S ≅ Φ :=
    Functor.isoWhiskerLeft L (Functor.isoWhiskerLeft S.toEssImage.inv S.toEssImageCompι.symm ≪≫
      Functor.isoWhiskerRight S.toEssImage.asEquivalence.counitIso S.essImage.ι ≪≫
      Functor.leftUnitor _) ≪≫ S.essImage.liftCompιIso Φ hΦ
  let H := DerivedCategory.homologyFunctor A q
  let e₂ : Φ ⋙ H ≅ Φ' :=
    Functor.isoWhiskerRight e₁.symm _ ≪≫
      Functor.isoWhiskerLeft Φ' (DerivedCategory.singleFunctorCompHomologyFunctorIso A q) ≪≫
      Functor.rightUnitor _
  let α : t.truncLE q ⋙ H ⟶ H := Functor.whiskerRight (t.truncLEι q) H
  let β : t.truncLE q ⋙ H ⟶ Φ ⋙ H :=
    Functor.whiskerLeft (t.truncLE q) (Functor.whiskerRight (t.truncGEπ q) H)
  have (X : DerivedCategory A) : IsIso (α.app X) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app X (q + 1) q (by omega)
  have (X : DerivedCategory A) : IsIso (β.app X) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app _ q q le_rfl
  have : IsIso α := NatIso.isIso_of_isIso_app _
  have : IsIso β := NatIso.isIso_of_isIso_app _
  let e : Φ ≅ H ⋙ S :=
    e₁.symm ≪≫ Functor.isoWhiskerRight (e₂.symm ≪≫ (asIso β).symm ≪≫ asIso α) S
  exact ⟨Functor.isoWhiskerRight e (shiftFunctor _ q) ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft H ((DerivedCategory.singleFunctors A).shiftIso q 0 q (by omega))⟩

/-- The cohomology formula, naturally on the full ordinary constructible category:
truncate to degree `i`, then shift by `i`, to obtain the degree-zero complex of `H^i`.
Source: current blueprint prop-constructible-truncations, cohomology display
(blueprint: prop-constructible-truncations).

Proof: the t-exact inclusion compares the restricted and ambient truncations and commutes
with shift. The ambient double truncation has only degree-i cohomology. Full faithfulness
of the single functor and the degree-i isomorphisms of the truncation unit and counit
identify it naturally with the degree-i single complex of that cohomology. Shifting
by i moves the single complex to degree zero. -/
theorem condensedConstructibleTruncations_cohomology
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [(boundedConstructible R).IsTriangulated]
    (t : TStructure (BoundedConstructible R)) (ht : OrdinaryConstructibleTruncations R t)
    (i : ℤ) :
    Nonempty (WeilConjectures.constructibleTruncationCohomology t i ⋙
        (boundedConstructible R).ι ≅
      (boundedConstructible R).ι ⋙ DerivedCategory.homologyFunctor _ i ⋙
        DerivedCategory.singleFunctor _ 0) := by
  let J := (boundedConstructible R).ι
  let s := DerivedCategory.TStructure.t
    (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
  have : J.IsTExact t s :=
    { isLE := fun K n h ↦ (ht.1 K n).mp h
      isGE := fun K n h ↦ (ht.2.1 K n).mp h }
  let e : WeilConjectures.constructibleTruncationCohomology t i ⋙ J ≅
      J ⋙ WeilConjectures.constructibleTruncationCohomology s i :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (J.commShiftIso i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (J.eTruncGEIso t s i) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (J.eTruncLTIso t s (i + 1 : ℤ)) _ ≪≫
          Functor.associator _ _ _) _ ≪≫
      Functor.associator _ _ _
  exact ⟨e ≪≫ Functor.isoWhiskerLeft J (ambient_cohomology_iso
    (A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) i).some⟩

end AlgebraicGeometry.ProEtale
