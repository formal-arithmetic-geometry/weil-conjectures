/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData
import all Sheaf.CategoryTheory.ConstantModuleOrdinaryRealization
import all Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.CategoryTheory.ConstantModuleOrdinaryTensorSquare
import Sheaf.CategoryTheory.NormalizedExactTensorSquare
import Sheaf.CategoryTheory.ExactDerivedMonoidalConstruction

/-! # Descent of the constant-module tensor square

Source: Stacks Project, Cohomology on Sites, Tag 07A4,
and Derived Categories, Tags 0FPQ and 0FPT
(blueprint: lem-sfb-constant-module-tensor-square-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory CategoryTheory.ConstantScalarRestriction.fixedMonoidal
  CategoryTheory.ConstantScalarRestriction.fixedSymmetric
  CategoryTheory.ConstantScalarRestriction.restrictionBraided
  CategoryTheory.ConstantScalarRestriction.ordinary
attribute [-instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
namespace CategoryTheory.ConstantModuleDerivedProjection


section ComparisonNormalization
universe a b ha hb wa wb
variable {B : Type a} [Category.{ha} B] [Abelian B]
  [IsGrothendieckAbelian.{ha} B] [HasColimitsOfSize.{0, 0} B]
  [MonoidalCategory B] [MonoidalClosed B] [MonoidalPreadditive B] [BraidedCategory B]
  [Abelian.HasFunctorialFlatResolution B] [HasDerivedCategory.{wa} B]
  {E : Type b} [Category.{hb} E] [Abelian E]
  [IsGrothendieckAbelian.{hb} E] [HasColimitsOfSize.{0, 0} E]
  [MonoidalCategory E] [MonoidalClosed E] [MonoidalPreadditive E] [BraidedCategory E]
  [Abelian.HasFunctorialFlatResolution E] [HasDerivedCategory.{wb} E]

private theorem normalization_of_kflat_comparison
    (G : B ⥤ E) [G.Additive] [G.IsEquivalence]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesColimitsOfSize.{0, 0} G]
    (m : G.Monoidal) (n : G.mapDerivedCategory.Monoidal)
    (κ : CochainComplex B ℤ → Prop)
    (hκ : ∀ P, P.IsKFlatForTotalTensor → κ P)
    (h : letI := m; derivedTensorCompatibility B E G κ n) :
    TensorNormalization B E G m n := by
  letI := m
  intro P Q hP hQ
  exact h P Q (hκ P hP) (hκ Q hQ)

end ComparisonNormalization

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type (max u v)} [CommRing A]
private theorem ring_pull_preserves_flat (d : GeometricData J K A) :
    d.pullR.PreservesFlat := by
  constructor
  intro M hM
  have hf : SheafOfModules.IsFlatOnSite.{u, v, max u v, max u v} (R := ring J A) M :=
    (exactFunctor (Modules J A) (Modules J A)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (ring J A) M).symm hM.2
  have ht := SheafOfModules.isFlat_ringedToposPullback.{u, v, u, v, max u v, max u v}
    d.inverse d.direct d.geometric
    (SheafOfModules.inverseImageOfUniverses.{u, v, u, v, max u v} d.algebraic) d.scalarIso.hom M hf
  have hf' : SheafOfModules.IsFlatOnSite.{u, v, max u v, max u v}
      (R := ring K A) (d.pullR.obj M) := by
    rw [d.object_eq]
    exact ht
  have hright : exactFunctor _ _ (tensorRight (d.pullR.obj M)) :=
    (exactFunctor (Modules K A) (Modules K A)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (ring K A) (d.pullR.obj M)) hf'
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight (d.pullR.obj M)).symm hright, hright⟩

private theorem preserves_flat_square
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory F] [MonoidalCategory H]
    (S : B ⥤ E) [S.Monoidal] [S.IsEquivalence]
    (L : B ⥤ F) [L.PreservesFlat] (T : F ⥤ H) [T.PreservesFlat]
    (V : E ⥤ H) (e : L ⋙ T ≅ S ⋙ V) : V.PreservesFlat := by
  letI : S.asEquivalence.functor.Monoidal := inferInstanceAs S.Monoidal
  letI : S.inv.Monoidal := S.asEquivalence.inverseMonoidal
  letI : S.inv.PreservesFlat := S.inv.preservesFlat_of_isEquivalence
  constructor
  intro M hM
  have h := Functor.PreservesFlat.flat_obj (F := S.inv) hM
  have h' := Functor.PreservesFlat.flat_obj (F := L) h
  have h'' := Functor.PreservesFlat.flat_obj (F := T) h'
  exact ObjectProperty.prop_of_iso _
    (e.app (S.inv.obj M) ≪≫ V.mapIso (S.asEquivalence.counitIso.app M)) h''

private theorem fixed_pull_preserves_flat (d : GeometricData J K A)
    (o : OrdinaryIdentification d) : d.pullA.PreservesFlat := by
  letI := ring_pull_preserves_flat d
  letI := (restriction K A).preservesFlat_of_isEquivalence
  exact preserves_flat_square (restriction J A) d.pullR (restriction K A) d.pullA o.left

private theorem scalar_tensor_normalization
    [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Fixed J A)]
    (c : DerivedComparison.{u, v, w, w} J A) :
    TensorNormalization (Modules J A) (Fixed J A) (restriction J A)
      (restrictionBraided J A).toMonoidal c.val := by
  exact normalization_of_kflat_comparison (restriction J A)
    (restrictionBraided J A).toMonoidal c.val (fun P ↦ P.IsKFlatIndependentCoefficients)
    (fun P hP ↦ (kflat_iff J A P).2.1.mpr hP) c.property.1

variable [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Modules K A)]
  [HasDerivedCategory.{w} (Fixed J A)] [HasDerivedCategory.{w} (Fixed K A)]

/-- The normalized left comparison intertwines the canonical derived tensor maps.
Source: Stacks Tags 07A4, 0FPQ and 0FPT
(blueprint: lem-sfb-constant-module-tensor-square-descent).

Proof: use the canonical ringed pure-tensor comparison and the supplied fixed tensor
comparison. The scalar-restriction comparison sends the scalar-extension unit 1 tensor x
to the geometric inverse image of x. Thus both routes around the ordinary tensor square
send a generalized pure tensor x tensor y to the tensor of the two inverse images.
The universal property of the tensor and sheafification gives equality. On cochain
complexes the degree p,q summands carry this same equality; the signed differential
and the direct-sum total preserve it. Exact inverse image preserves flat objects and
K-flat complexes: tensoring after inverse image identifies with inverse image of the
tensor, and exactness preserves acyclicity. Construct the derived tensor comparisons
on flat-term K-flat representatives, using the total comparison and the exact-functor
localization factors. Resolving localization descends these comparisons uniquely and
transports associativity and the unit laws, giving the two strong monoidal structures.
Their defining representative equations are the two TensorNormalization clauses.
The prescribed left localization square and the normalized scalar-restriction tensors
identify the derived tensor square on K-flat representatives. Two-variable resolving
descent extends it to arbitrary unbounded objects. The construction uses the specified
ringed tensor comparison, so its ordinary tensorator is exactly ringTensor.mu. -/
theorem constant_module_tensor_square_descent (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (cJ : DerivedComparison.{u, v, w, w} J A)
    (cK : DerivedComparison.{u, v, w, w} K A)
    (i : d.pullR.mapDerivedCategory ⋙ onDerived K A ≅
      onDerived J A ⋙ d.pullA.mapDerivedCategory)
    (hi : LeftLocalizationSquare d x o i) :
    ∃ tensor : DerivedTensorIdentification d x t,
      TensorSquare d.pullR.mapDerivedCategory d.pullA.mapDerivedCategory
        (onDerived J A) (onDerived K A) tensor.val.1 tensor.val.2.2 cJ.val cK.val i := by
  letI := x
  letI := ring_pull_preserves_flat d
  letI := fixed_pull_preserves_flat d o
  letI := (restriction J A).preservesFlat_of_isEquivalence
  letI := (restriction K A).preservesFlat_of_isEquivalence
  obtain ⟨mR, hmR⟩ := ringMonoidal_exists d
  obtain ⟨nR, hnR⟩ := exact_monoidal_normalization d.pullR mR
  obtain ⟨nA, hnA⟩ := exact_monoidal_normalization d.pullA t.monoidal
  let tensor : DerivedTensorIdentification d x t :=
    ⟨⟨nR, mR, nA⟩, hmR, hnR, hnA⟩
  refine ⟨tensor, ?_⟩
  apply normalized_exact_tensor_square d.pullR d.pullA (restriction J A) (restriction K A)
    mR t.monoidal (restrictionBraided J A).toMonoidal (restrictionBraided K A).toMonoidal
    nR nA cJ.val cK.val o.left
    (constant_module_ordinary_tensor_square d o t mR hmR) hnR hnA
  · exact scalar_tensor_normalization cJ
  · exact scalar_tensor_normalization cK
  · exact hi

end CategoryTheory.ConstantModuleDerivedProjection
