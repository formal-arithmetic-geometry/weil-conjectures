/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-!
# The Koszul braiding of the derived category is symmetric

If `C` is a symmetric monoidal category, the Koszul braiding of cochain complexes
(`CochainComplex.Monoidal.braidedCategory`) is symmetric, since the signs `(-1)^(pq)` of the two
composed braidings cancel. Hence so are the braiding of the homotopy category
(`HomotopyCategory.braidedCategory`) and the braiding descended to the derived monoidal category
(`CategoryTheory.DerivedMonoidal.braidedCategory'`), in particular the braiding
`DerivedCategory.braidedCategory' C` of the derived tensor product on `DerivedCategory C`.

## Main definitions

- `CochainComplex.Monoidal.symmetricCategory`, `HomotopyCategory.symmetricCategory`,
  `CategoryTheory.DerivedMonoidal.symmetricCategory`, `DerivedCategory.symmetricCategory`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex.Monoidal

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C] [SymmetricCategory C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The Koszul braiding of cochain complexes over a symmetric category is symmetric. -/
lemma braiding_hom_braiding_hom (K L : CochainComplex C ℤ) :
    (braiding K L).hom ≫ (braiding L K).hom = 𝟙 _ := by
  ext n
  refine HomologicalComplex.mapBifunctor.hom_ext (fun p q hpq ↦ ?_)
  have h : p + q = n := hpq
  have h₁ := ι_braiding_hom (K := K) (L := L) p q n h
  have h₂ := ι_braiding_hom (K := L) (L := K) q p n (by rw [← h, add_comm])
  dsimp only [HomologicalComplex.ιTensorObj] at h₁ h₂
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  rw [reassoc_of% h₁]
  simp only [Preadditive.zsmul_comp, assoc, h₂, Preadditive.comp_zsmul, smul_smul,
    SymmetricCategory.symmetry_assoc]
  rw [mul_comm q p, ← Units.val_mul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul,
    Units.val_one, one_smul]
  exact (Category.comp_id _).symm

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- The Koszul braiding makes cochain complexes over a symmetric category a symmetric monoidal
category. -/
@[instance_reducible]
noncomputable def symmetricCategory : SymmetricCategory (CochainComplex C ℤ) where
  toBraidedCategory := braidedCategory
  symmetry K L := braiding_hom_braiding_hom K L

end CochainComplex.Monoidal

namespace HomotopyCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C] [SymmetricCategory C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The braiding of the homotopy category of cochain complexes over a symmetric category is
symmetric. -/
@[instance_reducible]
noncomputable def symmetricCategory : SymmetricCategory (HomotopyCategory C (.up ℤ)) where
  toBraidedCategory := braidedCategory
  symmetry X Y := by
    obtain ⟨X, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨Y, rfl⟩ := Y.quotient_obj_surjective
    change (quotient C _).map (CochainComplex.Monoidal.braiding X Y).hom ≫
      (quotient C _).map (CochainComplex.Monoidal.braiding Y X).hom = 𝟙 _
    rw [← Functor.map_comp, CochainComplex.Monoidal.braiding_hom_braiding_hom,
      CategoryTheory.Functor.map_id]

end HomotopyCategory

namespace CategoryTheory.DerivedMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [SymmetricCategory C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]
  [L.HasDerivedMonoidalCategory W]

/-- Over a symmetric category, the braiding of the derived monoidal category is symmetric: its
inverse is lifted from `β_ Y X⁻¹ = β_ X Y`. -/
lemma braiding_hom_braiding_hom (X Y : DerivedMonoidal L W) :
    (braiding' L W X Y).hom ≫ (braiding' L W Y X).hom = 𝟙 _ := by
  have h : braidingInvNatTrans L W = braidingNatTrans L W := by
    unfold braidingInvNatTrans braidingNatTrans
    congr 1
    unfold braidingInvCounit braidingCounit
    congr 2
    ext X Y
    exact (SymmetricCategory.braiding_swap_eq_inv_braiding X Y).symm
  have := (braiding' L W X Y).hom_inv_id
  simp only [braiding'] at this ⊢
  rwa [h] at this

variable [W.RespectsIso] [W.HasTwoOutOfThreeProperty]
  [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]

/-- Over a symmetric category, the derived monoidal category is symmetric. -/
@[instance_reducible]
noncomputable def symmetricCategory : SymmetricCategory (DerivedMonoidal L W) where
  toBraidedCategory := braidedCategory' L W
  symmetry X Y := braiding_hom_braiding_hom L W X Y

end CategoryTheory.DerivedMonoidal

namespace DerivedCategory

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local instance hasColimitsOfSize_symmetricCategory : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- The braiding `DerivedCategory.braidedCategory' C` of the derived tensor product over a
symmetric category is symmetric. -/
lemma braiding_hom_braiding_hom (X Y : DerivedCategory C) :
    letI := braidedCategory' C
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _ :=
  letI := HomotopyCategory.symmetricCategory (C := C)
  DerivedMonoidal.braiding_hom_braiding_hom Qh _ X Y

/-- The derived category of a symmetric monoidal closed Grothendieck abelian category with
functorial flat resolutions is symmetric for the Koszul braiding
`DerivedCategory.braidedCategory' C`. -/
@[instance_reducible]
noncomputable def symmetricCategory : SymmetricCategory (DerivedCategory C) where
  toBraidedCategory := braidedCategory' C
  symmetry X Y := braiding_hom_braiding_hom C X Y

end DerivedCategory
