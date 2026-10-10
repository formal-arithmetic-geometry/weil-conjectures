/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal

/-!
# The unit comparison of `Qh : K(C) ⥤ D(C)`

The unit comparison `ε : 𝟙_ ⟶ Qh (𝟙_)` of the lax monoidal functor `Qh` is an isomorphism.

Stating this once for a general category `C` lets a concrete category (such as étale sheaves on a
scheme) use it as a plain application. Deriving it at a concrete category through
`inferInstanceAs` makes the kernel compare the two paths to the lax monoidal structure of `Qh`
there, which takes about a minute.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe w v u

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- The unit comparison `𝟙_ ⟶ Qh (𝟙_)` of `Qh : K(C) ⥤ D(C)` is an isomorphism. -/
theorem isIso_ε_Qh : IsIso (Functor.LaxMonoidal.ε (Qh (C := C))) :=
  inferInstanceAs (IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal Qh
    (HomotopyCategory.quasiIso C (.up ℤ)))))

end DerivedCategory

namespace CategoryTheory.DerivedMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]
  [L.HasDerivedMonoidalCategory W]

/-- The lax monoidal structure `L X ⊗ L 𝟙_ ⟶ L (X ⊗ 𝟙_)` of the localization functor to the
derived monoidal category is an isomorphism: it is the right unitor of `DerivedMonoidal L W`
followed by `L` of the inverse right unitor of `C`. -/
lemma isIso_μ_tensorUnit_right (X : C) :
    IsIso (Functor.LaxMonoidal.μ (toDerivedMonoidal L W) X (𝟙_ C)) := by
  have h : Functor.LaxMonoidal.μ (toDerivedMonoidal L W) X (𝟙_ C) =
      (rightUnitor L W).hom.app ((toDerivedMonoidal L W).obj X) ≫
        (toDerivedMonoidal L W).map (ρ_ X).inv := by
    rw [rightUnitor_hom_app, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Functor.map_id]
    exact (Category.comp_id _).symm
  rw [h]
  infer_instance

/-- The lax monoidal structure `L 𝟙_ ⊗ L X ⟶ L (𝟙_ ⊗ X)` of the localization functor to the
derived monoidal category is an isomorphism: it is the left unitor of `DerivedMonoidal L W`
followed by `L` of the inverse left unitor of `C`. -/
lemma isIso_μ_tensorUnit_left (X : C) :
    IsIso (Functor.LaxMonoidal.μ (toDerivedMonoidal L W) (𝟙_ C) X) := by
  have h : Functor.LaxMonoidal.μ (toDerivedMonoidal L W) (𝟙_ C) X =
      (leftUnitor L W).hom.app ((toDerivedMonoidal L W).obj X) ≫
        (toDerivedMonoidal L W).map (λ_ X).inv := by
    rw [leftUnitor_hom_app, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Functor.map_id]
    exact (Category.comp_id _).symm
  rw [h]
  infer_instance

end CategoryTheory.DerivedMonoidal

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- The lax monoidal structure `Qh K ⊗ Qh 𝟙_ ⟶ Qh (K ⊗ 𝟙_)` is an isomorphism. -/
theorem isIso_μ_Qh_tensorUnit_right (K : HomotopyCategory C (.up ℤ)) :
    IsIso (Functor.LaxMonoidal.μ (Qh (C := C)) K (𝟙_ _)) :=
  DerivedMonoidal.isIso_μ_tensorUnit_right Qh (HomotopyCategory.quasiIso C (.up ℤ)) K

/-- The lax monoidal structure `Qh 𝟙_ ⊗ Qh K ⟶ Qh (𝟙_ ⊗ K)` is an isomorphism. -/
theorem isIso_μ_Qh_tensorUnit_left (K : HomotopyCategory C (.up ℤ)) :
    IsIso (Functor.LaxMonoidal.μ (Qh (C := C)) (𝟙_ _) K) :=
  DerivedMonoidal.isIso_μ_tensorUnit_left Qh (HomotopyCategory.quasiIso C (.up ℤ)) K

end DerivedCategory
