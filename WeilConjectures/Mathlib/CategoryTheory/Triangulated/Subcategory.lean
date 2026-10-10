/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Functors induced between triangulated subcategories

For full subcategories `P` of `C` and `Q` of `D`, both stable under the shift, a functor
`F : C ⥤ D` commuting with the shifts and carrying `P` into `Q` induces a functor
`P.liftFullSubcategory Q F h` commuting with the shifts; it is triangulated if `F` is and `P`, `Q`
are triangulated subcategories.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C) (Q : ObjectProperty D)

section CommShift

variable {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [P.IsStableUnderShift A]
  [Q.IsStableUnderShift A] (F : C ⥤ D) [F.CommShift A] (h : ∀ X, P X → Q (F.obj X))

noncomputable instance commShiftLiftFullSubcategory :
    (P.liftFullSubcategory Q F h).CommShift A :=
  inferInstanceAs ((Q.lift (P.ι ⋙ F) fun X ↦ h X.obj X.property).CommShift A)

instance : NatTrans.CommShift (P.liftFullSubcategoryCompιIso Q F h).hom A :=
  inferInstanceAs (NatTrans.CommShift
    ((Q.liftCompιIso (P.ι ⋙ F) fun X ↦ h X.obj X.property).hom) A)

end CommShift

instance isTriangulated_liftFullSubcategory [HasZeroObject C] [HasZeroObject D] [Preadditive C]
    [Preadditive D] [HasShift C ℤ] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated C] [Pretriangulated D]
    [P.IsTriangulated] [Q.IsTriangulated] (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (h : ∀ X, P X → Q (F.obj X)) :
    (P.liftFullSubcategory Q F h).IsTriangulated :=
  inferInstanceAs ((Q.lift (P.ι ⋙ F) fun X ↦ h X.obj X.property).IsTriangulated)

section Lift

variable [HasZeroObject C] [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [P.IsTriangulated]

/-- A distinguished triangle of `C` whose vertices lie in a triangulated subcategory `P` is the
image of a distinguished triangle of `P`. -/
lemma exists_distTriang_ι_mapTriangle_iso (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : P T.obj₁) (h₂ : P T.obj₂) (h₃ : P T.obj₃) :
    ∃ T' : Triangle P.FullSubcategory, T' ∈ distTriang P.FullSubcategory ∧
      T'.obj₁.obj = T.obj₁ ∧ T'.obj₂.obj = T.obj₂ ∧ T'.obj₃.obj = T.obj₃ ∧
      Nonempty (P.ι.mapTriangle.obj T' ≅ T) := by
  let X₁ : P.FullSubcategory := ⟨T.obj₁, h₁⟩
  let X₂ : P.FullSubcategory := ⟨T.obj₂, h₂⟩
  let X₃ : P.FullSubcategory := ⟨T.obj₃, h₃⟩
  let T' : Triangle P.FullSubcategory := Triangle.mk (X := X₁) (Y := X₂) (Z := X₃)
    (P.fullyFaithfulι.preimage T.mor₁) (P.fullyFaithfulι.preimage T.mor₂)
    (P.fullyFaithfulι.preimage (T.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app X₁))
  let e : P.ι.mapTriangle.obj T' ≅ T := Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by dsimp; rw [Category.comp_id, Category.id_comp]; rfl)
    (by dsimp; rw [Category.comp_id, Category.id_comp]; rfl) (by
      change ((T.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app X₁) ≫
        (P.ι.commShiftIso (1 : ℤ)).hom.app X₁) ≫ (𝟙 T.obj₁)⟦(1 : ℤ)⟧' = 𝟙 _ ≫ T.mor₃
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
      erw [Functor.map_id, Category.comp_id, Category.id_comp])
  exact ⟨T', isomorphic_distinguished _ hT _ e, rfl, rfl, rfl, ⟨e⟩⟩

end Lift

end CategoryTheory.ObjectProperty
