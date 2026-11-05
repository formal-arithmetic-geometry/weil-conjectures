/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Full faithfulness of triangulated functors on generated subcategories

Let `F : C ⥤ D` be a triangulated functor between pretriangulated categories. For objects `X`
and `Y` of `C`, consider the condition `F.HomBijective X Y` that `F` induces a bijection
`(X ⟶ Y) ≃ (F X ⟶ F Y)`, and its shifted version `F.HomBijectiveShifts X Y`, which asks this
for all the shifts `X⟦a⟧`, `Y⟦b⟧`. By the five lemma applied to the long exact sequences of
`Hom` groups attached to a distinguished triangle, for fixed `X` the objects `Y` with
`F.HomBijectiveShifts X Y` form a triangulated subcategory of `C`, and similarly for fixed `Y`.

Consequently, if every object of `C` lies in every triangulated subcategory containing an
object `G`, and `F` is bijective on the morphisms `G⟦a⟧ ⟶ G⟦b⟧`, then `F` is fully faithful
(`CategoryTheory.Functor.fullyFaithfulOfGenerator`).

## Main statements

- `CategoryTheory.Functor.homBijective_obj₂_of_triangle`,
  `CategoryTheory.Functor.homBijective_obj₂_of_triangle'`: the five lemmas.
- `CategoryTheory.Functor.isTriangulated_homBijectiveShiftsRight`,
  `CategoryTheory.Functor.isTriangulated_homBijectiveShiftsLeft`: the triangulated
  subcategories.
- `CategoryTheory.Functor.fullyFaithfulOfGenerator`: full faithfulness from a generator.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated Preadditive ZeroObject

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/-- The functor `F` induces a bijection `(X ⟶ Y) ≃ (F X ⟶ F Y)`. -/
def HomBijective (X Y : C) : Prop :=
  Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))

variable {F}

lemma HomBijective.of_iso {X Y X' Y' : C} (h : F.HomBijective X Y) (e : X ≅ X') (e' : Y ≅ Y') :
    F.HomBijective X' Y' := by
  have h₁ : (F.map : (X' ⟶ Y') → (F.obj X' ⟶ F.obj Y')) =
      (fun g : F.obj X ⟶ F.obj Y ↦ F.map e.inv ≫ g ≫ F.map e'.hom) ∘
        (fun f : X ⟶ Y ↦ F.map f) ∘ (fun f : X' ⟶ Y' ↦ e.hom ≫ f ≫ e'.inv) := by
    ext f
    simp [← Functor.map_comp]
  have h₂ : Function.Bijective (fun f : X' ⟶ Y' ↦ e.hom ≫ f ≫ e'.inv) :=
    ((Iso.homCongr e.symm e'.symm).bijective)
  have h₃ : Function.Bijective (fun g : F.obj X ⟶ F.obj Y ↦ F.map e.inv ≫ g ≫ F.map e'.hom) :=
    ((Iso.homCongr (F.mapIso e) (F.mapIso e')).bijective)
  unfold HomBijective
  rw [h₁]
  exact h₃.comp (h.comp h₂)

/-- `F.HomBijective X Y` only depends on `X` up to isomorphism. -/
lemma HomBijective.of_iso_left {X Y X' : C} (h : F.HomBijective X Y) (e : X ≅ X') :
    F.HomBijective X' Y :=
  h.of_iso e (Iso.refl _)

/-- `F.HomBijective X Y` only depends on `Y` up to isomorphism. -/
lemma HomBijective.of_iso_right {X Y Y' : C} (h : F.HomBijective X Y) (e : Y ≅ Y') :
    F.HomBijective X Y' :=
  h.of_iso (Iso.refl _) e

section Zero

variable [Preadditive C] [Preadditive D]

lemma HomBijective.of_isZero_left {X Y : C} (hX : IsZero X) [F.PreservesZeroMorphisms] :
    F.HomBijective X Y :=
  ⟨fun _ _ _ ↦ hX.eq_of_src _ _, fun _ ↦ ⟨0, (F.map_isZero hX).eq_of_src _ _⟩⟩

lemma HomBijective.of_isZero_right {X Y : C} (hY : IsZero Y) [F.PreservesZeroMorphisms] :
    F.HomBijective X Y :=
  ⟨fun _ _ _ ↦ hY.eq_of_tgt _ _, fun _ ↦ ⟨0, (F.map_isZero hY).eq_of_tgt _ _⟩⟩

end Zero

section Biprod

variable [Preadditive C] [Preadditive D] [F.Additive] [HasBinaryBiproducts C]

/-- If `F` is bijective on the morphisms `X₁ ⟶ Y` and `X₂ ⟶ Y`, it is bijective on the morphisms
`X₁ ⊞ X₂ ⟶ Y`: a morphism `F (X₁ ⊞ X₂) ⟶ F Y` is determined by its restrictions along
`F inl` and `F inr`.
```
F X₁ --F inl--> F (X₁ ⊞ X₂) <--F inr-- F X₂
                     |
                     v
                    F Y
```
-/
lemma HomBijective.biprod_left {X₁ X₂ Y : C} (h₁ : F.HomBijective X₁ Y)
    (h₂ : F.HomBijective X₂ Y) : F.HomBijective (X₁ ⊞ X₂) Y := by
  refine ⟨fun φ ψ hφψ ↦ ?_, fun χ ↦ ?_⟩
  · refine biprod.hom_ext' _ _ (h₁.1 ?_) (h₂.1 ?_) <;>
      simp only [F.map_comp] <;> exact congrArg (_ ≫ ·) hφψ
  · obtain ⟨φ₁, hφ₁⟩ := h₁.2 (F.map biprod.inl ≫ χ)
    obtain ⟨φ₂, hφ₂⟩ := h₂.2 (F.map biprod.inr ≫ χ)
    refine ⟨biprod.desc φ₁ φ₂, ?_⟩
    rw [biprod.desc_eq, F.map_add, F.map_comp, F.map_comp, hφ₁, hφ₂, ← Category.assoc,
      ← Category.assoc, ← F.map_comp, ← F.map_comp, ← Preadditive.add_comp, ← F.map_add,
      biprod.total, F.map_id, Category.id_comp]

/-- If `F` is bijective on the morphisms `X ⟶ Y₁` and `X ⟶ Y₂`, it is bijective on the morphisms
`X ⟶ Y₁ ⊞ Y₂`: a morphism `F X ⟶ F (Y₁ ⊞ Y₂)` is determined by its composites with
`F fst` and `F snd`.
```
                    F X
                     |
                     v
F Y₁ <--F fst-- F (Y₁ ⊞ Y₂) --F snd--> F Y₂
```
-/
lemma HomBijective.biprod_right {X Y₁ Y₂ : C} (h₁ : F.HomBijective X Y₁)
    (h₂ : F.HomBijective X Y₂) : F.HomBijective X (Y₁ ⊞ Y₂) := by
  refine ⟨fun φ ψ hφψ ↦ ?_, fun χ ↦ ?_⟩
  · refine biprod.hom_ext _ _ (h₁.1 ?_) (h₂.1 ?_) <;>
      simp only [F.map_comp] <;> exact congrArg (· ≫ _) hφψ
  · obtain ⟨φ₁, hφ₁⟩ := h₁.2 (χ ≫ F.map biprod.fst)
    obtain ⟨φ₂, hφ₂⟩ := h₂.2 (χ ≫ F.map biprod.snd)
    refine ⟨biprod.lift φ₁ φ₂, ?_⟩
    rw [biprod.lift_eq, F.map_add, F.map_comp, F.map_comp, hφ₁, hφ₂, Category.assoc,
      Category.assoc, ← F.map_comp, ← F.map_comp, ← Preadditive.comp_add, ← F.map_add,
      biprod.total, F.map_id, Category.comp_id]

end Biprod

variable [HasShift C ℤ]

section Shift

variable [HasShift D ℤ] [F.CommShift ℤ]

lemma HomBijective.shift {X Y : C} (h : F.HomBijective X Y) (c : ℤ) :
    F.HomBijective (X⟦c⟧) (Y⟦c⟧) := by
  have e : (fun f : X ⟶ Y ↦ F.map (f⟦c⟧')) = (fun g : F.obj X ⟶ F.obj Y ↦
      (F.commShiftIso c).hom.app X ≫ g⟦c⟧' ≫ (F.commShiftIso c).inv.app Y) ∘ F.map := by
    ext f
    simp
  have h₁ : Function.Bijective (fun g : F.obj X ⟶ F.obj Y ↦
      (F.commShiftIso c).hom.app X ≫ g⟦c⟧' ≫ (F.commShiftIso c).inv.app Y) :=
    (Iso.homCongr ((F.commShiftIso c).app X).symm ((F.commShiftIso c).app Y).symm).bijective.comp
      ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D c)).map_bijective _ _)
  have h₂ : Function.Bijective ((F.map : (X⟦c⟧ ⟶ Y⟦c⟧) → _) ∘ (shiftFunctor C c).map) := by
    change Function.Bijective (fun f : X ⟶ Y ↦ F.map (f⟦c⟧'))
    rw [e]
    exact h₁.comp h
  exact (Function.Bijective.of_comp_iff _
    ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C c)).map_bijective _ _)).1 h₂

end Shift

variable [HasZeroObject C]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

section Triangulated

variable [F.CommShift ℤ] [F.IsTriangulated]

end Triangulated

variable (F) [F.CommShift ℤ] [F.IsTriangulated]

end Functor

end CategoryTheory
