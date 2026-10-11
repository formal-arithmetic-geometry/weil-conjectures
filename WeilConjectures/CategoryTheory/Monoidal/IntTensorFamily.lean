/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.TensorInverse
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Coherent integer families of objects in a monoidal category

A *coherent integer family* in a monoidal category `C`
(`CategoryTheory.MonoidalCategory.IntTensorFamily`) is a family of objects `P m`, `m ∈ ℤ`, with
identifications `P 0 ≅ 𝟙` and `P a ⊗ P b ≅ P (a + b)` satisfying the unit and associativity
laws; equivalently, a strong monoidal functor out of the discrete monoidal category `ℤ`. The
integer tensor powers of an object with a tensor inverse form one
(`CategoryTheory.MonoidalCategory.TensorInverse.intTensorFamily`), and a functor whose oplax
monoidal structure is invertible carries coherent families to coherent families
(`CategoryTheory.MonoidalCategory.IntTensorFamily.map`). A monoidal isomorphism `H ≅ A ⋙ B`
between such functors is compatible with the transported families
(`CategoryTheory.MonoidalCategory.IntTensorFamily.map_addIso_comp`).
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.MonoidalCategory

open Category Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- A coherent integer family of objects in a monoidal category: objects `P m` for `m ∈ ℤ`, with
`P 0 ≅ 𝟙` and `P a ⊗ P b ≅ P (a + b)`, subject to the unit and associativity laws. -/
structure IntTensorFamily (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] where
  /-- The objects. -/
  obj : ℤ → C
  /-- `P 0 ≅ 𝟙`. -/
  zeroIso : obj 0 ≅ 𝟙_ C
  /-- `P a ⊗ P b ≅ P (a + b)`. -/
  addIso (a b : ℤ) : obj a ⊗ obj b ≅ obj (a + b)
  zero_left (m : ℤ) : zeroIso.hom ▷ obj m ≫ (λ_ (obj m)).hom =
    (addIso 0 m).hom ≫ eqToHom (by rw [zero_add])
  zero_right (m : ℤ) : obj m ◁ zeroIso.hom ≫ (ρ_ (obj m)).hom =
    (addIso m 0).hom ≫ eqToHom (by rw [add_zero])
  assoc (a b c : ℤ) : (addIso a b).hom ▷ obj c ≫ (addIso (a + b) c).hom =
    (α_ (obj a) (obj b) (obj c)).hom ≫ obj a ◁ (addIso b c).hom ≫ (addIso a (b + c)).hom ≫
      eqToHom (by rw [add_assoc])

namespace TensorInverse

variable {L : C} (e : TensorInverse L)

/-- The integer tensor powers of an object with a tensor inverse form a coherent family. -/
noncomputable def intTensorFamily : IntTensorFamily C where
  obj := e.zpow
  zeroIso := Iso.refl _
  addIso a b := e.addIso a b (a + b) rfl
  zero_left m := by
    rw [e.addIso_zero_left]
    simp
  zero_right m := by
    rw [e.addIso_zero_right]
    simp
  assoc a b c := by
    rw [e.addIso_assoc a b c (a + b) (b + c) (a + b + c) rfl rfl rfl (by rw [add_assoc]),
      e.addIso_hom_eqToHom]
    rw [add_assoc]

end TensorInverse

namespace IntTensorFamily

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

variable (P : IntTensorFamily C)

/-- The image of a coherent family under a functor whose oplax monoidal structure maps are
isomorphisms. -/
noncomputable def map (F : C ⥤ D) [F.OplaxMonoidal] [IsIso (η F)]
    [∀ X Y, IsIso (δ F X Y)] : IntTensorFamily D where
  obj m := F.obj (P.obj m)
  zeroIso := F.mapIso P.zeroIso ≪≫ asIso (η F)
  addIso a b := (asIso (δ F _ _)).symm ≪≫ F.mapIso (P.addIso a b)
  zero_left m := by
    have h := P.zero_left m
    have hl := left_unitality_hom F (P.obj m)
    rw [← cancel_epi (δ F _ _)]
    simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, comp_whiskerRight, Category.assoc,
      Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
    rw [δ_natural_left_assoc, hl, ← F.map_comp, h, F.map_comp, eqToHom_map]
  zero_right m := by
    have h := P.zero_right m
    have hr := right_unitality_hom F (P.obj m)
    rw [← cancel_epi (δ F _ _)]
    simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
    rw [δ_natural_right_assoc, hr, ← F.map_comp, h, F.map_comp, eqToHom_map]
  assoc a b c := by
    have h := P.assoc a b c
    have ha := associativity F (P.obj a) (P.obj b) (P.obj c)
    rw [← cancel_epi (δ F (P.obj a ⊗ P.obj b) (P.obj c) ≫
      δ F (P.obj a) (P.obj b) ▷ F.obj (P.obj c))]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom, comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← comp_whiskerRight_assoc (δ F _ _) (inv _), IsIso.hom_inv_id, id_whiskerRight,
      Category.id_comp, δ_natural_left_assoc, IsIso.hom_inv_id_assoc, ← F.map_comp, h,
      reassoc_of% ha, ← MonoidalCategory.whiskerLeft_comp_assoc,
      IsIso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp,
      δ_natural_right_assoc, IsIso.hom_inv_id_assoc]
    simp only [Functor.map_comp, eqToHom_map]

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- An isomorphism `c : H ≅ A ⋙ B` of functors with invertible oplax monoidal structures which is
compatible with the comonoidal structures is compatible with the images of a coherent family:
```
B(A(P a) ⊗ A(P b)) ───B(addIso)───▶ B(A(P (a + b))) ───c⁻¹───▶ H(P (a + b))
        │                                                          ‖
        δ                                                          ‖
        ▼                                                          ‖
B(A(P a)) ⊗ B(A(P b)) ──c⁻¹ ⊗ c⁻¹──▶ H(P a) ⊗ H(P b) ──addIso──▶ H(P (a + b))
``` -/
lemma map_addIso_comp (A : C ⥤ D) (B : D ⥤ E) (H : C ⥤ E) [A.OplaxMonoidal] [B.OplaxMonoidal]
    [H.OplaxMonoidal] [IsIso (η A)] [IsIso (η B)] [IsIso (η H)] [∀ X Y, IsIso (δ A X Y)]
    [∀ X Y, IsIso (δ B X Y)] [∀ X Y, IsIso (δ H X Y)] (c : H ≅ A ⋙ B)
    (hc : ∀ X Y, δ H X Y ≫ (c.hom.app X ⊗ₘ c.hom.app Y) =
      c.hom.app (X ⊗ Y) ≫ B.map (δ A X Y) ≫ δ B _ _) (a b : ℤ) :
    B.map ((P.map A).addIso a b).hom ≫ c.inv.app (P.obj (a + b)) =
      δ B _ _ ≫ (c.inv.app (P.obj a) ⊗ₘ c.inv.app (P.obj b)) ≫ ((P.map H).addIso a b).hom := by
  have hn := c.inv.naturality (P.addIso a b).hom
  dsimp at hn
  have h' : B.map (inv (δ A (P.obj a) (P.obj b))) ≫ c.inv.app (P.obj a ⊗ P.obj b) =
      δ B _ _ ≫ (c.inv.app (P.obj a) ⊗ₘ c.inv.app (P.obj b)) ≫ inv (δ H _ _) := by
    rw [← cancel_mono (δ H _ _), Category.assoc, Category.assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, ← cancel_epi (B.map (δ A (P.obj a) (P.obj b))),
      ← B.map_comp_assoc, IsIso.hom_inv_id, B.map_id, Category.id_comp,
      ← cancel_mono (c.hom.app (P.obj a) ⊗ₘ c.hom.app (P.obj b)), Category.assoc, hc,
      Iso.inv_hom_id_app_assoc, Category.assoc, Category.assoc, tensorHom_comp_tensorHom,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    simp
  simp only [map, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom, B.map_comp,
    Category.assoc]
  rw [hn, reassoc_of% h']

end IntTensorFamily

end CategoryTheory.MonoidalCategory
