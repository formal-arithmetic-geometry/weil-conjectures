/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Whiskering

/-!
# Complements on lax and oplax monoidal functors

`CategoryTheory.Functor.Monoidal.transport` transports a strong monoidal structure along a
natural isomorphism of functors. Here we do the same for lax monoidal structures.

## Main definitions

- `CategoryTheory.Functor.LaxMonoidal.transport`: the lax monoidal structure on a functor
  that is isomorphic to a lax monoidal functor.
- `CategoryTheory.Functor.OplaxMonoidal.δNatTrans`: the comonoidal structure of an oplax
  monoidal functor, as a natural transformation of bifunctors.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Transport a lax monoidal structure along a natural isomorphism of functors. -/
@[instance_reducible]
def transport {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) : G.LaxMonoidal where
  ε := ε F ≫ i.hom.app _
  μ X Y := (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y)
  μ_natural_left f X' := by
    simp only [Category.assoc, NatTrans.whiskerRight_app_tensor_app_assoc i.inv i.inv,
      μ_natural_left_assoc, ← i.hom.naturality]
  μ_natural_right X' f := by
    simp only [Category.assoc, NatTrans.whiskerLeft_app_tensor_app_assoc i.inv i.inv,
      μ_natural_right_assoc, ← i.hom.naturality]
  associativity X Y Z := by
    rw [comp_whiskerRight, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.whiskerLeft_comp, ← tensorHom_id (i.hom.app (X ⊗ Y)),
      ← id_tensorHom (G.obj X) (i.hom.app (Y ⊗ Z))]
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
      Category.id_comp]
    rw [id_tensorHom, tensorHom_id, ← whisker_exchange_assoc (μ F X Y) (i.inv.app Z),
      whisker_exchange_assoc (i.inv.app X) (μ F Y Z), ← tensorHom_def_assoc,
      whisker_exchange_assoc (i.inv.app X) (i.inv.app Y ⊗ₘ i.inv.app Z),
      ← tensorHom_def_assoc, ← i.hom.naturality, associativity_assoc,
      associator_naturality_assoc]
  left_unitality X := by
    rw [comp_whiskerRight, ← tensorHom_id (i.hom.app (𝟙_ C)), Category.assoc, Category.assoc,
      tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app, Category.id_comp, id_tensorHom,
      ← whisker_exchange_assoc, Category.assoc, ← i.hom.naturality, ← left_unitality_assoc]
    simp
  right_unitality X := by
    rw [MonoidalCategory.whiskerLeft_comp, ← id_tensorHom (G.obj X) (i.hom.app (𝟙_ C)),
      Category.assoc, Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
      Category.id_comp, tensorHom_id, whisker_exchange_assoc, Category.assoc, ← i.hom.naturality,
      ← right_unitality_assoc]
    simp

@[reassoc]
lemma transport_ε {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) :
    letI := transport i
    ε G = ε F ≫ i.hom.app (𝟙_ C) :=
  rfl

@[reassoc]
lemma transport_μ {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) (X Y : C) :
    letI := transport i
    μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y) :=
  rfl

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.Functor.OplaxMonoidal

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.OplaxMonoidal]

/-- The comonoidal structure `δ F X Y : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y` of an oplax
monoidal functor `F : C ⥤ D`, as a natural transformation between bifunctors `C ⥤ C ⥤ D`. -/
@[simps]
def δNatTrans :
    (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) where
  app X₁ := { app X₂ := δ F X₁ X₂ }

end CategoryTheory.Functor.OplaxMonoidal
