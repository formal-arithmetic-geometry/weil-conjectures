/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category

/-!
# Transport of a lax monoidal structure, and the image of a tensor-inverse pair

`CategoryTheory.Functor.Monoidal.transport` transports a strong monoidal structure along a
natural isomorphism of functors. Here we do the same for lax monoidal structures.

We also record that a monoidal functor sends a pair of objects whose tensor product is the unit
to a pair of objects whose tensor product is the unit, and that it commutes with the tensor
powers of `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category`.

## Main definitions

- `CategoryTheory.Functor.LaxMonoidal.transport`: the lax monoidal structure on a functor
  that is isomorphic to a lax monoidal functor.
- `CategoryTheory.Functor.Monoidal.mapIsoTensorUnit`: the image under a monoidal functor of an
  isomorphism `L ⊗ N ≅ 𝟙_ C`.
- `CategoryTheory.Functor.Monoidal.mapTensorPowIso`: the image of a tensor power under a
  monoidal functor is the tensor power of the image.
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

namespace CategoryTheory.Functor.Monoidal

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- **A monoidal functor sends a tensor-inverse pair to a tensor-inverse pair.** If `L ⊗ N` is
isomorphic to the tensor unit of `C`, then `F.obj L ⊗ F.obj N` is isomorphic to the tensor unit
of `D`. -/
noncomputable def mapIsoTensorUnit (F : C ⥤ D) [F.Monoidal] {L N : C} (e : L ⊗ N ≅ 𝟙_ C) :
    F.obj L ⊗ F.obj N ≅ 𝟙_ D :=
  μIso F L N ≪≫ F.mapIso e ≪≫ (εIso F).symm

/-- **A monoidal functor commutes with tensor powers**: the image of `X ^⊗ n` is the `n`-th
tensor power of the image of `X`. -/
noncomputable def mapTensorPowIso (F : C ⥤ D) [F.Monoidal] (X : C) :
    ∀ n : ℕ, F.obj (X ^⊗ n) ≅ F.obj X ^⊗ n
  | 0 => (εIso F).symm
  | n + 1 => (μIso F (X ^⊗ n) X).symm ≪≫ tensorIso (mapTensorPowIso F X n) (Iso.refl _)

end CategoryTheory.Functor.Monoidal
