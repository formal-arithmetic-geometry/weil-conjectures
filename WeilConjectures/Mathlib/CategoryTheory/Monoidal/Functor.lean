/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Transport of a lax monoidal structure along a natural isomorphism

If `F G : C ⥤ D` are functors between monoidal categories, `F` is lax monoidal and
`i : F ≅ G`, then `G` is lax monoidal (`CategoryTheory.Functor.LaxMonoidal.transport`),
with unit `ε F ≫ i.hom.app (𝟙_ C)` and tensorator
`(i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y)`.

This is the lax analogue of `CategoryTheory.Functor.Monoidal.transport`.

We also show that the property of being a monoidal adjunction is stable under replacing
the right adjoint along a monoidal natural isomorphism: if `adj : L ⊣ R` satisfies
`adj.IsMonoidal` and `e : R ≅ R'` is a natural isomorphism of lax monoidal functors with
`NatTrans.IsMonoidal e.hom`, then `(adj.ofNatIsoRight e).IsMonoidal`
(`CategoryTheory.Adjunction.isMonoidal_ofNatIsoRight`). This complements the existing
stability instances for `Adjunction.id` and `Adjunction.comp`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- Transport a lax monoidal structure along a natural isomorphism of functors. -/
@[implicit_reducible]
def transport {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) : G.LaxMonoidal where
  ε := ε F ≫ i.hom.app (𝟙_ C)
  μ X Y := (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y)
  μ_natural_left _ _ := by simp [NatTrans.whiskerRight_app_tensor_app_assoc]
  μ_natural_right _ _ := by simp [NatTrans.whiskerLeft_app_tensor_app_assoc]
  associativity X Y Z := by
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [tensorHom_def (i.inv.app (X ⊗ Y)) (i.inv.app Z),
      tensorHom_def' (i.inv.app X) (i.inv.app (Y ⊗ Z))]
    simp only [Category.assoc]
    rw [← comp_whiskerRight_assoc (i.hom.app (X ⊗ Y)) (i.inv.app (X ⊗ Y)),
      Iso.hom_inv_id_app, MonoidalCategory.id_whiskerRight, Category.id_comp,
      ← MonoidalCategory.whiskerLeft_comp_assoc (G.obj X) (i.hom.app (Y ⊗ Z))
        (i.inv.app (Y ⊗ Z)),
      Iso.hom_inv_id_app, MonoidalCategory.whiskerLeft_id, Category.id_comp,
      ← whisker_exchange_assoc (f := μ F X Y) (g := i.inv.app Z),
      whisker_exchange_assoc (f := i.inv.app X) (g := μ F Y Z),
      ← i.hom.naturality (α_ X Y Z).hom, associativity_assoc,
      ← tensorHom_def_assoc, ← tensorHom_def'_assoc, associator_naturality_assoc]
  left_unitality X := by
    simp only [comp_whiskerRight, Category.assoc]
    rw [tensorHom_def (i.inv.app (𝟙_ C)) (i.inv.app X)]
    simp only [Category.assoc]
    rw [← comp_whiskerRight_assoc (i.hom.app (𝟙_ C)) (i.inv.app (𝟙_ C)),
      Iso.hom_inv_id_app, MonoidalCategory.id_whiskerRight, Category.id_comp,
      ← whisker_exchange_assoc (f := ε F) (g := i.inv.app X),
      ← i.hom.naturality (λ_ X).hom, ← left_unitality_assoc,
      leftUnitor_naturality_assoc, Iso.inv_hom_id_app, Category.comp_id]
  right_unitality X := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [tensorHom_def' (i.inv.app X) (i.inv.app (𝟙_ C))]
    simp only [Category.assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc (G.obj X) (i.hom.app (𝟙_ C))
        (i.inv.app (𝟙_ C)),
      Iso.hom_inv_id_app, MonoidalCategory.whiskerLeft_id, Category.id_comp,
      whisker_exchange_assoc (f := i.inv.app X) (g := ε F),
      ← i.hom.naturality (ρ_ X).hom, ← right_unitality_assoc,
      rightUnitor_naturality_assoc, Iso.inv_hom_id_app, Category.comp_id]

@[reassoc]
lemma transport_ε {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) : letI := transport i
    ε G = ε F ≫ i.hom.app (𝟙_ C) :=
  rfl

@[reassoc]
lemma transport_μ {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) (X Y : C) : letI := transport i
    μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y) :=
  rfl

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]
  {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (e : R ≅ R')
  [L.OplaxMonoidal] [R.LaxMonoidal] [R'.LaxMonoidal] [adj.IsMonoidal]
  [NatTrans.IsMonoidal e.hom]

/-- The property of being a monoidal adjunction is stable under replacing the right adjoint
along a monoidal natural isomorphism. -/
instance isMonoidal_ofNatIsoRight : (adj.ofNatIsoRight e).IsMonoidal where
  leftAdjoint_ε := by
    simp only [ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.id_obj, Category.assoc]
    rw [← e.hom.naturality (η L), unit_app_unit_comp_map_η_assoc,
      NatTrans.IsMonoidal.unit (τ := e.hom)]
  leftAdjoint_μ X Y := by
    simp only [ofNatIsoRight_unit, ofNatIsoRight_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.id_obj,
      Category.assoc, ← tensorHom_comp_tensorHom]
    rw [δ_natural_assoc, ← e.hom.naturality, Functor.map_comp, Category.assoc,
      adj.unit_naturality_assoc, ← Category.assoc (adj.unit.app _),
      ← IsMonoidal.leftAdjoint_μ (adj := adj), NatTrans.IsMonoidal.tensor (τ := e.hom),
      tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app,
      tensorHom_id, id_whiskerRight, Category.id_comp]

end CategoryTheory.Adjunction
