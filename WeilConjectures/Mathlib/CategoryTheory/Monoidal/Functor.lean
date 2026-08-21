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

namespace CategoryTheory.Adjunction

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.LaxMonoidal]

/-- The projection morphism of an adjunction `adj : F ⊣ G` with `G` lax monoidal.
Instantiated at a pushforward/pullback adjunction between monoidal sheaf categories,
this is the underived projection formula map `g_* M ⊗ N ⟶ g_* (M ⊗ g^* N)`. -/
def projectionMap (X : D) (Y : C) : G.obj X ⊗ Y ⟶ G.obj (X ⊗ F.obj Y) :=
  (G.obj X ◁ adj.unit.app Y) ≫ μ G X (F.obj Y)

@[reassoc]
lemma projectionMap_natural_left {X X' : D} (f : X ⟶ X') (Y : C) :
    G.map f ▷ Y ≫ adj.projectionMap X' Y =
      adj.projectionMap X Y ≫ G.map (f ▷ F.obj Y) := by
  dsimp only [projectionMap]
  rw [← whisker_exchange_assoc]
  -- `erw` because the codomain of `adj.unit.app Y` is `(F ⋙ G).obj Y`, not `G.obj (F.obj Y)`
  erw [μ_natural_left]
  rw [assoc]

@[reassoc]
lemma projectionMap_natural_right (X : D) {Y Y' : C} (g : Y ⟶ Y') :
    G.obj X ◁ g ≫ adj.projectionMap X Y' =
      adj.projectionMap X Y ≫ G.map (X ◁ F.map g) := by
  dsimp only [projectionMap]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← adj.unit_naturality g,
    MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right, assoc]

section IsMonoidal

variable [F.OplaxMonoidal] [adj.IsMonoidal]

/-- The transpose of the projection morphism along the adjunction is the composite of the
oplax structure morphism of the left adjoint with the counit. This is the form in which the
projection morphism is usually accessed in computations. -/
@[reassoc]
lemma homEquiv_symm_projectionMap (X : D) (Y : C) :
    (adj.homEquiv _ _).symm (adj.projectionMap X Y) =
      δ F (G.obj X) Y ≫ adj.counit.app X ▷ F.obj Y := by
  dsimp only [projectionMap]
  rw [homEquiv_counit, Functor.map_comp, assoc, map_μ_comp_counit_app_tensor]
  erw [← δ_natural_right_assoc]
  rw [← id_tensorHom, tensorHom_comp_tensorHom, id_comp, left_triangle_components,
    tensorHom_id]

/-- The projection morphism is the transpose of
`δ F (G.obj X) Y ≫ adj.counit.app X ▷ F.obj Y` along the adjunction. -/
lemma projectionMap_eq_homEquiv (X : D) (Y : C) :
    adj.projectionMap X Y =
      adj.homEquiv _ _ (δ F (G.obj X) Y ≫ adj.counit.app X ▷ F.obj Y) :=
  (Equiv.symm_apply_eq _).mp (adj.homEquiv_symm_projectionMap X Y)

/-- Compatibility of the projection morphism with the unit objects: at `Y = 𝟙_ C` the
projection morphism degenerates to the right unitors. -/
@[reassoc]
lemma projectionMap_unit (X : D) :
    adj.projectionMap X (𝟙_ C) ≫ G.map (X ◁ η F) =
      (ρ_ (G.obj X)).hom ≫ G.map (ρ_ X).inv := by
  dsimp only [projectionMap]
  rw [assoc, ← μ_natural_right, ← MonoidalCategory.whiskerLeft_comp_assoc,
    adj.unit_app_unit_comp_map_η, ← right_unitality_inv, Iso.hom_inv_id_assoc]

/-- Compatibility of the projection morphism with the associators: projecting in two steps
agrees with projecting the tensor product in one step. -/
@[reassoc]
lemma projectionMap_assoc (X : D) (Y Y' : C) :
    adj.projectionMap X (Y ⊗ Y') ≫ G.map (X ◁ δ F Y Y') ≫
        G.map (α_ X (F.obj Y) (F.obj Y')).inv =
      (α_ (G.obj X) Y Y').inv ≫ adj.projectionMap X Y ▷ Y' ≫
        adj.projectionMap (X ⊗ F.obj Y) Y' := by
  dsimp only [projectionMap]
  rw [assoc, ← μ_natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    adj.unit_app_tensor_comp_map_δ Y Y', MonoidalCategory.whiskerLeft_comp_assoc,
    Functor.LaxMonoidal.associativity_inv, ← id_tensorHom]
  erw [associator_inv_naturality_assoc]
  rw [id_tensorHom, tensorHom_def, assoc]
  erw [whisker_exchange_assoc]
  rw [comp_whiskerRight, assoc]
  rfl

end IsMonoidal

end CategoryTheory.Adjunction
