/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The projection morphism of a monoidal adjunction

Given an adjunction `adj : F ⊣ G` between monoidal categories with `G` lax monoidal,
we define the projection morphism ("projection formula map")

`adj.projectionMap X Y : G.obj X ⊗ Y ⟶ G.obj (X ⊗ F.obj Y)`

and prove its naturality and coherence properties:

* `CategoryTheory.Adjunction.homEquiv_symm_projectionMap`: when moreover `F` is oplax monoidal
  and the adjunction is monoidal, the transpose of the projection morphism along the adjunction
  is `δ F (G.obj X) Y ≫ adj.counit.app X ▷ F.obj Y`;
* `CategoryTheory.Adjunction.projectionMap_unit`: compatibility with the right unitors;
* `CategoryTheory.Adjunction.projectionMap_assoc`: compatibility with the associators.

Instantiated at a pushforward/pullback adjunction between monoidal sheaf categories, the
projection morphism is the underived projection formula map `g_* M ⊗ N ⟶ g_* (M ⊗ g^* N)`
of the six-functor formalism.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

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
