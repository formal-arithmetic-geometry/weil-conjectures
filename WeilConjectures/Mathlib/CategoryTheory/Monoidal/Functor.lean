/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

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

When moreover `F` is strong monoidal, the projection morphism is an isomorphism at every
object `Y` with a left dual (`CategoryTheory.Adjunction.projectionMapIso` and the instance
`CategoryTheory.Adjunction.isIso_projectionMap`): this is the "projection formula for
dualizable coefficients". The inverse is obtained by bending the `Y`-strand with the
coevaluation of `ᘁY` and evaluating `F.obj Y` against `F.obj (ᘁY)` inside `G`, using that
a strong monoidal functor preserves exact pairings (`CategoryTheory.ExactPairing.map`).

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

section Dualizable

variable [F.Monoidal] [adj.IsMonoidal]

/-- Projecting in twice and evaluating upstairs is evaluation downstairs: composing the
projection morphisms at `Y` and at `ᘁY` with the image under `G` of the evaluation of the
pairing of `F.obj (ᘁY)` with `F.obj Y` recovers the evaluation of the pairing of `ᘁY` with
`Y`. This is the key computation showing that the projection morphism is an isomorphism at
dualizable objects. -/
@[reassoc]
lemma projectionMap_evaluation (X : D) (Y : C) [HasLeftDual Y] :
    adj.projectionMap X Y ▷ (ᘁY) ≫ adj.projectionMap (X ⊗ F.obj Y) (ᘁY) ≫
      G.map ((α_ X (F.obj Y) (F.obj (ᘁY))).hom ≫
        X ◁ (μ F Y (ᘁY) ≫ F.map (ε_ (ᘁY) Y) ≫ η F) ≫ (ρ_ X).hom) =
      (α_ (G.obj X) Y (ᘁY)).hom ≫ G.obj X ◁ ε_ (ᘁY) Y ≫ (ρ_ (G.obj X)).hom := by
  have h : adj.projectionMap X Y ▷ (ᘁY) ≫ adj.projectionMap (X ⊗ F.obj Y) (ᘁY) =
      (α_ (G.obj X) Y (ᘁY)).hom ≫ adj.projectionMap X (Y ⊗ ᘁY) ≫
        G.map (X ◁ δ F Y (ᘁY)) ≫ G.map (α_ X (F.obj Y) (F.obj (ᘁY))).inv := by
    rw [adj.projectionMap_assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [Functor.Monoidal.whiskerLeft_δ_μ_assoc, Functor.map_comp, Functor.map_comp,
    ← adj.projectionMap_natural_right_assoc, adj.projectionMap_unit_assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]

/-- The projection morphism of a monoidal adjunction whose left adjoint is strong monoidal
is an isomorphism at every object `Y` admitting a left dual: the "projection formula for
dualizable coefficients". The inverse is obtained by bending the `Y`-strand with the
coevaluation of the pairing of `ᘁY` with `Y` and evaluating `F.obj Y` against
`F.obj (ᘁY)` inside `G`. -/
@[simps hom]
noncomputable def projectionMapIso (X : D) (Y : C) [HasLeftDual Y] :
    G.obj X ⊗ Y ≅ G.obj (X ⊗ F.obj Y) where
  hom := adj.projectionMap X Y
  inv := tensorRightHomEquiv _ (ᘁY) Y _
    (adj.projectionMap (X ⊗ F.obj Y) (ᘁY) ≫
      G.map ((α_ X (F.obj Y) (F.obj (ᘁY))).hom ≫
        X ◁ (μ F Y (ᘁY) ≫ F.map (ε_ (ᘁY) Y) ≫ η F) ≫ (ρ_ X).hom))
  hom_inv_id := by
    apply (tensorRightHomEquiv (G.obj X ⊗ Y) (ᘁY) Y (G.obj X)).symm.injective
    rw [tensorRightHomEquiv_symm_naturality, Equiv.symm_apply_apply,
      adj.projectionMap_evaluation]
    simp [tensorRightHomEquiv]
  inv_hom_id := by
    letI : ExactPairing (F.obj (ᘁY)) (F.obj Y) := ExactPairing.map F (ᘁY) Y
    have hε : (ε_ (F.obj (ᘁY)) (F.obj Y) : F.obj Y ⊗ F.obj (ᘁY) ⟶ 𝟙_ D) =
        μ F Y (ᘁY) ≫ F.map (ε_ (ᘁY) Y) ≫ η F := rfl
    have hzig : (tensorRightHomEquiv (X ⊗ F.obj Y) (F.obj (ᘁY)) (F.obj Y) X)
        ((α_ X (F.obj Y) (F.obj (ᘁY))).hom ≫
          X ◁ (μ F Y (ᘁY) ≫ F.map (ε_ (ᘁY) Y) ≫ η F) ≫ (ρ_ X).hom) = 𝟙 (X ⊗ F.obj Y) := by
      rw [show (α_ X (F.obj Y) (F.obj (ᘁY))).hom ≫
            X ◁ (μ F Y (ᘁY) ≫ F.map (ε_ (ᘁY) Y) ≫ η F) ≫ (ρ_ X).hom =
          (tensorRightHomEquiv (X ⊗ F.obj Y) (F.obj (ᘁY)) (F.obj Y) X).symm
            (𝟙 (X ⊗ F.obj Y)) by simp [tensorRightHomEquiv, hε],
        Equiv.apply_symm_apply]
    dsimp only [tensorRightHomEquiv, Equiv.coe_fn_mk] at hzig ⊢
    rw [show (η_ (F.obj (ᘁY)) (F.obj Y) : 𝟙_ D ⟶ _) =
        ε F ≫ F.map (η_ (ᘁY) Y) ≫ δ F (ᘁY) Y from rfl] at hzig
    have hG := congrArg G.map hzig
    simp only [Category.assoc, MonoidalCategory.comp_whiskerRight]
    rw [adj.projectionMap_natural_left, ← adj.projectionMap_assoc_assoc,
      adj.projectionMap_natural_right_assoc,
      show (X ⊗ F.obj Y) ◁ F.map (η_ (ᘁY) Y) =
          (X ⊗ F.obj Y) ◁ η F ≫ (X ⊗ F.obj Y) ◁ (ε F ≫ F.map (η_ (ᘁY) Y)) by
        rw [← MonoidalCategory.whiskerLeft_comp, Functor.Monoidal.η_ε_assoc],
      Functor.map_comp]
    simp only [Category.assoc]
    rw [adj.projectionMap_unit_assoc, Iso.inv_hom_id_assoc]
    simp only [Functor.map_comp, Functor.map_id, MonoidalCategory.whiskerLeft_comp,
      Category.assoc] at hG ⊢
    exact hG

/-- The projection morphism of a monoidal adjunction whose left adjoint is strong monoidal
is an isomorphism at every object with a left dual. -/
instance isIso_projectionMap (X : D) (Y : C) [HasLeftDual Y] :
    IsIso (adj.projectionMap X Y) :=
  (adj.projectionMapIso X Y).isIso_hom

end Dualizable

end CategoryTheory.Adjunction
