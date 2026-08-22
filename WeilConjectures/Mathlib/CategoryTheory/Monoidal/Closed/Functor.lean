/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# The internal hom adjunction formula for a monoidal adjunction

Given an adjunction `adj : L ⊣ R` between monoidal categories with `L` strong monoidal,
we construct the canonical natural isomorphism

`CategoryTheory.Adjunction.ihomNatIso : ihom (L.obj Y) ⋙ R ≅ R ⋙ ihom Y`,

i.e. `R [L Y, X] ≅ [Y, R X]` naturally in `X` — the "adjunction formula" expressing that
the right adjoint of a monoidal adjunction is a closed functor. It is obtained by
conjugating the commutation isomorphism `tensorLeft Y ⋙ L ≅ L ⋙ tensorLeft (L.obj Y)`
of the strong monoidal functor `L` across the composed adjunctions
`L ⋙ tensorLeft (L.obj Y) ⊣ ihom (L.obj Y) ⋙ R` and `tensorLeft Y ⋙ L ⊣ R ⋙ ihom Y`.

In contrast to the projection formula, no dualizability hypothesis is needed.

## Main declarations

- `CategoryTheory.Adjunction.ihomNatIso`: the natural isomorphism
  `ihom (L.obj Y) ⋙ R ≅ R ⋙ ihom Y`.
- `CategoryTheory.Adjunction.ihomIso`: its component
  `R.obj ((ihom (L.obj Y)).obj X) ≅ (ihom Y).obj (R.obj X)`.
- `CategoryTheory.Adjunction.uncurry_ihomNatIso_hom_app`: when the adjunction is monoidal,
  the uncurried forward map is `η_Y ▷ _ ≫ μ ≫ R.map ev`, the formula quoted by downstream
  instantiations.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory MonoidalClosed Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Monoidal]

/-- The internal hom adjunction formula: for an adjunction `L ⊣ R` with `L` strong
monoidal, there is a canonical isomorphism `R [L Y, X] ≅ [Y, R X]` natural in `X`. It is
the conjugate of the commutation isomorphism `tensorLeft Y ⋙ L ≅ L ⋙ tensorLeft (L.obj Y)`
across the composed adjunctions. -/
def ihomNatIso (Y : C) [Closed Y] [Closed (L.obj Y)] :
    ihom (L.obj Y) ⋙ R ≅ R ⋙ ihom Y :=
  conjugateIsoEquiv (adj.comp (ihom.adjunction (L.obj Y))) ((ihom.adjunction Y).comp adj)
    (Functor.Monoidal.commTensorLeft L Y).symm

/-- The component of the internal hom adjunction formula `ihomNatIso` at an object:
`R [L Y, X] ≅ [Y, R X]`. -/
def ihomIso (Y : C) [Closed Y] [Closed (L.obj Y)] (X : D) :
    R.obj ((ihom (L.obj Y)).obj X) ≅ (ihom Y).obj (R.obj X) :=
  (adj.ihomNatIso Y).app X

@[simp]
lemma ihomIso_hom (Y : C) [Closed Y] [Closed (L.obj Y)] (X : D) :
    (adj.ihomIso Y X).hom = (adj.ihomNatIso Y).hom.app X :=
  rfl

@[simp]
lemma ihomIso_inv (Y : C) [Closed Y] [Closed (L.obj Y)] (X : D) :
    (adj.ihomIso Y X).inv = (adj.ihomNatIso Y).inv.app X :=
  rfl

variable [R.LaxMonoidal] [adj.IsMonoidal]

/-- The forward map of the internal hom adjunction formula is, after uncurrying, the
composite `η_Y ▷ R [L Y, X] ≫ μ ≫ R.map ev` built from the unit of the adjunction, the
lax monoidal structure of `R` and the evaluation of the internal hom. -/
lemma uncurry_ihomNatIso_hom_app (Y : C) [Closed Y] [Closed (L.obj Y)] (X : D) :
    MonoidalClosed.uncurry ((adj.ihomNatIso Y).hom.app X) =
      adj.unit.app Y ▷ R.obj ((ihom (L.obj Y)).obj X) ≫
        μ R (L.obj Y) ((ihom (L.obj Y)).obj X) ≫ R.map ((ihom.ev (L.obj Y)).app X) := by
  have h : (adj.ihomNatIso Y).hom.app X =
      MonoidalClosed.curry (adj.unit.app (Y ⊗ R.obj ((ihom (L.obj Y)).obj X)) ≫
        R.map (δ L Y (R.obj ((ihom (L.obj Y)).obj X)) ≫
          (L.obj Y ◁ adj.counit.app ((ihom (L.obj Y)).obj X)) ≫
          (ihom.ev (L.obj Y)).app X)) := by
    simp [ihomNatIso, MonoidalClosed.curry_eq, comp_unit_app, comp_counit_app]
    rfl
  rw [h, MonoidalClosed.uncurry_curry, R.map_comp, adj.unit_app_tensor_comp_map_δ_assoc,
    R.map_comp]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [← μ_natural_right_assoc, tensorHom_def_assoc, ← whiskerLeft_comp_assoc,
    adj.right_triangle_components]
  simp

/-- The uncurried component of the internal hom adjunction formula `ihomIso` is the
composite `η_Y ▷ R [L Y, X] ≫ μ ≫ R.map ev`. -/
lemma uncurry_ihomIso_hom (Y : C) [Closed Y] [Closed (L.obj Y)] (X : D) :
    MonoidalClosed.uncurry (adj.ihomIso Y X).hom =
      adj.unit.app Y ▷ R.obj ((ihom (L.obj Y)).obj X) ≫
        μ R (L.obj Y) ((ihom (L.obj Y)).obj X) ≫ R.map ((ihom.ev (L.obj Y)).app X) :=
  adj.uncurry_ihomNatIso_hom_app Y X

end CategoryTheory.Adjunction
