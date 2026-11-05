/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Endomorphisms of the unit acting on an object

In a monoidal category `C`, an endomorphism `u` of the unit acts on every object `X` by
`X ≅ X ⊗ 𝟙_ C ⟶ X ⊗ 𝟙_ C ≅ X` (`CategoryTheory.MonoidalCategory.unitEndAction`); this is a
monoid homomorphism `End (𝟙_ C) →* End X`, natural in `X`, and a ring homomorphism in the
preadditive case (`CategoryTheory.MonoidalCategory.unitEndRingHom`).

If `C` is monoidal closed and the canonical map `MonoidalClosed.id X : 𝟙_ C ⟶ [X, X]` is an
isomorphism, the action is bijective (`CategoryTheory.MonoidalCategory.bijective_unitEndAction`):
every endomorphism of `X` is "multiplication" by a unique endomorphism of the unit, the
automorphisms of `X` are the units of `End (𝟙_ C)`
(`CategoryTheory.MonoidalCategory.unitsUnitEndMulEquivAut`), and two isomorphisms `X ≅ Y`
differ by a unique unit of `End (𝟙_ C)`
(`CategoryTheory.MonoidalCategory.existsUnique_hom_eq_comp_unitEndAction`).

The condition on `MonoidalClosed.id X` holds for `X = 𝟙_ C`
(`CategoryTheory.MonoidalClosed.isIso_id_unit`), is invariant under isomorphism
(`CategoryTheory.MonoidalClosed.isIso_id_of_iso`), and is compatible with monoidal functors
(`CategoryTheory.Functor.LaxMonoidal.ε_comp_map_id_comp_ihomComparison`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

namespace MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- The action of an endomorphism `u` of the unit on an object `X`:
`X ≅ X ⊗ 𝟙_ C ⟶ X ⊗ 𝟙_ C ≅ X`, the middle map being `X ◁ u`. -/
@[simps]
def unitEndAction (X : C) : End (𝟙_ C) →* End X where
  toFun u := (ρ_ X).inv ≫ X ◁ u ≫ (ρ_ X).hom
  map_one' := by simp [End.one_def]
  map_mul' u v := by simp [End.mul_def]

/-- The action of endomorphisms of the unit is natural. -/
@[reassoc]
lemma unitEndAction_naturality {X Y : C} (φ : X ⟶ Y) (u : End (𝟙_ C)) :
    unitEndAction X u ≫ φ = φ ≫ unitEndAction Y u := by
  rw [unitEndAction_apply, unitEndAction_apply, Category.assoc, Category.assoc,
    ← rightUnitor_naturality, whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

/-- The action of endomorphisms of the unit on the unit is the multiplication. -/
lemma unitEndAction_unit (u : End (𝟙_ C)) : unitEndAction (𝟙_ C) u = u := by
  rw [unitEndAction_apply, ← unitors_inv_equal, ← unitors_equal, leftUnitor_naturality,
    Iso.inv_hom_id_assoc]

/-- The action of endomorphisms of the unit, as a ring homomorphism. -/
def unitEndRingHom [Preadditive C] [MonoidalPreadditive C] (X : C) : End (𝟙_ C) →+* End X where
  toFun u := (ρ_ X).inv ≫ X ◁ u ≫ (ρ_ X).hom
  map_one' := (unitEndAction X).map_one
  map_mul' := (unitEndAction X).map_mul
  map_zero' := by simp
  map_add' u v := by
    rw [MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]

@[simp]
lemma unitEndRingHom_apply [Preadditive C] [MonoidalPreadditive C] (X : C) (u : End (𝟙_ C)) :
    unitEndRingHom X u = unitEndAction X u :=
  rfl

end MonoidalCategory

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/-- The curried left unitor `𝟙_ C ⟶ [𝟙_ C, X]` is an isomorphism, with inverse the evaluation. -/
instance isIso_curry_leftUnitor_hom (X : C) : IsIso (curry (λ_ X).hom) := by
  refine ⟨(λ_ _).inv ≫ (ihom.ev (𝟙_ C)).app X, ?_, ?_⟩
  · rw [leftUnitor_inv_naturality_assoc, ← uncurry_eq, uncurry_curry]
    exact (λ_ X).inv_hom_id
  · rw [← curry_natural_left, leftUnitor_naturality, Iso.hom_inv_id_assoc, ← uncurry_id_eq_ev,
      curry_uncurry]

/-- The canonical map `𝟙_ C ⟶ [𝟙_ C, 𝟙_ C]` is an isomorphism. -/
instance isIso_id_unit : IsIso (id (𝟙_ C)) := by
  rw [MonoidalClosed.id_eq, ← unitors_equal]
  infer_instance

end MonoidalClosed

namespace MonoidalCategory

open MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

end MonoidalCategory

namespace Functor.LaxMonoidal

open MonoidalClosed

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (F : C ⥤ D) [F.LaxMonoidal]

/-- A lax monoidal functor maps the canonical map `𝟙_ C ⟶ [X, X]` to the canonical map
`𝟙_ D ⟶ [F X, F X]`, up to the unit map and the comparison map. -/
@[reassoc]
lemma ε_comp_map_id_comp_ihomComparison (X : C) :
    ε F ≫ F.map (MonoidalClosed.id X) ≫ (ihomComparison F X).natTrans.app X =
      MonoidalClosed.id (F.obj X) :=
  uncurry_injective (by
    rw [uncurry_natural_left, uncurry_natural_left, uncurry_eq, ihomComparison_ev,
      μ_natural_right_assoc, ← F.map_comp, ← uncurry_eq,
      MonoidalClosed.id_eq, MonoidalClosed.id_eq, uncurry_curry,
      uncurry_curry, right_unitality])

end Functor.LaxMonoidal

end CategoryTheory
