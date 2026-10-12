/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

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
  rw [unitEndAction_apply, ← unitors_inv_equal, ← unitors_equal, leftUnitor_inv_naturality_assoc,
    ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

/-- The action of endomorphisms of the unit, as a ring homomorphism. -/
@[simps!]
def unitEndRingHom [Preadditive C] [MonoidalPreadditive C] (X : C) : End (𝟙_ C) →+* End X :=
  { unitEndAction X with
    map_zero' := by simp
    map_add' u v := by simp }

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
  rw [id_eq, ← unitors_equal]
  infer_instance

/-- The canonical maps `𝟙_ C ⟶ [X, X]` are compatible with isomorphisms `X ≅ Y`. -/
lemma id_comp_ihom_map {X Y : C} (f : X ⟶ Y) :
    id X ≫ (ihom X).map f = id Y ≫ (pre f).app Y :=
  uncurry_injective (by
    rw [uncurry_natural_right, uncurry_pre_app, id_eq, id_eq, uncurry_curry, uncurry_curry,
      rightUnitor_naturality])

/-- If `𝟙_ C ⟶ [X, X]` is an isomorphism, so is `𝟙_ C ⟶ [Y, Y]` for `Y ≅ X`. -/
lemma isIso_id_of_iso {X Y : C} (e : X ≅ Y) [IsIso (id X)] : IsIso (id Y) := by
  have : IsIso (id Y ≫ (pre e.hom).app Y) := by
    rw [← id_comp_ihom_map]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((pre e.hom).app Y)

end MonoidalClosed

namespace MonoidalCategory

open MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/-- The action of `u` is the uncurried composite of `u` and `𝟙_ C ⟶ [X, X]`. -/
lemma unitEndAction_apply_eq_uncurry' (X : C) (u : End (𝟙_ C)) :
    unitEndAction X u = uncurry' (u ≫ MonoidalClosed.id X) := by
  rw [unitEndAction_apply, uncurry', id_eq, uncurry_natural_left, uncurry_curry]

/-- **Endomorphisms of an object `X` with `𝟙_ C ≅ [X, X]` are endomorphisms of the unit**: the
action `End (𝟙_ C) → End X` is bijective. -/
theorem bijective_unitEndAction (X : C) [IsIso (MonoidalClosed.id X)] :
    Function.Bijective (unitEndAction X) := by
  refine ⟨fun u v h ↦ ?_, fun g ↦ ⟨curry' g ≫ inv (MonoidalClosed.id X), ?_⟩⟩
  · rw [unitEndAction_apply_eq_uncurry', unitEndAction_apply_eq_uncurry'] at h
    exact (cancel_mono (MonoidalClosed.id X)).1 (uncurry'_injective h)
  · rw [unitEndAction_apply_eq_uncurry', Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      uncurry'_curry']

/-- The action `End (𝟙_ C) ≃* End X`, for `X` with `𝟙_ C ≅ [X, X]`. -/
noncomputable def unitEndMulEquiv (X : C) [IsIso (MonoidalClosed.id X)] : End (𝟙_ C) ≃* End X :=
  MulEquiv.ofBijective (unitEndAction X) (bijective_unitEndAction X)

@[simp]
lemma unitEndMulEquiv_apply (X : C) [IsIso (MonoidalClosed.id X)] (u : End (𝟙_ C)) :
    unitEndMulEquiv X u = unitEndAction X u :=
  rfl

/-- The action `End (𝟙_ C) ≃+* End X` as a ring isomorphism, for `X` with `𝟙_ C ≅ [X, X]`. -/
noncomputable def unitEndRingEquiv [Preadditive C] [MonoidalPreadditive C] (X : C)
    [IsIso (MonoidalClosed.id X)] : End (𝟙_ C) ≃+* End X :=
  RingEquiv.ofBijective (unitEndRingHom X) (bijective_unitEndAction X)

@[simp]
lemma unitEndRingEquiv_apply [Preadditive C] [MonoidalPreadditive C] (X : C)
    [IsIso (MonoidalClosed.id X)] (u : End (𝟙_ C)) :
    unitEndRingEquiv X u = unitEndAction X u :=
  rfl

/-- **The automorphisms of an object `X` with `𝟙_ C ≅ [X, X]` are the units of
`End (𝟙_ C)`**, acting on `X`. -/
noncomputable def unitsUnitEndMulEquivAut (X : C) [IsIso (MonoidalClosed.id X)] :
    (End (𝟙_ C))ˣ ≃* Aut X :=
  (Units.mapEquiv (unitEndMulEquiv X)).trans (Aut.unitsEndEquivAut X)

@[simp]
lemma unitsUnitEndMulEquivAut_apply_hom (X : C) [IsIso (MonoidalClosed.id X)]
    (u : (End (𝟙_ C))ˣ) :
    (unitsUnitEndMulEquivAut X u).hom = unitEndAction X u :=
  rfl

/-- **Two isomorphisms `X ≅ Y` differ by a unique unit of `End (𝟙_ C)`**, provided
`𝟙_ C ≅ [Y, Y]`: there is a unique unit `u` with `ψ = u • φ`. -/
theorem existsUnique_hom_eq_comp_unitEndAction {X Y : C} [IsIso (MonoidalClosed.id Y)]
    (φ ψ : X ≅ Y) : ∃! u : (End (𝟙_ C))ˣ, ψ.hom = φ.hom ≫ unitEndAction Y u := by
  refine ⟨(unitsUnitEndMulEquivAut Y).symm (φ.symm ≪≫ ψ), ?_, fun v hv ↦ ?_⟩
  · rw [← unitsUnitEndMulEquivAut_apply_hom, MulEquiv.apply_symm_apply, Iso.trans_hom,
      Iso.symm_hom, Iso.hom_inv_id_assoc]
  · rw [MulEquiv.eq_symm_apply]
    refine Iso.ext ?_
    rw [unitsUnitEndMulEquivAut_apply_hom, Iso.trans_hom, Iso.symm_hom, hv, Iso.inv_hom_id_assoc]

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
      μ_natural_right_assoc, ← F.map_comp, ← uncurry_eq, id_eq, id_eq, uncurry_curry,
      uncurry_curry, right_unitality])

/-- If the unit map and the comparison map of `F` at `X` are isomorphisms, `F` maps the
canonical map `𝟙_ C ⟶ [X, X]` to an isomorphism if `𝟙_ D ⟶ [F X, F X]` is one. -/
lemma isIso_map_id [IsIso (ε F)] (X : C) [IsIso ((ihomComparison F X).natTrans.app X)]
    [IsIso (MonoidalClosed.id (F.obj X))] : IsIso (F.map (MonoidalClosed.id X)) := by
  have : IsIso (ε F ≫ F.map (MonoidalClosed.id X) ≫ (ihomComparison F X).natTrans.app X) := by
    rw [ε_comp_map_id_comp_ihomComparison]
    infer_instance
  have : IsIso (F.map (MonoidalClosed.id X) ≫ (ihomComparison F X).natTrans.app X) :=
    IsIso.of_isIso_comp_left (ε F) _
  exact IsIso.of_isIso_comp_right _ ((ihomComparison F X).natTrans.app X)

end Functor.LaxMonoidal

end CategoryTheory
