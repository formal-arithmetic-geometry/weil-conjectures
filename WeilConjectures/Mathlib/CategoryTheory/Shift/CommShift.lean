/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Detecting the compatibility of a natural transformation with shifts

Let `τ : F₁ ⟶ F₂` be a natural transformation between functors which commute with shifts.
We give two criteria for `τ` to commute with shifts (`NatTrans.CommShift τ A`):

- `CategoryTheory.NatTrans.CommShift.of_whiskerRight`: it suffices that `τ` commutes with
  shifts after composition with a faithful functor `G` commuting with shifts;
- `CategoryTheory.NatTrans.CommShift.of_whiskerLeft`: it suffices that `τ` commutes with
  shifts after precomposition with a functor `L` commuting with shifts, provided every object
  `X` maps to some `L.obj Y` by a morphism `f` such that `F₂.map f` is an isomorphism. This
  applies for instance when `L` is essentially surjective, or when `L` is the inclusion of
  a class of objects such as complexes of injective objects, through which every object is
  resolved.
-/

@[expose] public section

namespace CategoryTheory.NatTrans.CommShift

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*} [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A]
  {F₁ F₂ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.CommShift A] [F₂.CommShift A]

/-- A natural transformation commutes with shifts if it does after composition with a
faithful functor commuting with shifts. -/
lemma of_whiskerRight (G : D ⥤ E) [G.CommShift A] [G.Faithful]
    [NatTrans.CommShift (Functor.whiskerRight τ G) A] : NatTrans.CommShift τ A where
  shift_comm a := by
    ext X
    apply G.map_injective
    have h := NatTrans.shift_app_comm (Functor.whiskerRight τ G) a X
    simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.commShiftIso_comp_hom_app,
      Category.assoc] at h
    rw [← Functor.commShiftIso_hom_naturality, ← G.map_comp_assoc, ← G.map_comp_assoc] at h
    simpa using (cancel_mono _).1 h

/-- A natural transformation `τ : F₁ ⟶ F₂` commutes with shifts if it does after
precomposition with a functor `L` commuting with shifts, provided every object `X` maps to
an object `L.obj Y` by a morphism `f` such that `F₂.map f` is an isomorphism. -/
lemma of_whiskerLeft (L : E ⥤ C) [L.CommShift A]
    [NatTrans.CommShift (Functor.whiskerLeft L τ) A]
    (h : ∀ X, ∃ (Y : E) (f : X ⟶ L.obj Y), IsIso (F₂.map f)) : NatTrans.CommShift τ A where
  shift_comm a := by
    ext X
    obtain ⟨Y, f, hf⟩ := h X
    have hY : (F₁.commShiftIso a).hom.app (L.obj Y) ≫ (τ.app (L.obj Y))⟦a⟧' =
        τ.app ((L.obj Y)⟦a⟧) ≫ (F₂.commShiftIso a).hom.app (L.obj Y) := by
      have h := NatTrans.shift_app_comm (Functor.whiskerLeft L τ) a Y
      simp only [Functor.comp_obj, Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app,
        Category.assoc] at h
      rw [← τ.naturality_assoc] at h
      exact (cancel_epi _).1 h
    dsimp
    rw [← cancel_mono ((F₂.map f)⟦a⟧'), Category.assoc, ← Functor.map_comp,
      ← τ.naturality, Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc, hY,
      Category.assoc, ← Functor.commShiftIso_hom_naturality, τ.naturality_assoc]

end CategoryTheory.NatTrans.CommShift
