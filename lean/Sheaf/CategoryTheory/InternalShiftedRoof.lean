/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! # Localized shifted roofs with a fixed endpoint comparison

Source: the generic categorical cancellation in step 4 of the internal character-roof
argument, under paragraph (3) of the latest six-functors direct-images proof
(blueprint: def-sfb-localized-shifted-roof).
The irreducible wrapper keeps concrete action-category structures out of shift algebra.
Its defining formula is the ordinary localized roof with canonical shift comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory
namespace CategoryTheory.CondensedDerivedRestriction

/-- Ordered shifted arrows in a category, including the identity at degree zero.
This helper implements the finite composition without unfolding the action category.
Source: latest direct-images proof, paragraph (3), internal normalization
(blueprint: lem-sfb-internal-bar-character-roof-cup). -/
def orderedShiftedArrows {D : Type v} [Category.{w} D] [HasShift D ℤ] (X : D) :
    (q : ℕ) → (Fin q → (X ⟶ X⟦(1 : ℤ)⟧)) → (X ⟶ X⟦(q : ℤ)⟧)
  | 0, _ => ShiftedHom.mk₀ 0 rfl (𝟙 X)
  | q + 1, L => ShiftedHom.comp
      (orderedShiftedArrows X q (fun i ↦ L i.castSucc)) (L (Fin.last q))
      (by simp [Nat.cast_add, add_comm])

private def conjugateShifted {D : Type v} [Category.{w} D] [HasShift D ℤ]
    {X Y : D} (e : X ≅ Y) {n : ℤ} (f : X ⟶ X⟦n⟧) : Y ⟶ Y⟦n⟧ :=
  e.inv ≫ f ≫ e.hom⟦n⟧'

private lemma conjugateShifted_comp {D : Type v} [Category.{w} D] [HasShift D ℤ]
    {X Y : D} (e : X ≅ Y) {a b c : ℤ}
    (f : X ⟶ X⟦a⟧) (g : X ⟶ X⟦b⟧) (h : b + a = c) :
    conjugateShifted e (ShiftedHom.comp f g h) =
      ShiftedHom.comp (conjugateShifted e f) (conjugateShifted e g) h := by
  simp only [conjugateShifted, ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← (shiftFunctor D a).map_comp_assoc e.hom e.inv]
  simp only [Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  rw [← (shiftFunctorAdd' D b a c h).inv.naturality]
  rfl

private lemma conjugateShifted_zero {D : Type v} [Category.{w} D] [HasShift D ℤ]
    {X Y : D} (e : X ≅ Y) :
    conjugateShifted e (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 X)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 Y) := by
  dsimp only [conjugateShifted, ShiftedHom.mk₀]
  rw [Category.id_comp, ← (shiftFunctorZero' D (0 : ℤ) rfl).inv.naturality]
  simpa only [Functor.id_map, Category.id_comp] using e.inv_hom_id_assoc _

private lemma localizedRoof_as_conjugate
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (Q : C ⥤ D) [Q.CommShift ℤ] {X Y : C} {Z : D}
    (e : X ⟶ Y) [IsIso (Q.map e)] (s : Z ≅ Q.obj Y) (q : ℤ)
    (F : X ⟶ X⟦q⟧) :
    s.hom ≫ inv (Q.map e) ≫ Q.map (F ≫ e⟦q⟧') ≫
        (Q.commShiftIso q).hom.app Y ≫ s.inv⟦q⟧' =
      conjugateShifted (asIso (Q.map e) ≪≫ s.symm) (ShiftedHom.map F Q) := by
  dsimp only [conjugateShifted, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv, ShiftedHom.map]
  simp only [Functor.map_comp, Category.assoc, Q.commShiftIso_hom_naturality_assoc]

/-- The localized roof with endpoint identification s. No data are chosen:
this is the displayed composition of the inverse augmentation, shifted arrow and s.
Source: internal character-roof argument, step 4
(blueprint: def-sfb-localized-shifted-roof). -/
@[irreducible] def localizedShiftedRoof
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (Q : C ⥤ D) [Q.CommShift ℤ] {X Y : C} {Z : D}
    (e : X ⟶ Y) [IsIso (Q.map e)] (s : Z ≅ Q.obj Y) (q : ℤ)
    (F : X ⟶ X⟦q⟧) : Z ⟶ Z⟦q⟧ :=
  s.hom ≫ inv (Q.map e) ≫ Q.map (F ≫ e⟦q⟧') ≫
    (Q.commShiftIso q).hom.app Y ≫ s.inv⟦q⟧'

/-- Cancellation of the shifted intermediate augmentation preserves ordered composition.
Source: internal character-roof argument, step 4
(blueprint: def-sfb-localized-shifted-roof). -/
theorem localizedShiftedRoof_comp
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (Q : C ⥤ D) [Q.CommShift ℤ] {X Y : C} {Z : D}
    (e : X ⟶ Y) [IsIso (Q.map e)] (s : Z ≅ Q.obj Y)
    {a b c : ℤ} (f : X ⟶ X⟦a⟧) (g : X ⟶ X⟦b⟧) (h : b + a = c) :
    localizedShiftedRoof Q e s c (ShiftedHom.comp f g h) =
      ShiftedHom.comp (localizedShiftedRoof Q e s a f)
        (localizedShiftedRoof Q e s b g) h := by
  simp only [localizedShiftedRoof, localizedRoof_as_conjugate,
    ShiftedHom.map_comp, conjugateShifted_comp]

/-- The empty roof is the zero-shift identity at the coefficient object.
Source: internal character-roof argument, step 4
(blueprint: def-sfb-localized-shifted-roof). -/
theorem localizedShiftedRoof_zero
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (Q : C ⥤ D) [Q.CommShift ℤ] {X Y : C} {Z : D}
    (e : X ⟶ Y) [IsIso (Q.map e)] (s : Z ≅ Q.obj Y) :
    localizedShiftedRoof Q e s 0 (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 X)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 Z) := by
  simp only [localizedShiftedRoof, localizedRoof_as_conjugate,
    ShiftedHom.map_mk₀, Functor.map_id, conjugateShifted_zero]

/-- Finite ordered composites of roofs are the roofs of finite ordered composites.
The empty family uses the zero-shift identity on both sides.
Source: internal character-roof argument, step 4
(blueprint: def-sfb-localized-shifted-roof). -/
theorem localizedShiftedRoof_ordered
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (Q : C ⥤ D) [Q.CommShift ℤ] {X Y : C} {Z : D}
    (e : X ⟶ Y) [IsIso (Q.map e)] (s : Z ≅ Q.obj Y) (q : ℕ)
    (L : Fin q → (X ⟶ X⟦(1 : ℤ)⟧)) :
    localizedShiftedRoof Q e s (q : ℤ) (orderedShiftedArrows X q L) =
      orderedShiftedArrows Z q (fun i ↦ localizedShiftedRoof Q e s 1 (L i)) := by
  induction q with
  | zero => exact localizedShiftedRoof_zero Q e s
  | succ q ih =>
    rw [orderedShiftedArrows, localizedShiftedRoof_comp, ih]
    rfl

end CategoryTheory.CondensedDerivedRestriction
