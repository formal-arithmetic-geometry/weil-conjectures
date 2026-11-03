/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Unit normalization from a normalized counit

Source: lem-fix-weil-operations.proof.md, paragraph 3, ordinary adjunction.
-/

@[expose] public section
set_option autoImplicit false

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
  {U : C ⥤ E} {V : D ⥤ F}

/-- Counit-normalized invertible comparisons also normalize the unit, without any
faithfulness or equivalence assumption on the vertical functors.

Source: lem-fix-weil-operations.proof.md, paragraph 3, ordinary adjunction
(blueprint: lem-sf-adjunction-unit-from-counit-normalization).

Proof: transpose the counit equation by the lower adjunction. The counit identity
for mates and cancellation of the left comparison identify the right comparison
with the mate of the inverse left comparison. Apply the unit identity for mates
and cancel the right comparison. This also applies to identity functors and to
empty categories; neither conservativity nor faithfulness enters the argument. -/
theorem adjunction_unit_of_counit_normalization
    (a : L ⊣ R) (b : L' ⊣ R')
    (l : L ⋙ V ≅ U ⋙ L') (r : R ⋙ U ≅ V ⋙ R')
    (hc : ∀ Y : D, V.map (a.counit.app Y) =
      l.hom.app (R.obj Y) ≫ L'.map (r.hom.app Y) ≫ b.counit.app (V.obj Y))
    (X : C) :
    U.map (a.unit.app X) = b.unit.app (U.obj X) ≫
      R'.map (l.inv.app X) ≫ r.inv.app (L.obj X) := by
  have hm : (mateEquiv a b l.inv).natTrans = r.hom := by
    ext Y
    apply (b.homEquiv (U.obj (R.obj Y)) (V.obj Y)).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    rw [mateEquiv_counit a b l.inv Y, hc Y]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hu := unit_mateEquiv a b l.inv X
  change U.map (a.unit.app X) ≫
    (mateEquiv a b l.inv).natTrans.app (L.obj X) = _ at hu
  rw [hm] at hu
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv (r.app (L.obj X))).2 hu

end CategoryTheory
