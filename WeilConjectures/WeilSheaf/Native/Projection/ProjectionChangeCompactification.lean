/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.NatIso

/-! # Transporting a projection square to another compact direct image -/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
  {I J : C ⥤ D} (η : J ≅ I)
  {A B M : C} {U V T N : D}

/-- A projection square is preserved by an isomorphism of geometric direct images which
intertwines their projection morphisms. -/
lemma projectionForgetSquare_changeGeometricPush
    (a : U ⟶ V) (dA : V ⟶ I.obj A) (b : U ⟶ T ⊗ N) (dM : T ⟶ I.obj M)
    (βA : V ⟶ J.obj A) (βM : T ⟶ J.obj M) (t : A ⟶ B)
    (pI : I.obj M ⊗ N ⟶ I.obj B) (pJ : J.obj M ⊗ N ⟶ J.obj B)
    (hβA : βA = dA ≫ η.inv.app A) (hβM : βM = dM ≫ η.inv.app M)
    (hη : η.hom.app M ▷ N ≫ pI = pJ ≫ η.hom.app B)
    (h : a ≫ dA ≫ I.map t = b ≫ dM ▷ N ≫ pI) :
    a ≫ βA ≫ J.map t = b ≫ βM ▷ N ≫ pJ := by
  have hc : η.inv.app M ▷ N ≫ η.hom.app M ▷ N = 𝟙 _ := by
    rw [← comp_whiskerRight, Iso.inv_hom_id_app, id_whiskerRight]
  rw [hβA, hβM]
  apply (cancel_mono (η.hom.app B)).1
  simp only [comp_whiskerRight, Category.assoc]
  rw [η.hom.naturality t, ← hη]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hc, Category.id_comp]
  exact h

end CategoryTheory
