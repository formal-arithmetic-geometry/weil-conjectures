/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatible

/-!
# Compatibility with a pasted commutation square, componentwise

This file records the equation of a compatibility
(`CategoryTheory.NatTrans.SquareCompatible`) with a pasted commutation square, solved for the
components of the squares (`NatTrans.SquareCompatible.inv_app_comp_pasteSquareIso`).
-/

@[expose] public section

namespace CategoryTheory.NatTrans.SquareCompatible

variable {A B A' B' D D' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Category* D] [Category* D'] {T : A ⥤ A'} {T' : B ⥤ B'} {S : D ⥤ D'}

/-- The equation of a compatibility with a pasted commutation square, solved for the components
of the commutation squares. -/
lemma inv_app_comp_pasteSquareIso {F : A ⥤ B} {F' : A' ⥤ B'} {ιF : F ⋙ T' ≅ T ⋙ F'}
    {F₁ : A ⥤ D} {F₂ : D ⥤ B} {F₁' : A' ⥤ D'} {F₂' : D' ⥤ B'} {ι₁ : F₁ ⋙ S ≅ T ⋙ F₁'}
    {ι₂ : F₂ ⋙ T' ≅ S ⋙ F₂'} {α : F ⟶ F₁ ⋙ F₂} {α' : F' ⟶ F₁' ⋙ F₂'}
    (h : SquareCompatible ιF (Functor.pasteSquareIso ι₁ ι₂) α α') (K : A) :
    ιF.inv.app K ≫ T'.map (α.app K) ≫ ι₂.hom.app (F₁.obj K) =
      α'.app (T.obj K) ≫ F₂'.map (ι₁.inv.app K) := by
  have hK := h K
  rw [Functor.pasteSquareIso_hom_app] at hK
  rw [← cancel_mono (F₂'.map (ι₁.hom.app K))]
  simp only [Category.assoc, hK, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp

end CategoryTheory.NatTrans.SquareCompatible
