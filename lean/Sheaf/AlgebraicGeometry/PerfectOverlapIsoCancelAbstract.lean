/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # A categorical cancellation used by the overlap object pin -/

@[expose] public section

open CategoryTheory
namespace AlgebraicGeometry

/-- Pasting a whiskered natural isomorphism after its inverse component
leaves the following comparison unchanged.

Proof: The component of the whiskered isomorphism is the functorial image of
the original component. Functoriality carries the inverse-forward product to
the identity; the identity law removes it from the composite. -/
theorem perfectOverlapIsoWhiskerRight_inv_cancel
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {P Q : C ⥤ D} {R : C ⥤ E}
    (α : P ≅ Q) (H : D ⥤ E) (β : Q ⋙ H ≅ R) (X : C) :
    H.map (α.inv.app X) ≫
      ((Functor.isoWhiskerRight α H ≪≫ β).app X).hom =
        (β.app X).hom := by
  rw [NatIso.trans_app, Iso.trans_hom]
  change H.map (α.inv.app X) ≫ H.map (α.hom.app X) ≫ (β.app X).hom = _
  rw [← Category.assoc, ← H.map_comp, Iso.inv_hom_id_app,
    H.map_id, Category.id_comp]

end AlgebraicGeometry
