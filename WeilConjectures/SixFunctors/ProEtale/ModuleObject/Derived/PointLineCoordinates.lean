/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd

/-! # Independence of coordinates on a trivial line
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Conjugating an endomorphism of a trivial line to the tensor unit is independent
of the chosen trivialization. -/
theorem point_line_conjugation_independent
    {A : Type*} [Category* A] [MonoidalCategory A]
    {L : A} (f : L ⟶ L) (h h' : L ≅ 𝟙_ A) :
    h.inv ≫ f ≫ h.hom = h'.inv ≫ f ≫ h'.hom := by
  have hc := unitEndAction_naturality
    (h.inv ≫ f ≫ h.hom) (End.of (h.inv ≫ h'.hom))
  simp only [unitEndAction_unit] at hc
  calc
    h.inv ≫ f ≫ h.hom =
        (h'.inv ≫ h.hom) ≫ (h.inv ≫ h'.hom) ≫ (h.inv ≫ f ≫ h.hom) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    _ = (h'.inv ≫ h.hom) ≫ (h.inv ≫ f ≫ h.hom) ≫ (h.inv ≫ h'.hom) := by
      rw [hc]
    _ = h'.inv ≫ f ≫ h'.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
