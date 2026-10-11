/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Conjugation of natural transformations commuting with shifts

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions compatible with given `CommShift`
structures on the four functors (`CategoryTheory.Adjunction.CommShift`). If a natural
transformation `α : L₂ ⟶ L₁` commutes with the shifts, so does its conjugate
`conjugateEquiv adj₁ adj₂ α : R₁ ⟶ R₂`, which is built from `α`, the unit of `adj₂` and the
counit of `adj₁` (`CategoryTheory.conjugateEquiv_eq_comp`).

## Main results

- `CategoryTheory.Adjunction.CommShift.ofNatIsoLeft`: transporting an adjunction compatible
  with shifts along an isomorphism of left adjoints commuting with shifts.
- `CategoryTheory.NatTrans.CommShift.conjugateEquiv`: the conjugate of a natural
  transformation commuting with shifts commutes with shifts.
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] {A : Type*} [AddMonoid A] [HasShift C A]
  [HasShift D A] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The conjugate of a natural transformation commuting with shifts commutes with shifts. -/
instance NatTrans.CommShift.conjugateEquiv [L₁.CommShift A] [L₂.CommShift A] [R₁.CommShift A]
    [R₂.CommShift A] [adj₁.CommShift A] [adj₂.CommShift A] (α : L₂ ⟶ L₁)
    [NatTrans.CommShift α A] : NatTrans.CommShift (conjugateEquiv adj₁ adj₂ α) A := by
  rw [conjugateEquiv_eq_comp]
  infer_instance

/-- An adjunction compatible with shifts stays so after transport along an isomorphism of
left adjoints commuting with the shifts. -/
lemma Adjunction.CommShift.ofNatIsoLeft {L L' : C ⥤ D} {R : D ⥤ C} [L.CommShift A]
    [L'.CommShift A] [R.CommShift A] (adj : L ⊣ R) [adj.CommShift A] (e : L ≅ L')
    [NatTrans.CommShift e.hom A] : (adj.ofNatIsoLeft e).CommShift A :=
  .mk' _ _ (by rw [ofNatIsoLeft_unit]; infer_instance)

end CategoryTheory
