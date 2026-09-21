/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Characterisation of the canonical isomorphism between two left adjoints

If `adj1 : L₁ ⊣ G` and `adj2 : L₂ ⊣ G` are two adjunctions with the same right adjoint,
`CategoryTheory.Adjunction.leftAdjointUniq` is the canonical isomorphism `L₁ ≅ L₂`. Mathlib
records the identity `adj1.unit ≫ whiskerRight (leftAdjointUniq adj1 adj2).hom G = adj2.unit`
that it satisfies; this file records that this identity *characterises* it, which is what makes
it possible to compute with composites of such isomorphisms. The characterisation is stated
both pointwise (`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom`) and as an identity of
natural transformations (`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_of_unit`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]

/-- A natural transformation between two left adjoints of the same functor which is compatible
with the units is the canonical isomorphism `Adjunction.leftAdjointUniq`. -/
lemma eq_leftAdjointUniq_hom {L₁ L₂ : C ⥤ D} {G : D ⥤ C} (adj1 : L₁ ⊣ G) (adj2 : L₂ ⊣ G)
    (τ : L₁ ⟶ L₂) (h : ∀ X, adj1.unit.app X ≫ G.map (τ.app X) = adj2.unit.app X) :
    τ = (adj1.leftAdjointUniq adj2).hom := by
  ext X
  refine (adj1.homEquiv X (L₂.obj X)).injective ?_
  rw [Adjunction.homEquiv_unit, h X, adj1.homEquiv_leftAdjointUniq_hom_app adj2]

/-- The natural-transformation form of `CategoryTheory.Adjunction.eq_leftAdjointUniq_hom`: it is
the converse of Mathlib's `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom`. -/
lemma eq_leftAdjointUniq_hom_of_unit {L₁ L₂ : C ⥤ D} {G : D ⥤ C} (adj1 : L₁ ⊣ G) (adj2 : L₂ ⊣ G)
    (τ : L₁ ⟶ L₂) (h : adj1.unit ≫ Functor.whiskerRight τ G = adj2.unit) :
    τ = (adj1.leftAdjointUniq adj2).hom :=
  eq_leftAdjointUniq_hom adj1 adj2 τ fun X ↦ NatTrans.congr_app h X

end CategoryTheory.Adjunction
