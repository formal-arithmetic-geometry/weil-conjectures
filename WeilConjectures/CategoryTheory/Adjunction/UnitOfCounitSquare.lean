/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Compatibility of units from compatibility of counits

Let `L ⊣ R` and `L' ⊣ R'` be adjunctions, `A : C ⥤ C'` and `B : D ⥤ D'` functors, `α : L ⋙ B ⟶
A ⋙ L'` an invertible 2-square and `β_K : A (R K) ⟶ R' (B K)` a family of morphisms. If the
counits are compatible with `α` and `β`,

`α_{R K} ≫ L' β_K ≫ ε'_{B K} = B ε_K`,

then so are the units: `A η_M ≫ β_{L M} ≫ R' α_M = η'_{A M}`. As diagrams:
```
               α_{R K}                      L' β_K
B (L (R K)) -------> L' (A (R K)) -----------> L' (R' (B K))
      \                                             |
       \ B ε_K                                      | ε'_{B K}
        \------------------------------------------>v
                                                   B K

        A η_M                   β_{L M}                    R' α_M
A M ----------> A (R (L M)) ------------> R' (B (L M)) ------------> R' (L' (A M))
  \                                                                       ^
   \------------------------------- η'_{A M} -----------------------------+
```
In applications the counit compatibility is the base change or coefficient change of a counit,
and the theorem gives the same statement for the unit.

## Main results

- `CategoryTheory.Adjunction.unit_comp_of_counit_comp`

## Implementation details

The unit is determined by the counit through the triangle identities: both sides of the unit
equation are sent to the same morphism by the hom-equivalence of `L' ⊣ R'`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}

/-- If the counits of `L ⊣ R` and `L' ⊣ R'` are compatible with an invertible 2-square
`α : L ⋙ B ⟶ A ⋙ L'` and a family `β_K : A (R K) ⟶ R' (B K)`, then so are the units:
`A η_M ≫ β_{L M} ≫ R' α_M = η'_{A M}`. -/
theorem unit_comp_of_counit_comp (adj : L ⊣ R) (adj' : L' ⊣ R') {A : C ⥤ C'} {B : D ⥤ D'}
    (α : L ⋙ B ⟶ A ⋙ L') [IsIso α] (β : ∀ K : D, A.obj (R.obj K) ⟶ R'.obj (B.obj K))
    (h : ∀ K : D, α.app (R.obj K) ≫ L'.map (β K) ≫ adj'.counit.app (B.obj K) =
      B.map (adj.counit.app K))
    (M : C) :
    A.map (adj.unit.app M) ≫ β (L.obj M) ≫ R'.map (α.app M) = adj'.unit.app (A.obj M) := by
  have key : L'.map (β (L.obj M)) ≫ adj'.counit.app (B.obj (L.obj M)) =
      (inv α).app (R.obj (L.obj M)) ≫ B.map (adj.counit.app (L.obj M)) := by
    rw [← h, NatIso.isIso_inv_app, IsIso.inv_hom_id_assoc]
  have hα := (inv α).naturality (adj.unit.app M)
  simp only [Functor.comp_map] at hα
  apply (adj'.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, counit_naturality,
    Functor.comp_obj]
  rw [reassoc_of% key, reassoc_of% hα, ← B.map_comp_assoc, left_triangle_components, B.map_id,
    Category.id_comp, ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
  exact (left_triangle_components adj' _).symm

end CategoryTheory.Adjunction
