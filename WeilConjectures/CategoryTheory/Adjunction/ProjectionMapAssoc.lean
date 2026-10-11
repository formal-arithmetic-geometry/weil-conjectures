/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor

/-!
# Associativity of the projection map

Let `adj : F ⊣ G` be an adjunction between monoidal categories whose left adjoint `F` is
oplax monoidal, and let `PF : G M ⊗ L ⟶ G (M ⊗ F L)` be the right adjoint projection map
(`CategoryTheory.Adjunction.rightAdjointProjectionMap` for the comonoidal structure of `F`).
The projection map is compatible with the associators:
```
G M ⊗ (L ⊗ L') --PF--> G (M ⊗ F (L ⊗ L')) --G(M ◁ δ)--> G (M ⊗ (F L ⊗ F L'))
      |                                                         |
     α⁻¹                                                      G(α⁻¹)
      v                                                         v
(G M ⊗ L) ⊗ L' --PF ▷ L'--> G (M ⊗ F L) ⊗ L' --PF--> G ((M ⊗ F L) ⊗ F L')
```

## Main results

- `CategoryTheory.Adjunction.rightAdjointProjectionMap_assoc`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The right adjoint projection map `G M ⊗ L ⟶ G (M ⊗ F L)` of an oplax monoidal left adjoint
is compatible with the associators. -/
lemma rightAdjointProjectionMap_assoc (M : C) (L L' : D) :
    ((adj.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app M).app (L ⊗ L') ≫
        G.map (M ◁ δ F L L') ≫ G.map (α_ M (F.obj L) (F.obj L')).inv =
      (α_ (G.obj M) L L').inv ≫
        (((adj.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app M).app L ▷ L') ≫
          ((adj.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app
            (M ⊗ F.obj L)).app L' := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, counit_naturality]
  erw [adj.counit.naturality_assoc, map_rightAdjointProjectionMap_app_app_comp_counit_assoc,
    map_rightAdjointProjectionMap_app_app_comp_counit]
  trace_state
  simp only [δNatTrans_app_app, curriedTensor_map_app, Functor.id_map]
  erw [← δ_natural_left_assoc, ← comp_whiskerRight]
  erw [map_rightAdjointProjectionMap_app_app_comp_counit]
  simp only [δNatTrans_app_app, curriedTensor_map_app, comp_whiskerRight]
  erw [← associativity_inv_assoc]
  rw [← associator_inv_naturality_left, ← whisker_exchange_assoc]
  rfl

end CategoryTheory.Adjunction
