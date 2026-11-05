/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Additive functors applied to a splitting

An additive functor `G` applied to a splitting `P ≅ (A ⊞ B) ⊞ M` gives a splitting of `G P`;
if `G P` and `G A` are both identified with `U`, this is `U ≅ U ⊞ (G B ⊞ G M)`. The statement is
for abstract functors, so that it can be applied to composites of derived functors without the
kernel unfolding them.

## Main statements

- `CategoryTheory.Functor.nonempty_iso_biprod_of_iso_biprod`: `U ≅ U ⊞ (G B ⊞ G M)`.
- `CategoryTheory.NatTrans.isIso_app_biproduct`: a natural transformation between additive
  functors is invertible at a finite biproduct if it is invertible at the summands.
-/

@[expose] public section

namespace CategoryTheory

open Limits

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- A natural transformation between additive functors is invertible at a finite biproduct if it
is invertible at the summands. -/
lemma NatTrans.isIso_app_biproduct {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    {J : Type} [Finite J] (f : J → C) [HasBiproduct f] (h : ∀ j, IsIso (α.app (f j))) :
    IsIso (α.app (⨁ f)) := by
  have := Fintype.ofFinite J
  refine ⟨∑ j, G.map (biproduct.π f j) ≫ inv (α.app (f j)) ≫ F.map (biproduct.ι f j), ?_, ?_⟩
  · simp only [Preadditive.comp_sum, ← NatTrans.naturality_assoc, IsIso.hom_inv_id_assoc,
      ← Functor.map_comp, ← Functor.map_sum]
    convert F.map_id _
    exact biproduct.total
  · simp only [Preadditive.sum_comp, Category.assoc, NatTrans.naturality, IsIso.inv_hom_id_assoc,
      ← Functor.map_comp, ← Functor.map_sum]
    convert G.map_id _
    exact biproduct.total

end CategoryTheory
