/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! Faithfulness of exact derived functors on objects in a common single degree.
(blueprint: lem-pur-exact-faithful-single-morphisms)
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- An exact faithful functor detects equality of derived morphisms between objects
isomorphic to single complexes in the same degree.

Source: Mathlib's fully faithful derived single embedding and its compatibility
with exact functors. Proof: conjugate both maps by the displayed isomorphisms.
Fullness of the single embedding expresses them as images of ordinary maps.
The composite of the single embedding with the derived functor is naturally
isomorphic to the original faithful functor followed by the target single
embedding, hence faithful. Cancel the conjugating isomorphisms.
(blueprint: lem-pur-exact-faithful-single-morphisms)
-/
theorem mapDerivedCategory_injective_of_single
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (n : ℤ) {X Y : DerivedCategory C}
    (M N : C) (e : X ≅ (DerivedCategory.singleFunctor C n).obj M)
    (i : Y ≅ (DerivedCategory.singleFunctor C n).obj N)
    {f g : X ⟶ Y} (h : F.mapDerivedCategory.map f = F.mapDerivedCategory.map g) :
    f = g := by
  let S := DerivedCategory.singleFunctor C n
  let : (S ⋙ F.mapDerivedCategory).Faithful :=
    Functor.Faithful.of_iso (F.mapDerivedCategorySingleFunctor n).symm
  obtain ⟨a, ha⟩ := S.map_surjective (e.inv ≫ f ≫ i.hom)
  obtain ⟨b, hb⟩ := S.map_surjective (e.inv ≫ g ≫ i.hom)
  have hab : a = b := (S ⋙ F.mapDerivedCategory).map_injective (by
    dsimp only [Functor.comp_map]
    rw [ha, hb]
    simp only [Functor.map_comp, h])
  have hh := ha.symm.trans ((congrArg S.map hab).trans hb)
  simpa only [← cancel_epi e.inv, ← cancel_mono i.hom, Category.assoc] using hh

end CategoryTheory.Functor
