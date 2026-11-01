/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover

/-! # Type-valued sheaves on disjoint covers

Source: the sheaf axiom, Stacks Project Tag 00VL.
(blueprint: lem-zl-disjoint-sheaf-sections).
-/

@[expose] public section
set_option autoImplicit false
universe c v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.GrothendieckTopology.IsDisjointCover

/-- Arbitrary sections on a finite disjoint cover glue.
Source: Stacks Project Tag 00VL
(blueprint: lem-zl-disjoint-sheaf-sections).
Proof: equal component indices give agreement by monicity. Unequal indices
have an empty cover on each overlap, so separatedness gives agreement there.
The sheaf axiom glues this matching family. -/
theorem exists_type_map_eq {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {W : C} {n : ℕ} {Y : Fin n → C}
    {f : ∀ i, Y i ⟶ W} (hf : J.IsDisjointCover f)
    (F : Sheaf J (Type w)) (t : ∀ i, F.obj.obj (op (Y i))) :
    ∃ x : F.obj.obj (op W), ∀ i, F.obj.map (f i).op x = t i := by
  have hF := ((isSheaf_iff_isSheaf_of_type J F.obj).1 F.property).isSheafFor _
    hf.ofArrows_mem
  rw [Presieve.isSheafFor_arrows_iff] at hF
  obtain ⟨x, hx, -⟩ := hF t (by
    intro i j Z a b hab
    by_cases hij : i = j
    · subst hij
      have := hf.mono i
      obtain rfl := (cancel_mono (f i)).1 hab
      rfl
    · exact Sheaf.isSeparated F Z ⊥ (hf.bot_mem i j hij a b hab) _ _ (by simp))
  exact ⟨x, hx⟩

/-- Equality can be checked on a disjoint cover.
Source: Stacks Project Tag 00VL
(blueprint: lem-zl-disjoint-sheaf-sections).
Proof: separatedness for the generated covering sieve, using functoriality on
arrows factoring through a cover member. -/
theorem type_ext {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {W : C} {n : ℕ} {Y : Fin n → C}
    {f : ∀ i, Y i ⟶ W} (hf : J.IsDisjointCover f)
    (F : Sheaf J (Type w)) {x y : F.obj.obj (op W)}
    (h : ∀ i, F.obj.map (f i).op x = F.obj.map (f i).op y) : x = y := by
  apply Sheaf.isSeparated F W _ hf.ofArrows_mem
  rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
  simp only [op_comp, Functor.map_comp, types_comp_apply]
  rw [h i]

end CategoryTheory.GrothendieckTopology.IsDisjointCover
