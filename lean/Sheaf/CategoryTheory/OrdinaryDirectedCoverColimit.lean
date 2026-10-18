/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Ordinary colimits over a directed cover by full subcategories

Source: Stacks Project, Categories, Definition 002F (`definition-colimit`),
`literature/stacks-project/categories.tex`, lines 1310--1329; the agent-formulated
directed-cover argument in the DAG (blueprint: lem-coef-ordinary-directed-cover-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- Chosen ordinary colimits on a directed increasing full-subcategory cover assemble to
the chosen total colimit. The functor `D` has exactly the prescribed objects, recorded by
`e`; `eqToHom` only transports along these equalities. The two iff clauses characterize
its transition maps and its maps to the total colimit uniquely by the prescribed legs.
The equivalence identifies compatible families with cocones having vertex `H`, with its
inverse specified on every local leg. The final comparison is the canonical `colimit.desc`.

Source: Stacks Project, Categories, Definition 002F (`definition-colimit`), lines
1310--1329 (blueprint: lem-coef-ordinary-directed-cover-colimit).

Proof plan (all categorical universal properties use def-weil-pbc-category-colimit):
1. Restrict the cocone at stage `j` to stage `i`. Its unique factorization through the
   chosen colimit at `i` defines the transition. Uniqueness on local legs proves identity
   and composition, hence gives `D`. Restrict the total cocone similarly to obtain `v`;
   uniqueness proves its naturality and both iff characterizations.
2. For a compatible family and an object `c`, choose a stage containing `c` and compose
   its local leg with the family map. Two choices agree in a common upper stage.
   For an arrow, choose a common stage containing its endpoints; fullness puts the arrow
   in that stage, whose cocone equation proves naturality.
3. Conversely restrict a cocone to each stage and use its chosen colimit to factor it.
   Uniqueness proves compatibility and that the two constructions are inverse, giving
   the displayed equivalence with the specified inverse legs.
4. This bijection, natural in `H`, identifies maps from the total colimit with compatible
   families. Thus the cocone with legs `v` is colimiting, and its canonical comparison
   from `colimit D` is an isomorphism with those legs.
5. When `C` is empty all stage colimits are initial; when only a stage is empty its
   colimit is initial. The same universal properties apply without any nonemptiness
   condition on `C` or on its full subcategories. -/
theorem ordinary_directed_cover_colimit
    {I : Type u} [PartialOrder I] [Nonempty I]
    (hdir : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
    {C : Type u} [SmallCategory C]
    (S : I → ObjectProperty C) (hmono : Monotone S)
    (hcover : ∀ c : C, ∃ i : I, S i c)
    {A : Type v} [Category.{u} A] [HasColimitsOfSize.{u, u} A]
    (F : C ⥤ A)
    (s : ∀ i : I, Cocone ((S i).ι ⋙ F))
    (hs : ∀ i : I, IsColimit (s i))
    (t : Cocone F) (ht : IsColimit t) :
    ∃ (D : I ⥤ A) (e : ∀ i : I, D.obj i = (s i).pt)
      (v : D ⟶ (Functor.const I).obj t.pt),
      (∀ (i j : I) (hij : i ≤ j) (a : (s i).pt ⟶ (s j).pt),
        (∀ c : (S i).FullSubcategory,
          (s i).ι.app c ≫ a = (s j).ι.app ⟨c.obj, hmono hij c.obj c.property⟩) ↔
        a = eqToHom (e i).symm ≫ D.map (homOfLE hij) ≫ eqToHom (e j)) ∧
      (∀ (i : I) (a : (s i).pt ⟶ t.pt),
        (∀ c : (S i).FullSubcategory, (s i).ι.app c ≫ a = t.ι.app c.obj) ↔
        a = eqToHom (e i).symm ≫ v.app i) ∧
      Nonempty (IsColimit (⟨t.pt, v⟩ : Cocone D)) ∧
      (∀ H : A,
        ∃ E : { f : ∀ i : I, (s i).pt ⟶ H //
            ∀ (i j : I) (hij : i ≤ j),
              (eqToHom (e i).symm ≫ D.map (homOfLE hij) ≫ eqToHom (e j)) ≫ f j = f i }
            ≃ (F ⟶ (Functor.const C).obj H),
          ∀ (g : F ⟶ (Functor.const C).obj H) (i : I) (c : (S i).FullSubcategory),
            (s i).ι.app c ≫ (E.symm g).val i = g.app c.obj) ∧
      IsIso (colimit.desc D (⟨t.pt, v⟩ : Cocone D)) ∧
      (∀ i : I, colimit.ι D i ≫ colimit.desc D (⟨t.pt, v⟩ : Cocone D) = v.app i) := by
  sorry

end CategoryTheory.Limits
