/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Mathlib.CategoryTheory.Sites.Over

/-! # Gluing maps on slice sites

Source: Stacks Project, Sites, Tag 04TQ, lemma-glue-maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Compatible natural maps on slices glue uniquely to a natural map.

Source: Stacks Project, Sites, Tag 04TQ, lemma-glue-maps
(blueprint: lem-trf-over-sheaf-map-gluing).

Proof: for V → U pull back the covering to V ×_U X_a → V. Apply each local
map to the restrictions of a section of F. Their values agree on pairwise
pullbacks by the displayed compatibility, using the canonical identity-arrow
identification of the two composites to U. The sheaf axiom for G gives a unique
section over V. Uniqueness of this amalgamation proves naturality in V. On an
object over X_a, restrict further along its graph into V ×_U X_a; the local
formula follows by naturality of the local map. Two maps with the prescribed
local formulas have the same restrictions on every pulled-back covering, hence
are equal by separatedness. The empty cover is valid: all section sets of G
are then singletons. No algebraic structure or cocycle is required. -/
theorem overSheafMapGluing
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C) {I : Type (max u v w)}
    (U : C) (X : I → C) (f : ∀ a, X a ⟶ U)
    (hcov : Sieve.ofArrows X f ∈ J U)
    (F G : Sheaf (J.over U) (Type (max u v w)))
    (s : ∀ a, (Over.map (f a)).op ⋙ F.obj ⟶ (Over.map (f a)).op ⋙ G.obj)
    (hs : ∀ (a b : I) (V : Over (pullback (f a) (f b)))
      (x : F.obj.obj (op ((Over.map (pullback.snd (f a) (f b)) ⋙
        Over.map (f b)).obj V))),
      G.obj.map
        (((Over.mapComp _ _).symm ≪≫
          Over.mapCongr _ _ (pullback.condition (f := f a) (g := f b)) ≪≫
          Over.mapComp _ _).hom.app V).op ((s b).app _ x) =
        (s a).app _ (F.obj.map
          (((Over.mapComp _ _).symm ≪≫
            Over.mapCongr _ _ (pullback.condition (f := f a) (g := f b)) ≪≫
            Over.mapComp _ _).hom.app V).op x)) :
    ∃! t : F.obj ⟶ G.obj,
      ∀ (a : I) (V : (Over (X a))ᵒᵖ)
        (x : F.obj.obj ((Over.map (f a)).op.obj V)),
        t.app _ x = (s a).app V x := by
  sorry

end CategoryTheory
