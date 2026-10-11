/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Compatible truncated simplex families in a coskeleton

Source: Stacks Project, Simplicial Methods, Lemma 0183 (lemma-existence-cosk)
(blueprint: lem-weil-pbc-coskeleton-matching-tuples).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- Source: Stacks Project, Simplicial Methods, Lemma 0183 (lemma-existence-cosk)
(blueprint: lem-weil-pbc-coskeleton-matching-tuples).
An `(n - 1)`-coskeleton of the truncation of `K` exists. Maps into its degree `n` term
correspond naturally to compatible families indexed by all maps from degrees at most `n - 1`.
The canonical map corresponds to the family of simplicial operators of `K`.

Proof for stage 3:
1. Apply lem-weil-pbc-truncated-coskeleton-finite-limits to the truncation of `K` at `n - 1`.
   Its degree `j` term is the limit over the opposite truncated simplex slice over `[j]`.
   The projections at the identity maps in truncated degrees are isomorphisms: identity is
   terminal in the slice and initial in its opposite. The projection equations make these
   isomorphisms natural. Comparing them with the counit gives a natural automorphism `a` of
   the truncation (def-weil-pbc-simplicial-coskeleton, def-weil-pbc-simplicial-object).
2. By the limit universal property (def-galois-finite-limits-colimits), maps into the degree
   `n` limit correspond bijectively to compatible families. Postcomposition by `a` is a
   bijection of compatible families and yields the displayed counit formula. Both operations
   commute with precomposition in `W`, giving naturality.
3. The canonical morphism has truncated composite with the counit equal to the identity
   (def-weil-pbc-simplicial-coskeleton). Its simplicial naturality then identifies the
   corresponding family with `K.map α.op` (def-weil-pbc-simplicial-object). -/
theorem exists_coskeleton_matching_tuples
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (n : ℕ) (_hn : 1 ≤ n) :
    let m := n - 1
    let i := SimplexCategory.Truncated.inclusion m
    let V := (truncation m).obj K
    let F := fun W : C ↦
      {x : ∀ (k : SimplexCategory.Truncated m),
          (i.obj k ⟶ SimplexCategory.mk n) → (W ⟶ K.obj (op (i.obj k))) //
        ∀ (k' k : SimplexCategory.Truncated m) (ψ : k' ⟶ k)
          (α : i.obj k ⟶ SimplexCategory.mk n),
          x k α ≫ K.map (i.map ψ).op = x k' (i.map ψ ≫ α)}
    ∃ (L : SimplicialObject C) (ε : (truncation m).obj L ⟶ V),
      L.IsRightKanExtension ε ∧
      ∃ (c : K ⟶ L), (truncation m).map c ≫ ε = 𝟙 V ∧
      ∃ (e : ∀ W : C, (W ⟶ L _⦋n⦌) ≃ F W),
        (∀ (W : C) (h : W ⟶ L _⦋n⦌) (k : SimplexCategory.Truncated m)
          (α : i.obj k ⟶ SimplexCategory.mk n),
          (e W h).val k α = h ≫ L.map α.op ≫ ε.app (op k)) ∧
        (∀ (W' W : C) (g : W' ⟶ W) (h : W ⟶ L _⦋n⦌)
          (k : SimplexCategory.Truncated m) (α : i.obj k ⟶ SimplexCategory.mk n),
          (e W' (g ≫ h)).val k α = g ≫ (e W h).val k α) ∧
        (∀ (k : SimplexCategory.Truncated m) (α : i.obj k ⟶ SimplexCategory.mk n),
          (e (K _⦋n⦌) (c.app (op (SimplexCategory.mk n)))).val k α = K.map α.op) := by
  sorry

end CategoryTheory.SimplicialObject
