/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G1
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic

/-!
# Gluing on cofinal coverings of a basis

Source: Stacks Project, Sheaves on Spaces, Tags 009J, 009K and 009L
(blueprint: lem-weil-pbc-basis-sheaf-cofinal-coverings).
-/

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite TopologicalSpace

namespace TopologicalSpace.Opens

/-- Source: Stacks Project, Tags 009K and 009L.
(blueprint: lem-weil-pbc-basis-sheaf-cofinal-coverings)
A presheaf of sets on an intersection-closed basis glues on all coverings if it glues on
cofinally many coverings. Families are indexed by arbitrary types, including empty types.
The predicate `C U I V` selects the cofinal coverings; it is only used when `V` covers `U`.
The local notation `meet` is intersection in the basis, and `res` is the functor's restriction.

Proof:
1. Refine an arbitrary covering `V` of `U` by a selected covering `W`, with refinement map
   `α`. All pairwise intersections belong to the basis by the intersection hypothesis.
2. Sections agreeing on `V` agree on `W` by functoriality. Uniqueness of gluing on `W`
   therefore gives uniqueness on every covering of every basis member.
3. Given a compatible family `s`, restrict `s (α j)` to `W j`. The resulting family is
   compatible on intersections by transitivity of restrictions and compatibility of `s`.
   Gluing on the selected covering gives a section `t` over `U`.
4. For each `i`, the intersections of `V i` with all `W j` cover `V i`. The restrictions
   of `t` and `s i` agree there by compatibility and functoriality. Apply the uniqueness
   from step 2 over `V i` to obtain that `t` restricts to `s i`.
5. Step 4 gives existence and step 2 gives uniqueness on the original covering.
For the empty covering of the empty basis member, a refinement has empty index type,
and the selected gluing condition forces the set of sections to have exactly one element.
No subsidiary nodes are used: all five steps of the DAG proof are elementary. -/
theorem gluing_of_cofinal_coverings
    {X : Type u} [TopologicalSpace X] (B : Set (Opens X))
    (hB : IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (F : Bᵒᵖ ⥤ Type v)
    (C : ∀ U : B, ∀ I : Type w, (I → {V : B // V ≤ U}) → Prop) :
    let meet : B → B → B := fun U V ↦ ⟨U.val ⊓ V.val, hcap U V⟩
    let res : ∀ U V : B, V ≤ U → F.obj (op U) → F.obj (op V) :=
      fun _ _ h ↦ F.map (homOfLE h).op
    (∀ (U : B) (I : Type w) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val →
      ∃ (J : Type w) (W : J → {Z : B // Z ≤ U}),
        (⨆ j, (W j).val.val) = U.val ∧ C U J W ∧
        ∃ α : J → I, ∀ j, (W j).val ≤ (V (α j)).val) →
    (∀ (U : B) (I : Type w) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val → C U I V →
      ∀ s : ∀ i, F.obj (op (V i).val),
        (∀ i j,
          res (V i).val (meet (V i).val (V j).val)
            (inf_le_left (a := (V i).val.val) (b := (V j).val.val)) (s i) =
          res (V j).val (meet (V i).val (V j).val)
            (inf_le_right (a := (V i).val.val) (b := (V j).val.val)) (s j)) →
        ∃! t : F.obj (op U), ∀ i, res U (V i).val (V i).property t = s i) →
    ∀ (U : B) (I : Type w) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val →
      ∀ s : ∀ i, F.obj (op (V i).val),
        (∀ i j,
          res (V i).val (meet (V i).val (V j).val)
            (inf_le_left (a := (V i).val.val) (b := (V j).val.val)) (s i) =
          res (V j).val (meet (V i).val (V j).val)
            (inf_le_right (a := (V i).val.val) (b := (V j).val.val)) (s j)) →
        ∃! t : F.obj (op U), ∀ i, res U (V i).val (V i).property t = s i := by
  sorry

end TopologicalSpace.Opens
