/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Sections of a sheaf on a basis are the locally represented families of germs

Source: Stacks Project, Sheaves on Spaces, Section 009H, Lemma 009M
(blueprint: lem-weil-pbc-basis-sheaf-sections-germs).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopologicalSpace.Opens

/-- Source: Stacks Project, Section 009H, Lemma 009M
(blueprint: lem-weil-pbc-basis-sheaf-sections-germs).
Let `B` be an intersection-closed basis of `X` and `F : Bᵒᵖ ⥤ AddCommGrpCat` a presheaf of abelian
groups on `B` with unique gluing on every covering of a member of `B` by members of `B` (families
indexed by arbitrary types, including empty ones; `res` is the functor's restriction, `meet` the
intersection in `B`). The stalk at `x` is the colimit of `F` over the basis opens containing `x`
(def-weil-pbc-basis-presheaf-stalk, `colimit`, the germ maps are `colimit.ι`). Then for every
`U ∈ B` the map `s ↦ (s_x)_{x ∈ U}` is injective with image the families satisfying (*): every
`x ∈ U` has `V ∈ B` with `x ∈ V ≤ U` and `σ ∈ F(V)` with `t_y = σ_y` for all `y ∈ V`.

Proof:
1. Injectivity: if `s_x = s'_x` for all `x ∈ U`, then for each `x` there is a basis open
   `x ∈ W_x ≤ U` on which `s` and `s'` restrict to the same section (stalks are directed
   colimits). The `W_x` cover `U`, so uniqueness of gluing gives `s = s'`.
2. The image satisfies (*): take `V = U` and `σ = s`.
3. Conversely, given `t` with (*), choose for each `x ∈ U` a pair `(V_x, σ_x)`. On
   `V_x ∩ V_y` the restrictions of `σ_x` and `σ_y` have the same germs at every point, so by step 1
   applied to `V_x ∩ V_y` (in `B`) they are equal. The `V_x` cover `U`, so gluing gives `s` with
   `s|_{V_x} = σ_x`, hence `s_y = t_y` for all `y ∈ U`. -/
theorem sections_eq_locally_germ_families
    {X : Type u} [TopologicalSpace X] (B : Set (Opens X))
    (hB : IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (F : Bᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    let meet : B → B → B := fun U V ↦ ⟨U.val ⊓ V.val, hcap U V⟩
    let res : ∀ U V : B, V ≤ U → F.obj (op U) → F.obj (op V) :=
      fun _ _ h s ↦ (F.map (homOfLE h).op).hom s
    let stalk : X → AddCommGrpCat.{max u v} := fun x ↦
      colimit ((Subtype.mono_coe (fun U : B ↦ x ∈ U.val)).functor.op ⋙ F)
    let germ : ∀ (U : B) (x : X) (hx : x ∈ U.val), F.obj (op U) → stalk x :=
      fun U x hx s ↦
        (colimit.ι ((Subtype.mono_coe (fun U : B ↦ x ∈ U.val)).functor.op ⋙ F) (op ⟨U, hx⟩)).hom s
    (∀ (U : B) (I : Type w) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val →
      ∀ s : ∀ i, F.obj (op (V i).val),
        (∀ i j,
          res (V i).val (meet (V i).val (V j).val)
            (inf_le_left (a := (V i).val.val) (b := (V j).val.val)) (s i) =
          res (V j).val (meet (V i).val (V j).val)
            (inf_le_right (a := (V i).val.val) (b := (V j).val.val)) (s j)) →
        ∃! t : F.obj (op U), ∀ i, res U (V i).val (V i).property t = s i) →
    ∀ U : B,
      Function.Injective (fun (s : F.obj (op U)) (x : X) (hx : x ∈ U.val) ↦ germ U x hx s) ∧
      Set.range (fun (s : F.obj (op U)) (x : X) (hx : x ∈ U.val) ↦ germ U x hx s) =
        {t : ∀ x : X, x ∈ U.val → stalk x |
          ∀ (x : X) (hx : x ∈ U.val), ∃ (V : B) (hVU : V ≤ U), x ∈ V.val ∧
            ∃ σ : F.obj (op V), ∀ (y : X) (hy : y ∈ V.val), germ V y hy σ = t y (hVU hy)} := by
  sorry

end TopologicalSpace.Opens
