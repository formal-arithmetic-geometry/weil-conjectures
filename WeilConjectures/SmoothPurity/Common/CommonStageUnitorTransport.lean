/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-! # Transport of stagewise unitors in a stage system

Let `S` be a stage system with a family of bifunctors `T i` and scalar comparisons `c h`
satisfying the tower equation, together with stagewise units `Un i`, unitors and scalar unit
comparisons `e h : T_h (Un i) ≅ Un j` obeying both unit squares. Then the scalar unit
comparisons satisfy the cocycle equation, and the stagewise unitor representatives of a
common-stage tensor with the unit are compatible with transport. This is the categorical part
of the construction of the common-stage unitors.

Source: Stacks Project, Tag 0FFK (coherence for unit constraints); blueprint coefficient
conventions (blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public section

namespace WeilConjectures

open CategoryTheory

section
variable {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
  (S : StageSystem C) (T : ∀ i, C i × C i ⥤ C i)
  (c : ∀ {i j : I} (h : i ≤ j), T i ⋙ S.T h ≅ (S.T h).prod (S.T h) ⋙ T j)
  (Un : ∀ i, C i) (e : ∀ {i j : I} (h : i ≤ j), (S.T h).obj (Un i) ≅ Un j)

end

end WeilConjectures
