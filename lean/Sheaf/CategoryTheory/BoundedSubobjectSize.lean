/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Objects with bounded subobject size

Source: Stacks Project, `injectives.tex`, Lemma `lemma-set-iso-classes-bounded-size`
(blueprint: lem-pur-kinjective-set-iso-classes-bounded-size).
-/

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

/-- In a Grothendieck abelian category with generator `U`, each object with at most `κ`
subobjects is a quotient of a coproduct of at most `κ` copies of `U`, and the isomorphism
classes of such objects form a set. Size is the cardinality of the small model of the
subobject lattice; `Skeleton` identifies objects exactly up to isomorphism.

Source: Stacks Project, `injectives.tex`, Lemma `lemma-set-iso-classes-bounded-size`
(blueprint: lem-pur-kinjective-set-iso-classes-bounded-size).

Proof:
1. For each proper subobject `M'` of `M`, choose a map `U ⟶ M` with image not contained
   in `M'`, using the generator property of `def-sp-grothendieck-abelian`. The induced map
   from the coproduct is epi: otherwise its image is a proper subobject `N`, and the
   summand chosen for `N` contradicts that choice. The index set has size at most `κ`.
2. For each cardinal `λ ≤ κ`, the coproduct of `λ` copies of `U` exists by
   `def-sp-grothendieck-abelian`. Its subobjects form a set by
   `lem-pur-kinjective-set-of-subobjects`; each quotient is determined up to isomorphism
   by its kernel. The cardinals at most `κ` form a set, so these quotient classes do too.
3. By step 1 every bounded-size object is among these quotients, proving the second clause. -/
theorem bounded_subobject_size_quotient_and_small_iso_classes
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (U : C) (_hU : IsSeparator U) (κ : Cardinal.{v}) :
    (∀ M : C, Cardinal.mk (Shrink.{v} (Subobject M)) ≤ κ →
      ∃ (I : Type v), Cardinal.mk I ≤ κ ∧
        ∃ p : (∐ fun _ : I ↦ U) ⟶ M, Epi p) ∧
    Small.{v} (Skeleton (ObjectProperty.FullSubcategory
      (fun M : C ↦ Cardinal.mk (Shrink.{v} (Subobject M)) ≤ κ))) := by
  sorry

end CategoryTheory
