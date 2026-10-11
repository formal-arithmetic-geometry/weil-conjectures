/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Sheaf.CategoryTheory.BoundedSubobjectSize

/-!
# Bounded-size subobjects surjecting onto a quotient

Source: Stacks Project, `injectives.tex`, Lemma `lemma-surjection-bounded-size`
(blueprint: lem-pur-kinjective-surjection-bounded-size).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Let `|X| = #(Subobject X)` be the size of an object and `c(λ)` the size of the
coproduct of `λ` copies of the generator `U`.  Every surjection `π : M ⟶ N` has a
subobject `M' ⊆ M` that still surjects onto `N` and whose size is at most `c(|N|)`.

Source: Stacks Project, `injectives.tex`, Lemma `lemma-surjection-bounded-size`
(blueprint: lem-pur-kinjective-surjection-bounded-size).

Proof:
1. For every proper subobject `N'` of `N`, the inverse image under `π` is proper,
   so the generator gives a map from `U` to `M` whose composite with `π` does not
   factor through `N'` (`def-sp-grothendieck-abelian`).
2. Take the image `M'` of the coproduct of these maps.  Its subobjects inject
   into those of the coproduct, which is a summand of the coproduct of `|N|`
   copies of `U`; hence its size is at most `c(|N|)`, using
   `lem-pur-kinjective-set-iso-classes-bounded-size` and
   `def-sp-grothendieck-abelian`.
3. If the image of `M'` in `N` were proper, the corresponding summand would
   factor through that proper subobject, contradicting the generator choice in step 1
   (`def-sp-grothendieck-abelian`). -/
theorem exists_subobject_surjecting_bounded_size
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (U : C) (_hU : IsSeparator U) (M N : C) (π : M ⟶ N) [Epi π] :
    ∃ (M' : C) (ι : M' ⟶ M), Mono ι ∧ Epi (ι ≫ π) ∧
      Cardinal.mk (Shrink.{v} (Subobject M')) ≤
        Cardinal.mk (Shrink.{v} (Subobject
          (∐ fun _ : (Cardinal.mk (Shrink.{v} (Subobject N))).out => U))) := by
  sorry

end CategoryTheory
