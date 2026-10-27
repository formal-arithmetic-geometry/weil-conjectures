/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.AlgebraicGeometry.StacksBigSiteCategory
public import Mathlib.CategoryTheory.Skeletal

/-! # Bounded-size representatives in a chosen big-site category

Source: Stacks Project, sets.tex, Tag 000J (lemma-construct-category), clause (2),
equation-bound and section-categories-schemes; topologies.tex, Tag 021R
(definition-big-fppf-site), clause (2)
(blueprint: lem-sfb-big-site-bounded-size-representative).

The first statement uses the chosen full category itself. The second gives the same
conclusion in any chosen full skeleton, as permitted by the size convention. Topology
and coverings play no role: the admissibility of the already chosen underlying category
is precisely `IsStacksBigSiteCategory`, required by Tag 021R (2).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A chosen admissible big-site category contains representatives of all schemes of the
specified bounded size, and contains a representative of every empty scheme.

Source: Stacks Project, sets.tex, Tag 000J (2), equation-bound and
section-categories-schemes; topologies.tex, Tag 021R (2)
(blueprint: lem-sfb-big-site-bounded-size-representative).

Proof plan: unpack clause (2) of `IsStacksBigSiteCategory` for the fixed category,
substitute `S = T` and `W = Z`, and reverse the resulting isomorphism. No membership
of `Z` in the chosen category is assumed. If `Z` is empty, its affine-open set has
at most one element and each ring of sections has one element, so its cardinal size
is aleph zero. Every `T` has size at least aleph zero, and its successor cardinal is
at most the displayed bound. Thus the same clause applies without a size hypothesis
for an empty `Z`. -/
theorem exists_bounded_size_representative
    (code : Scheme.{u} ↪ ZFSet.{u + 1}) (S₀ : Set Scheme.{u}) (α : Ordinal.{u + 1})
    (hα : IsStacksBigSiteCategory code S₀ α) (T : StacksBigSiteCategory code α) :
    (∀ Z : Scheme.{u},
      Z.cardinalSize ≤ max (T.obj.cardinalSize ^ Cardinal.aleph0)
        (Order.succ T.obj.cardinalSize) →
      ∃ Z₀ : StacksBigSiteCategory code α, Nonempty (Z₀.obj ≅ Z)) ∧
    (∀ Z : Scheme.{u}, IsEmpty Z →
      ∃ Z₀ : StacksBigSiteCategory code α, Nonempty (Z₀.obj ≅ Z)) := by
  sorry

/-- The bounded-size and empty-scheme representative conclusions hold in the originally
chosen full skeleton as well.

Source: Stacks Project, sets.tex, Tag 000J (2), under the full-skeleton convention of
`def-weil-size-convention`; topologies.tex, Tag 021R (2)
(blueprint: lem-sfb-big-site-bounded-size-representative).

Proof plan: the image of `T` is an object of the same admissible full category.
Apply clause (2) there with this image and `Z`, reversing the obtained isomorphism.
Since `F` exhibits the chosen category as a full skeleton, choose a skeleton object
whose image is isomorphic to that representative, and compose these scheme
isomorphisms. The empty case follows from size equal to aleph zero, exactly as in
the full-category case. No replacement of the chosen category or membership of `Z`
in it is used. -/
theorem exists_bounded_size_representative_in_skeleton
    (code : Scheme.{u} ↪ ZFSet.{u + 1}) (S₀ : Set Scheme.{u}) (α : Ordinal.{u + 1})
    (hα : IsStacksBigSiteCategory code S₀ α)
    (C : Type v) [Category.{w} C] (F : C ⥤ StacksBigSiteCategory code α)
    (hC : IsSkeletonOf (StacksBigSiteCategory code α) C F) (T : C) :
    (∀ Z : Scheme.{u},
      Z.cardinalSize ≤ max ((F.obj T).obj.cardinalSize ^ Cardinal.aleph0)
        (Order.succ (F.obj T).obj.cardinalSize) →
      ∃ Z₀ : C, Nonempty ((F.obj Z₀).obj ≅ Z)) ∧
    (∀ Z : Scheme.{u}, IsEmpty Z → ∃ Z₀ : C, Nonempty ((F.obj Z₀).obj ≅ Z)) := by
  sorry

end AlgebraicGeometry.Scheme
