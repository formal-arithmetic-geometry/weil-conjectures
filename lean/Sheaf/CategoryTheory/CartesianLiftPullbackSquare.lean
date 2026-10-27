/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Pullback squares from strongly cartesian lifts

Source: Stacks Project, Categories, Tag 06N4,
lemma-strongly-cartesian-fibre-product and its proof
(blueprint: lem-sfb-cartesian-lift-pullback-square).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor

/-- A strongly cartesian lift of the second projection of a specified base pullback,
with the first cospan arrow strongly cartesian, determines a unique comparison arrow
and a pullback square in the total category.

Source: Stacks Project, Categories, Tag 06N4,
lemma-strongly-cartesian-fibre-product and its proof
(blueprint: lem-sfb-cartesian-lift-pullback-square).

Proof:
1. The base pullback equation gives p(g a) = p(f) piX. Strong cartesianness of f
   gives the unique b over piX satisfying f b = g a.
2. Given h : t → x and k : t → z with f h = g k, the base pullback gives the
   unique q : p(t) → P with projections p(h), p(k). Strong cartesianness of a
   gives l : t → w over q with a l = k.
3. Both b l and h lie over p(h) and have the same composite with f. Uniqueness
   for the strongly cartesian arrow f gives b l = h.
4. Any other factorization l' has base map q by both base projection identities
   and base pullback uniqueness. Uniqueness for the strongly cartesian arrow a
   then gives l' = l. Thus w is the pullback, with its given strongly cartesian
   projection a and its given image object P. -/
theorem cartesian_lift_pullback_square
    {S : Type u₁} {C : Type u₂} [Category.{v₁} S] [Category.{v₂} C]
    (p : S ⥤ C) {x y z w : S} (f : x ⟶ y) (g : z ⟶ y)
    [p.IsStronglyCartesian (p.map f) f]
    {P : C} (piX : P ⟶ p.obj x) (piZ : P ⟶ p.obj z)
    (hP : IsPullback piX piZ (p.map f) (p.map g))
    (a : w ⟶ z) [p.IsStronglyCartesian piZ a] :
    ∃ b : w ⟶ x, p.IsHomLift piX b ∧ b ≫ f = a ≫ g ∧
      (∀ b' : w ⟶ x, p.IsHomLift piX b' → b' ≫ f = a ≫ g → b' = b) ∧
      IsPullback b a f g := by
  sorry

end CategoryTheory.Functor
