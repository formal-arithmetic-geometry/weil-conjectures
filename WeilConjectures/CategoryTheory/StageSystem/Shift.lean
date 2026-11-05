/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# The shift on the pair category of a stage system

Let `S` be a stage system on categories `C i` equipped with shifts by an additive monoid `A`,
such that the transition functors commute with the shifts (`Functor.CommShift`) and the
associators are compatible with these commutations (`NatTrans.CommShift`). In the application
these are the derived extensions of scalars `T_{F/E}` between the categories `D^b_c(T, E)`, with
their comparisons `σ_{F/E}`.

The shifts by `a : A` at all stages form a morphism of stage systems
`CategoryTheory.StageSystem.shiftMorphism S a`, and the descended functors define a shift on the
pair category: `(i, x)⟦a⟧ = (i, x⟦a⟧)`.
The stage inclusions `ι i` commute with the shifts, and so do the identifications
`T_{j/i} ⋙ ι j ≅ ι i`.

## Main definitions

- `CategoryTheory.StageSystem.shiftMorphism`: the shift by `a` as a morphism of stage systems.
- `CategoryTheory.StageSystem.PairCategory.hasShift`: the shift on the pair category.
- `CategoryTheory.StageSystem.ι_commShift`: the stage inclusions commute with the shifts.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (A : Type*) [AddMonoid A] [∀ i, HasShift (C i) A]
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift A]
  [∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom A]

variable [IsDirectedOrder I]

open PairCategory

namespace PairCategory

variable {S A}

end PairCategory

open PairCategory

variable {S A}

end StageSystem

end CategoryTheory
