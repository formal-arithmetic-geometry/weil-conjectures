/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.SixFunctors.BaseChange.Derived

/-!
# The degree-zero unit equation for derived base change

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), and the unit
characterization of derived base change (blueprint: lem-sbc-right-derived-base-change-zero-unit).
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives B] [EnoughInjectives B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteLimits G']
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

/-- The classical degree-zero base-change map respects the augmentations from the
underived functors.

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), applied to the defining
unit equation of `rightDerivedFunctorPlusBaseChange`.
(blueprint: lem-sbc-right-derived-base-change-zero-unit).

Proof:
1. Represent `Y[0]` by a nonnegative injective resolution `Y → I`. The defining equation
   `rightDerivedFunctorPlusBaseChange_fac` expresses derived base change after the
   augmentation as the levelwise transformation `e`, followed by the target augmentation.
2. Apply degree-zero homology. The comparisons in `rightDerivedBaseChange` identify
   this homology with the classical zeroth right derived functors; exactness of `β` and
   `γ` identifies their images of cycles and boundaries with cycles and boundaries of
   their image complexes.
3. In a nonnegative complex there are no degree-zero boundaries. Thus the augmentation
   on homology is the map induced from `G(Y) → G(I⁰)` into the kernel of `G(d⁰)`, which is
   precisely `G.toRightDerivedZero`; the same assertion holds for `G'` and `β(Y)`.
   Naturality of `e` with the resolution augmentation identifies the two composites.
   These are the two sides of the asserted equality. -/
theorem rightDerivedBaseChange_zero_unit (e : G ⋙ γ ⟶ β ⋙ G') (Y : B) :
    γ.map (G.toRightDerivedZero.app Y) ≫ (rightDerivedBaseChange e 0).app Y =
      e.app Y ≫ G'.toRightDerivedZero.app (β.obj Y) := by
  sorry

end CategoryTheory.Functor
