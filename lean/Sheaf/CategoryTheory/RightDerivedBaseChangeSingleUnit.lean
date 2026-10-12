/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-!
# The derived unit equation for base change on single complexes

Source: `rightDerivedFunctorPlusBaseChange_fac` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`
(blueprint: lem-sbc-right-derived-base-change-single-unit).
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
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

/-- The derived base-change equation on single complexes, before taking homology.

Source: `rightDerivedFunctorPlusBaseChange_fac` in `PlusBaseChange.lean`.
(blueprint: lem-sbc-right-derived-base-change-single-unit).

Proof: evaluate the defining base-change unit equation on the homotopy single
complex Y[0]. Expand the auxiliary transformation. The composition comparisons
identify the transformation induced by e with the single-complex map of e(Y).
Transport the source and target along the canonical isomorphisms from Qh of
homotopy single complexes to derived single complexes. Naturality of the derived
base-change transformation moves this transport to its target; naturality of the
unit for G' identifies the resulting map with its unit on beta(Y)[0]. The exact
functor comparisons for gamma and beta supply the displayed single-complex
comparison maps. This yields the equation without any left-exactness assumption
on G or G'. -/
theorem rightDerivedBaseChange_single_unit (e : G ⋙ γ ⟶ β ⋙ G') (Y : B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedPlusSingleUnit Y) ≫
      (rightDerivedFunctorPlusBaseChange e).app
        ((DerivedCategory.Plus.singleFunctor B 0).obj Y) ≫
      G'.rightDerivedFunctorPlus.map
        ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y) =
    (γ.mapDerivedCategoryPlusSingleFunctor 0).hom.app (G.obj Y) ≫
      (DerivedCategory.Plus.singleFunctor C' 0).map (e.app Y) ≫
      G'.rightDerivedPlusSingleUnit (β.obj Y) := by sorry

end CategoryTheory.Functor
