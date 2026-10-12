/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-!
# The homology unit equation for derived base change

Source: `rightDerivedFunctorPlusBaseChange_fac` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`
(blueprint: lem-sbc-right-derived-base-change-single-unit-homology).
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

/-- Degree-zero homology of the derived base-change unit equation on single complexes.

Source: `rightDerivedFunctorPlusBaseChange_fac` in `PlusBaseChange.lean`, together with
`mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor` in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
(blueprint: lem-sbc-right-derived-base-change-single-unit-homology).

Proof: evaluate rightDerivedFunctorPlusBaseChange_fac on the homotopy single complex
Y[0]. Expand rightDerivedFunctorPlusBaseChangeAux: its associators are identity maps,
and its comparison maps identify the levelwise transformation with e.app Y on single
complexes. Transport along the isomorphism from Qh of the homotopy single complex to
the derived single complex. Naturality of base change gives the derived unit equation
on Y[0], with the beta single-complex comparison on the target. Apply degree-zero
homology. Naturality of gamma.mapDerivedCategoryPlusHomologyFunctorIso moves the source
unit across the exact-functor homology comparison. The single-complex homology
comparison, using mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor,
identifies the transformation on single complexes with e.app Y. These
identifications give the equation below. No left exactness of G or G' is needed:
only beta and gamma are exact, and the equation is the defining derived-unit equation. -/
theorem rightDerivedBaseChange_single_unit_homology (e : G ⋙ γ ⟶ β ⋙ G') (Y : B) :
    γ.map (G.rightDerivedPlusSingleUnitHomology Y) ≫
      (γ.mapDerivedCategoryPlusHomologyFunctorIso (0 : ℕ)).hom.app
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y)) ≫
      (DerivedCategory.Plus.homologyFunctor C' (0 : ℕ)).map
        ((rightDerivedFunctorPlusBaseChange e).app
          ((DerivedCategory.Plus.singleFunctor B 0).obj Y)) ≫
      (DerivedCategory.Plus.homologyFunctor C' (0 : ℕ)).map
        (G'.rightDerivedFunctorPlus.map
          ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y)) =
    e.app Y ≫ G'.rightDerivedPlusSingleUnitHomology (β.obj Y) := by sorry

end CategoryTheory.Functor
