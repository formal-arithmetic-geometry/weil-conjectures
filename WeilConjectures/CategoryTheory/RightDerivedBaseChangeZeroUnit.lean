/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.RightDerivedBaseChangeSingleUnitHomology

/-!
# The degree-zero unit equation for derived base change

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), and the unit
characterization of derived base change.
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

omit [PreservesFiniteLimits G] [PreservesFiniteLimits G'] in
/-- The classical degree-zero base-change map respects the augmentations from the
underived functors.

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), applied to the defining
unit equation of `rightDerivedFunctorPlusBaseChange`. -/
theorem rightDerivedBaseChange_zero_unit (e : G ⋙ γ ⟶ β ⋙ G') (Y : B) :
    γ.map (G.toRightDerivedZero.app Y) ≫ (rightDerivedBaseChange e 0).app Y =
      e.app Y ≫ G'.toRightDerivedZero.app (β.obj Y) := by
  rw [rightDerivedBaseChange_app,
    ← rightDerivedPlusSingleUnitHomology_comp_comparison G Y,
    ← rightDerivedPlusSingleUnitHomology_comp_comparison G' (β.obj Y)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← γ.map_comp_assoc
    ((G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app Y)
    ((G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).inv.app Y),
    Iso.hom_inv_id_app, γ.map_id, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫
      (G'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app
        (β.obj Y)) (rightDerivedBaseChange_single_unit_homology e Y)

end CategoryTheory.Functor
