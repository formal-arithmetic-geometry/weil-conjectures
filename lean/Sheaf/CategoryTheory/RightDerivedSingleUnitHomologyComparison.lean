/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
/-!
# The derived unit and the classical degree-zero augmentation

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), and the unit
characterization of derived base change
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison).
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive]

/-- The unit on an object placed in degree zero, using the single-complex comparisons.

Source: `rightDerivedFunctorPlusUnit` and `mapHomotopyCategoryPlusSingleFunctorQhObjIso`
in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison). -/
noncomputable def rightDerivedPlusSingleUnit (Y : B) :
    (DerivedCategory.Plus.singleFunctor C 0).obj (G.obj Y) ⟶
      G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y) :=
  (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 Y).inv ≫
    G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor B 0).obj Y) ≫
    G.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.ι.preimageIso
        (X := (DerivedCategory.Plus.singleFunctor B 0).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj Y))
        ((DerivedCategory.singleFunctorIsoCompQ B 0).app Y ≪≫
          (DerivedCategory.quotientCompQhIso B).symm.app _)).inv

/-- Degree-zero homology of the derived unit on a single complex.

Source: the preceding unit and `DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso`
in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`.
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison). -/
noncomputable def rightDerivedPlusSingleUnitHomology (Y : B) :
    G.obj Y ⟶ (DerivedCategory.Plus.homologyFunctor C 0).obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y)) :=
  (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (G.obj Y) ≫
    (DerivedCategory.Plus.homologyFunctor C 0).map (G.rightDerivedPlusSingleUnit Y)

/-- The single-complex homology comparison identifies the derived unit with the
classical augmentation.

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), and the definitions of
`homologyRightDerivedFunctorPlusObjSingleFunctorIso` and `toRightDerivedZero`.
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison).

Proof: choose the injective resolution of Y used in both definitions. Naturality of the
right-derived unit along the resolution augmentation identifies the unit on Y[0] with
its map into the resolution followed by the unit on that resolution. The latter unit
is invertible, and cancels with its inverse in the definition of the single-complex
comparison. Apply homologyFunctorObjQIso naturality to the remaining resolution map.
The embedding from natural-number complexes to integer complexes preserves degree-zero
homology. Under this identification the remaining map is the lift of G applied to the
resolution augmentation into degree-zero cycles, followed by isoHomologyπ₀. This is
exactly InjectiveResolution.toRightDerivedZero', and composing isoRightDerivedObj.inv
gives G.toRightDerivedZero.app Y. -/
theorem rightDerivedPlusSingleUnitHomology_comp_comparison (Y : B) :
    G.rightDerivedPlusSingleUnitHomology Y ≫
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app Y =
    G.toRightDerivedZero.app Y := by sorry

end CategoryTheory.Functor
