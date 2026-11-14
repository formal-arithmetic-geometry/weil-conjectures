/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- The isomorphism `Lf^*(O_Y[1]) ≅ O_Z[1]`, assuming `derivedPullback f` is monoidal.
(Stacks, Tag 06YJ) -/
theorem exists_derivedPullback_shifted_unit_iso
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    Nonempty ((derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧) := by
  obtain ⟨I, hI, hmap, hadd, hlim, hcolim, hres, E, hE, hEmap, hEadd,
    ε, hleft, htri, hε⟩ := derivedPullback_spec f
  obtain ⟨s, _⟩ := htri
  let : (derivedPullback f).CommShift ℤ := s
  exact ⟨((derivedPullback f).commShiftIso (1 : ℤ)).app _ ≪≫
    (shiftFunctor (schemeDerivedCategory Z) (1 : ℤ)).mapIso
      (Functor.Monoidal.εIso (derivedPullback f)).symm⟩

end AlgebraicGeometry
