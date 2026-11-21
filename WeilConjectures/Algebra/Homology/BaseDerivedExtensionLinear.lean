/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionScalar

/-!
# Linear total derived extension of scalars

## References

* Stacks Project, Tag 06Y6.
-/

@[expose] public section

set_option autoImplicit false

universe uR uB v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (B : Type uB) [CommRing R] [CommRing B]
  [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} B)]

-- Derived scalar extension is expressed in a common module universe.
/-- The universal total left derived extension of scalars exists, is additive, and acts on
homology by the scalar `algebraMap R B r` for multiplication by `r`. -/
theorem exists_baseDerivedExtension_linear
    [(extendScalars.{_, _, max uR uB v} (algebraMap R B)).Additive] :
    ∃ (derived : DerivedCategory (ModuleCat.{max uR uB v} R) ⥤
        DerivedCategory (ModuleCat.{max uR uB v} B))
      (counit : DerivedCategory.Qh ⋙ derived ⟶
        (extendScalars.{_, _, max uR uB v} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      derived.IsLeftDerivedFunctor counit
        (HomotopyCategory.quasiIso (ModuleCat.{max uR uB v} R) (.up ℤ)) ∧
      derived.Additive ∧
      ∀ (i : ℤ) (E : CochainComplex (ModuleCat.{max uR uB v} R) ℤ) (r : R),
        (DerivedCategory.homologyFunctor (ModuleCat.{max uR uB v} B) i).map
          (derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient _ _).map (r • 𝟙 E)))) =
        algebraMap R B r • 𝟙
          ((DerivedCategory.homologyFunctor (ModuleCat.{max uR uB v} B) i).obj
            (derived.obj (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient _ _).obj E)))) := by
  obtain ⟨L, ε, hL, ⟨c, htri⟩, hres⟩ := exists_baseDerivedExtension_resolution R B
  let := c
  let := htri
  refine ⟨L, ε, hL, inferInstance, ?_⟩
  exact baseDerivedExtension_scalar R B L ε hres

end ModuleCat
