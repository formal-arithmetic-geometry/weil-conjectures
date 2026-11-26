/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Enough injectives for modules on a ringed space

The category of sheaves of modules on a ringed space is abelian and has enough injectives.

## Implementation details

Module sheaves on `X` are `SheafOfModules` over the ring sheaf `moduleRings X` on the small site
of opens; `SheafOfModules.isGrothendieckAbelian` makes this a Grothendieck abelian category,
which has enough injectives.

## References

* [Stacks Project, Tags 01DI and 03DA](https://stacks.math.columbia.edu/tag/01DI)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/-- The category of module sheaves on any ringed space is abelian and has enough injectives:
every module sheaf embeds into an injective module sheaf. -/
theorem moduleSheaves_abelian_enoughInjectives (X : RingedSpace.{u}) :
    Nonempty (Abelian (SheafOfModules.{u} (moduleRings X))) ∧
    EnoughInjectives (SheafOfModules.{u} (moduleRings X)) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X)
  exact ⟨⟨inferInstance⟩, inferInstance⟩

end AlgebraicGeometry.RingedSpace
