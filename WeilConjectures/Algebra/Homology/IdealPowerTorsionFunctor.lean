/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-!
# The ideal-power torsion functor

## Implementation details

The functor is defined directly as the primary component submodule; no object is selected from an
existence theorem.

## References

* Stacks Project, Tag 0BJA (the functor defining algebraic local cohomology)
-/

@[expose] public section

universe u
open CategoryTheory

namespace ModuleCat

/-- The submodule of elements annihilated by some power of `J`, with maps obtained
by restricting the original linear maps. -/
def idealPowerTorsion {R : Type u} [CommRing R] (J : Ideal R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Ideal.primaryComponent M J)
  map f := ModuleCat.ofHom (Ideal.primaryComponent.map J f.hom)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- Restriction to the ideal-power torsion submodules preserves addition of maps. -/
instance idealPowerTorsion_additive {R : Type u} [CommRing R] (J : Ideal R) :
    (idealPowerTorsion J).Additive where
  map_add := by
    intro M N f g
    ext x
    rfl

end ModuleCat
