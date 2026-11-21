/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitMono
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitEpi
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

/-! # Invertibility of the open extension unit

## References

* Stacks Project, Sheaves, Tag 00A7 (4); Modules on Sites, Tag 03DI
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- The unit of the chosen extension-by-zero/restriction adjunction is an isomorphism. -/
theorem moduleExtensionByZero_unit_isIso (X : RingedSpace.{u}) (W : Opens X)
    (G : SheafOfModules.{u} ((moduleRings X).over W)) :
    IsIso ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app G)
    := by
  let f := (Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app G
  have : Mono f := moduleExtensionByZero_unit_mono X W G
  have : Epi f := moduleExtensionByZero_unit_epi X W G
  exact isIso_of_mono_of_epi f

end AlgebraicGeometry
