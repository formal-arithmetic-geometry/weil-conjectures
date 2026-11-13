/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.OpenUnionModuleImagePullbackCore

/-! # Sheaf gluing over an arbitrary open union

## References

* [Stacks, Tags 01EB and 08BV]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- The direct-image restriction square for a union is a pullback, for any module sheaf
(Stacks, Tags 01EB and 08BV). -/
theorem schemeOpenUnionModuleImage_isPullback
    (X : Scheme.{u}) (U V : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    IsPullback
      ((schemeOpenModuleImageRestriction X
        (homOfLE (le_sup_left : U ≤ U ⊔ V))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (le_sup_right : V ≤ U ⊔ V))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M) := by
  apply schemeOpenUnionModuleImage_isPullback_of_sectionwise X U V M
  exact schemeOpenUnionModuleImage_sectionwise_gluing X U V M

end AlgebraicGeometry
