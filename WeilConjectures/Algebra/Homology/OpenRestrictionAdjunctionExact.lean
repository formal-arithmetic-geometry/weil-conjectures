/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact

/-! # Exact extension by zero and restriction on a ringed space

Restriction to an open of a ringed space is exact and has an exact left adjoint, extension by
zero.

## References

* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS) (proof), citing
  Tag 00A7 and Tag 01AK
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For an open `U` of a ringed space `X`, restriction
`j⁻¹ = SheafOfModules.overFunctor (moduleRings X) U : Mod(O_X) ⥤ Mod(O_U)` is exact, and
extension by zero `j_!` (the extension-by-zero presheaf followed by module
sheafification) is exact and left adjoint to it: `j_! ⊣ j⁻¹`. Exactness is preservation
of finite limits and finite colimits. -/
theorem open_restriction_adjunction_exact (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) ∧
      PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) ∧
      PreservesFiniteLimits
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ∧
      PreservesFiniteColimits
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ∧
      Nonempty
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj) ⊣
          SheafOfModules.overFunctor.{u} (moduleRings X) U) := by
  -- Specialize the localized ringed-site theorem (Stacks, Tags 03DI and 03DJ).
  -- The covering precoverage generates the original topology, so both module
  -- categories and the extension-by-zero construction are the stated ones.
  have hJ : (Opens.grothendieckTopology X).toPrecoverage.toGrothendieck =
      Opens.grothendieckTopology X := by
    apply le_antisymm
    · exact GrothendieckTopology.toGrothendieck_toPrecoverage_le _
    · intro V S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
  let P (J : GrothendieckTopology (Opens X)) (O : Sheaf J CommRingCat.{u}) :=
    let R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} R U) ∧
      PreservesFiniteColimits (SheafOfModules.overFunctor.{u} R U) ∧
      PreservesFiniteLimits (SheafOfModules.extensionByZeroPresheaf.{u} R U ⋙
        PresheafOfModules.sheafification.{u} (𝟙 R.obj)) ∧
      PreservesFiniteColimits (SheafOfModules.extensionByZeroPresheaf.{u} R U ⋙
        PresheafOfModules.sheafification.{u} (𝟙 R.obj)) ∧
      Nonempty (SheafOfModules.extensionByZeroPresheaf.{u} R U ⋙
        PresheafOfModules.sheafification.{u} (𝟙 R.obj) ⊣
          SheafOfModules.overFunctor.{u} R U)
  change P (Opens.grothendieckTopology X) X.sheaf
  have h : ∀ O, P (Opens.grothendieckTopology X) O := by
    rw [← hJ]
    intro O
    exact SheafOfModules.localizedModule_adjunction_exact
      (Opens.grothendieckTopology X).toPrecoverage O U
  exact h X.sheaf

end AlgebraicGeometry
