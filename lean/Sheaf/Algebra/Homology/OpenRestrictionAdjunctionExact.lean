/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.Paper.DerivedHomMayerVietoris
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf

/-! # Exact extension by zero and restriction on a ringed space

Source: literature/stacks-project/cohomology.tex, Lemma 08BS (proof), citing
literature/stacks-project/sheaves.tex, Lemma 00A7 and
literature/stacks-project/modules.tex, Lemma 01AK
(blueprint: lem-sc-derived-open-restriction-adjunction-exact).
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For an open `U` of a ringed space `X`, restriction
`j⁻¹ = SheafOfModules.overFunctor (moduleRings X) U : Mod(O_X) ⥤ Mod(O_U)` is exact, and
extension by zero `j_!` (the extension-by-zero presheaf followed by module
sheafification) is exact and left adjoint to it: `j_! ⊣ j⁻¹`. Exactness is preservation
of finite limits and finite colimits.

Source: literature/stacks-project/cohomology.tex, Lemma 08BS, with
Sheaves Lemma 00A7 and Modules Lemma 01AK
(blueprint: lem-sc-derived-open-restriction-adjunction-exact).

Proof: (1) Exactness of `j⁻¹` is checked stalkwise
(`lem-weil-pbc-module-stalk-exact` (5)): the stalk of a restriction at `x ∈ U` is the
stalk at `x`. (2) The adjunction: a presheaf map from the extension-by-zero presheaf to
`G` is a map on `U` (extend by zero outside `U`), and composing with the universal
property of module sheafification (`def-weil-presheaf-modules-sheafification`) gives
`j_! ⊣ j⁻¹`. (3) Exactness of `j_!`: its stalk at `x ∈ U` is the stalk of the input and
at `x ∉ U` is zero (`lem-weil-pbc-stalk-sheafification-space`), so it is exact by
`lem-weil-pbc-module-stalk-exact` (5). -/
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
  sorry

end AlgebraicGeometry
