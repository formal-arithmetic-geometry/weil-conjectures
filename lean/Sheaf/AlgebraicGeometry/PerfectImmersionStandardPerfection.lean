/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Perfection of closed-immersion pushforward in the standard localization

Source: Stacks Project, Tags 05RU, 08CM and 0A9U.
(blueprint: lem-sc-perfect-immersion-standard-perfection).
-/

@[expose] public section

set_option autoImplicit false

universe u wY

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- A perfect single pushforward of O_Z gives a perfect standard Ri_* of the unit.
Source: Stacks Project, Tags 05RU, 08CM and 0A9U.
(blueprint: lem-sc-perfect-immersion-standard-perfection).

Proof: on every open of Y compare the given derived localization with the standard
one by the Qh comparison. Restriction is an exact functor of module categories;
its derived functor commutes with these comparisons by localization uniqueness.
Thus the strictly perfect complexes witnessing the hypothesis, with the same open
cover and the same terms, also witness perfection of the standard single i_*O_Z.
Module pushforward for a closed immersion is exact: it is restriction of scalars
on the closed subset and extension by zero, and exactness can be checked on stalks.
Consequently its right derived functor carries a single module to the single of
its pushforward. The standard derived tensor unit is the single O_Z. These two
isomorphisms identify the standard Ri_* of its unit with the perfect standard
single i_*O_Z just obtained. Perfection is invariant under isomorphism by its
local definition. Properness and Noetherianity are unnecessary for this comparison.
The identity immersion gives the usual structure unit; for the empty closed
subscheme its pushforward is zero, a strictly perfect complex. -/
theorem perfectImmersion_standardPerfection
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hperfect : Y.IsPerfect
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))) :
    @Scheme.IsPerfect Y (HasDerivedCategory.standard _)
      (fun _ ↦ HasDerivedCategory.standard _)
      ((@schemeDerivedDirectImage Z Y (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) i).obj
        (𝟙_ (@schemeDerivedCategory Z (HasDerivedCategory.standard _)))) := by sorry

end AlgebraicGeometry
