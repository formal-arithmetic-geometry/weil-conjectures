/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.RingedProjectionRestrictionData

/-! # Canonical projection-formula models

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6.
(blueprint: lem-weil-pbc-ringed-projection-local-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

/-- A normalized global projection package admits compatible localization at any object.
Source: Stacks Project, Tags 04J0, 08FI, 0FN5, 07A4 and 0B56.
(blueprint: lem-weil-pbc-ringed-projection-local-model).

Proof: localize the site morphism at V and its base change, with the original
coefficient map evaluated on underlying objects. The ordinary direct-image square
is the identity on sections; its inverse adjunction mate is the pullback square.
Restriction is exact and preserves K-injectives. Derived uniqueness therefore
descends the direct-image square with the displayed representative normalization.
Its inverse mate gives the pullback square and the counit equation. On all four
sites localize the flat-term K-flat total tensor. The ordinary tensor comparison
and restriction send pure tensors to the same pure tensors. Their totalizations
respect bidegrees and the signed second-variable shifts. Descent gives all tensor
and shift comparisons. Apply tensor coherence to the ordinary localization square,
then transpose the counit-tensor composite under the two adjunctions. The counit
mate equation and tensor coherence identify its two paths; after the specified
source and target isomorphisms this is precisely ProjectionCompatible. All
comparisons are determined on representatives, so the construction applies to
any global package satisfying its normalization fields. -/
theorem localModel_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (g : Global f R_Y R_X c) (V : Y.ProEt) :
    ∃ l : Local f R_Y R_X c g V, l.ProjectionCompatible := by sorry

end AlgebraicGeometry.Scheme.ProjectionRestriction
