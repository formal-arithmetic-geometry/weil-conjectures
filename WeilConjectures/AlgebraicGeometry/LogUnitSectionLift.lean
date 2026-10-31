/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Unit sections of an étale log structure

Source: ILO, Exposé VI 1.1, printed p.69, the log unit isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The stalkwise log axiom gives a unique log section above every ring unit section.
Source: ILO VI 1.1, printed p.69, the isomorphism over units; the stalkwise criterion
for étale sheaves (Stacks, Tags 03PT and 03PU).
(blueprint: lem-trf-log-unit-section-lift).

Proof: form the subsheaf of log sections whose structural image is invertible,
and map it to the sheaf of units of the structure sheaf. Both are sheaves since
invertibility is local and inverse sections glue uniquely. Filtered pointed étale
colimits commute with finite limits, so the stalk of the first sheaf consists of
log germs whose structural image is a ring unit. Reflection of units identifies
this with the unit group of the log stalk. The map on stalks is therefore precisely
`Units.map stalkAlpha`, which is bijective by `unitsBijective`. Geometric points
are conservative on the small étale site, so the map of sheaves is an isomorphism.
Evaluate its inverse at the given unit section. Its two inverse identities give
existence and uniqueness, including when the test scheme is empty. -/
theorem EtaleLogStructure.existsUnique_unit_section_lift
    {X : Scheme.{u}} [IsLocallyNoetherian X] (K : EtaleLogStructure X)
    (U : X.Etaleᵒᵖ) (a : (X.etaleStructurePresheaf.obj U)ˣ) :
    ∃! m : K.monoidSheaf.obj.obj U, K.alpha.app U m = a.val := by sorry

end AlgebraicGeometry
