/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalDerivedData

/-! # Normalized operations on a localized pro-etale site

Source: Stacks Project, Tags 04J0, 08FI, 0FN5 and 07A4.
(blueprint: lem-weil-pbc-ringed-projection-local-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

/-- The localized operation and tensor comparisons exist before considering projection maps.
Source: Stacks Project, Modules on Sites, Tag 04J0; Cohomology on Sites,
Tags 08FI, 0FN5 and 07A4.
(blueprint: lem-weil-pbc-ringed-projection-local-data).

Proof: restrict the coefficient map of g to underlying objects of the slice.
The localized continuous functor gives the module adjunction, with exact pullback
because the original inverse image identifies the coefficient rings. Restriction
is exact and has exact extension by zero as left adjoint. It therefore preserves
K-injectives. On a K-injective representative the two ordinary direct images
have identical sections and scalar actions. Derive this identity square to obtain
the direct-image comparison with its stated representative equation. Its inverse
adjunction mate is the pullback comparison; the mate correspondence gives
mate_counit. Normalize the localized derived counit by the ordinary counit on
K-injectives. On each slice take the localization of the signed total tensor of
flat-term K-flat complexes. Restriction and pullback preserve these complexes.
The ordinary tensor comparisons send sheafified pure tensors to the displayed
pure tensors. Totalize and descend them to obtain the three tensor comparisons
and their representative equations. Shifting the same representatives yields
all the unary and binary shift equations, with the signed second-variable shift.
These data fill Local; no projection compatibility equation is asserted here. -/
theorem localData_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (g : Global f R_Y R_X c) (V : Y.ProEt) :
    Nonempty (Local f R_Y R_X c g V) := by
  obtain ⟨b⟩ := localBaseData_exists f R_Y R_X c g V
  obtain ⟨d⟩ := localDerivedData_exists f R_Y R_X c g V b
  exact ⟨{
    restrictionYAdditive := b.restrictionYAdditive
    restrictionXAdditive := b.restrictionXAdditive
    restrictionY := b.restrictionY
    restrictionX := b.restrictionX
    operation := b.operation
    coefficient_sections := b.coefficient_sections
    adjunction := b.adjunction
    tensorY := b.tensorY
    tensorX := b.tensorX
    tensorYShifts := b.tensorYShifts
    tensorXShifts := b.tensorXShifts
    ordinaryTensor := b.ordinaryTensor
    tensorComparison := b.tensorComparison
    tensorComparison_shifts := b.tensorComparison_shifts
    restrictionTensorY := b.restrictionTensorY
    restrictionTensorX := b.restrictionTensorX
    restrictionTensorY_shifts := b.restrictionTensorY_shifts
    restrictionTensorX_shifts := b.restrictionTensorX_shifts
    leftRouteZero := d.leftRouteZero
    rightRouteZero := d.rightRouteZero
    ordinaryDirectImage := d.ordinaryDirectImage
    ordinaryDirectImage_sections := d.ordinaryDirectImage_sections
    restrictsKInjective := d.restrictsKInjective
    directImage := d.directImage
    directImage_shift := d.directImage_shift
    directImage_representative := d.directImage_representative
    pullback := d.pullback
    pullback_shift := d.pullback_shift
    mate_counit := d.mate_counit }⟩

end AlgebraicGeometry.Scheme.ProjectionRestriction
