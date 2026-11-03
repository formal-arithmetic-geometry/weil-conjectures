/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityBoundaryShiftedCounit

/-! # Shifted closed counits in exact direct-image coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- The finite exceptional counit commutes with the shift by two, in exact
closed direct-image coordinates.
Source: finite exceptional counit composite and its ordinary etale adjunction.
(blueprint: lem-pur-boundary-exceptional-counit-shift).

Proof: expand the actual exceptional counit as the compact-support comparison,
comparison pullback of the ordinary etale counit, and comparison-adjunction counit.
The etale exceptional shift is the right-adjoint shift induced by its ordinary
compact-support adjunction, so its counit satisfies the shift-counit equation.
The derived site-comparison adjunction has its specified induced shifts; its
counit satisfies the same equation. The compact-support comparison commutes with
shifts: descend the identity-open extension comparison, then use the canonical
right-derived direct-image mate and bounded-below inclusion compatibilities.
Paste these three equations. The three factors of boundaryAdjunctShift are
exactly the composite right-functor shift; the last inclusion map is identity.
The closed Ri! to Ri* comparison and the exact Ri* to D(i*) comparison also
commute with shifts, as follows from their derived construction. Their inverses
move the source shift to exact closed-image coordinates. This gives the displayed
equality, for all maps into the exceptional object and independently of supported
cohomology or the ordinary classical-input normalization. -/
theorem boundary_exceptional_counit_shift (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.map
        (P.boundaryAdjunctShift h Y) ≫ P.boundaryShiftedCounit h Y a =
      P.boundaryExactCounit h Y a := by
  sorry

end WeilConjectures.PurityFiniteSetting
