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

/-- The shifted finite counit on the classical twist is the ordinary closed counit
transported through the specified comparison maps.
Source: affine-space zero-section purity proof, finite etale-origin counit transport.
(blueprint: lem-pur-boundary-classical-counit-shift).

Proof: use the identity/proper compactification of the zero section. Identify its
ordinary etale compact-support adjunction with the derived closed-image adjunction;
rightAdjointUniq_hom_app_counit fixes the counit. The unit of the actual derived
comparison adjunction is invertible on the bounded-below twist. Unit naturality and
the comparison triangle identity cancel it against the final comparison counit.
The compact-support comparison, after the exact closed-image identifications, is
the inverse of imageComparison: expand the identity-open comparison, cancel its
identity-extension factors, and use the defining derived direct-image mate.
Collapse cancels its inverse in boundaryExceptionalComparison. Move the shift by
two through the exact image and comparison functors, using the shift naturality
of those same canonical maps. The resulting source is boundaryImageComparison
at the shifted ordinary exceptional value; the resulting target is precisely
boundaryEtaleCounit followed by the comparison shift isomorphism. This computation
is on all morphisms of the classical twist, before any supported class is chosen. -/
theorem boundary_classical_counit_shift (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h Y)) :
    P.boundaryImageComparison Y ⟨P.boundaryEtaleValue h Y, hb⟩ ≫
      (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.map
        (P.boundaryExceptionalComparison h Y) ≫ P.boundaryShiftedCounit h Y a =
    (nu P (Line Y)).map (P.boundaryEtaleCounit h Y) ≫
      ((nu P (Line Y)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h Y).obj := by
  sorry

end WeilConjectures.PurityFiniteSetting
