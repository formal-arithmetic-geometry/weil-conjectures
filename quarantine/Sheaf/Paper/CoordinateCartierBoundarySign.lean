/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.TwistedCoordinateSectionSign

/-! The signed supported image of the coordinate Cartier adjunct. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- The image of the positive Cartier adjunct under the actual Gysin support
chart is minus the coordinate localization boundary.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, signed rank-one paragraph;
lem-pur-twisted-coordinate-section-normalization, Step 7.
(blueprint: lem-pur-coordinate-cartier-boundary-sign).

Proof: The zero section is Cartier since multiplication by the coordinate is
injective in R[t], including for nonreduced R. In the dual ideal frame e=t^-1,
the divisor section is tau=t*e. Apply principal_torsor_yoneda_sign with global
frame e, prescribed open section tau and g=t. Its normalized relative extension
sends tau to zero, exactly the normalization of ordinary_supported_kummer.
The Yoneda splice with the Kummer extension is consequently minus the coordinate
localization boundary. The relative cone comparison uses D(a,b)=(da,r(a)-db)
and sends the boundary of b to (0,-b), so it preserves this specified sign.
Apply the roots coefficient map and the exact etale/pro-etale comparison.
Use the canonical single/derived comparison, the closed exceptional counit and
the shift comparisons in coordinateCartierAdjunct. Their supported-Hom evaluation
is the support chart of OrientationSupportData, with its normalized snake
boundary. The affine-line orientation construction supplies this chart and its
boundary data. The supported image of coordinateCartierAdjunct is therefore
minus the coordinate boundary. Define pur as its negative. Additivity of the
support evaluation makes its image the positive boundary, and double negation
identifies the Cartier adjunct with -pur. No choice of generator or residue
identification changes this equality. In characteristic two negation agrees
with identity, and on the empty base both sides vanish. -/
theorem coordinateCartierBoundarySign (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] :
    P.CoordinateCartierSign T aT := by sorry

end WeilConjectures.PurityFiniteSetting
