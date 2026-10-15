/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare

/-!
# The inverse-image comparison of a base-change square

Source: blueprint, sec-smooth-base-change, sk-def-bc
(blueprint: sbc-def-base-change-square).

A base-change square is `ChosenCartesianSquare h e f g`, using the very same datum as
in the proper-base-change chapter. Only the orientation of its comparison is reversed.
The canonical comparison below inherits identity and pasting compatibility by inversion
from the source library's square comparison.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

/-- For the base-change square `Y --h--> X`, `Y --e--> T`, `X --f--> S`, `T --g--> S`,
the canonical isomorphism `h⁻¹ f⁻¹ ≅ e⁻¹ g⁻¹` is the inverse of the comparison in the
proper-base-change chapter. Here the square, including its chosen Cartesian identification
and projection equations, is `ChosenCartesianSquare h e f g`. Identity and pasting
compatibility are inherited from `Etale.squareUpperStarIso` by inversion.
Source: blueprint, sec-smooth-base-change, sk-def-bc, node sbc-def-base-change-square
(blueprint: sbc-def-base-change-square). -/
noncomputable def ChosenCartesianSquare.baseChangeInverseImageIso
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A] {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g) :
    Etale.upperStar A f ⋙ Etale.upperStar A h ≅ Etale.upperStar A g ⋙ Etale.upperStar A e :=
  (Etale.squareUpperStarIso A sq.toCommSq).symm

end AlgebraicGeometry
