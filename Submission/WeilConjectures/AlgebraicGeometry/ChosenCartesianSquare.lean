/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Cartesian squares with a chosen pullback identification

Source: blueprint, sec-curve-estimates, sk-prop-cd.

The inverse-image comparison is the existing `Etale.squareUpperStarIso` applied to
`ChosenCartesianSquare.toCommSq`. Its identity and pasting coherence are supplied by
`Etale.squareUpperStarIso_id`, `Etale.squareUpperStarIso_paste_horiz_hom`, and
`Etale.squareUpperStarIso_paste_vert_hom`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A Cartesian square of schemes with its chosen identification with the fibre product.
The two projection equations say that the identification is one of squares, not merely
of schemes. The inherited commutativity gives the canonical inverse-image comparison
`Etale.squareUpperStarIso A sq.toCommSq`, with the identity and pasting compatibility of
that construction. Source: blueprint, sec-curve-estimates, sk-prop-cd,
node def-weil-pbc-cartesian-square . -/
structure ChosenCartesianSquare {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    extends CommSq g' f' f g where
  /-- The specified Cartesian identification. -/
  isoPullback : X' ≅ pullback f g
  /-- The identification respects the first projection. -/
  hom_fst : isoPullback.hom ≫ pullback.fst f g = g'
  /-- The identification respects the second projection. -/
  hom_snd : isoPullback.hom ≫ pullback.snd f g = f'

end AlgebraicGeometry
