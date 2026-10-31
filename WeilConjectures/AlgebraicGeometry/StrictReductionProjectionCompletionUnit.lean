/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletionMateComparison

/-! # The strict projection extends the completion unit

Source: Stacks Project, Tags 0B56, 0941 and 0A07.
(blueprint: lem-pur-strict-reduction-projection-completion-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace CategoryTheory.AdicSites

variable {Y X : Site.{u}} (f : Morphism Y X) (A : Type u) [CommRing A] (I : Ideal A)

/-- Total derived limit of the strict projection carries the fixed completion unit
into direct image of the fixed completion unit, without perfectness or completeness.

Source: Stacks Project, sites-cohomology.tex, equation 0B56, Tags 0941 and 0A07;
strict augmentation and constant-tower specialization of the projection formula map
(blueprint: lem-pur-strict-reduction-projection-completion-unit).

Proof:
1. Let j_T be the derived quotient augmentation from the constant tower Delta_T to
reduction_T. Define it as the adjunction transpose of the fixed completion unit under
the constant-tower/derived-limit adjunction. On flat-term K-flat representatives
this is the ordinary quotient augmentation. Its limit, preceded by the constant/limit adjunction
unit, is
the fixed completion unit: the ordinary limit unit followed by the limit of
the quotient augmentation has projections exactly the defining ordinaryUnit maps. The normalized
quotient-presentation and delta-adjunction laws descend this equality.
2. The ordinary normalized moduleReductionPullIso preserves quotient insertion.
Localize its full-cochain square. This gives j_Y followed by reductionPullIso equal
to constantPullIso followed by Delta_X of inverse image of j_X. Taking adjunction mates
gives j_Y followed by towerProjection equal to the constant/pushforward mate chi followed
by towerPush of j_X, as an equality of whole strict tower maps.
3. Apply derived limit. The directLimitIso is the conjugate of constantPullIso under
the two composite adjunctions, so the unit mate equation identifies the limit of chi
preceded by the Y constant/limit unit with direct image of the X constant/limit unit
followed by directLimitIso. Move the image of j_X past directLimitIso by naturality,
then use step 1 and cancel this isomorphism. This is the asserted equation. No
perfectness or completeness assumption is involved. -/
theorem strictReductionProjectionCompletionUnit (F : X.derived A) :
    (Y.unit A I).app ((f.push A).obj F) ≫
        (Y.rlim A).map (f.towerProjection A I F) ≫
        (f.directLimitIso A).inv.app ((X.reduction A I).obj F) =
      (f.push A).map ((X.unit A I).app F) := by
  sorry

end CategoryTheory.AdicSites
