/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.AlgebraicGeometry.LabeledOrdinaryZariskiResolutionData

/-! # Padded ordinary resolution towers on affine overlaps

Source: ILO, Travaux de Gabber, VIII 2.1.9, 2.2.11 and Remark 2.3.5(ii).
(blueprint: lem-trf-ordinary-resolution-padded-overlaps).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For an open-functorial labeled ordinary resolution rule, affine overlaps admit a
common full tower, with precisely the unit-ideal stages inserted at missing labels.

Source: ILO VIII 2.1.9 and Remark 2.3.5(ii), printed pp.88,92;
parent descent proof, Steps 3--4.
(blueprint: lem-trf-ordinary-resolution-padded-overlaps).

Proof: pull back the assigned disjoint-union tower along each of the three open maps.
Flat base change identifies each next level with the ordinary blowup of the extended
ideal. The open comparison to the rule's tower on W deletes exactly the unit ideals
and preserves the ordered surviving labels and their actual ideals. Thus each full
pullback is obtained from that same assigned tower on W by inserting unit ideals at
exactly the labels missing from its increasing list. A unit ideal has empty zero
scheme, so the blowup-complement theorem identifies its blowup with the identity.
Induct through the common finite list, using the same identity stage at each missing
label. At each retained label the pullback of the center on its blowup is invertible;
the universal property supplies the comparison with the corresponding blowup of the
common tower. Uniqueness of lifts makes these identifications agree with the maps
at preceding stages. The three pullbacks therefore have a single common realization
P with uncontracted cartesian maps and with the label-preserving contraction to A(W).
Taking two of the maps equal gives double overlaps; using all three gives the
triple-overlap agreement. No affine-intersection assumption is used. A proper ideal
whose blowup is an isomorphism remains a retained stage, since deletion tests the
ideal itself. Empty W gives the same construction with only unit stages.
-/
theorem ordinary_resolution_padded_overlaps {L : Type w} [LinearOrder L]
    (A : OrdinaryZariskiResolutionRule.{u, w} L) : A.HasPaddedOverlaps := by
  sorry

end AlgebraicGeometry
