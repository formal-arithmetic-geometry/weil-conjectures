/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.AlgebraicGeometry.LabeledOrdinaryZariskiResolutionData

/-! # Common-cover comparison and ideal detection for ordinary affine descents

Source: ILO, Travaux de Gabber, VIII 2.1.9, 2.2.11 and Remark 2.3.5(ii).
(blueprint: lem-trf-affine-resolution-descent-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A tower descending from one affine cover pulls back to the assigned tower on
every affine cover, with detection of its actual center ideals; two such descents
admit a cartesian comparison over the identity. Uniqueness of the comparison and
the cocycle equation are deliberately not assumed here.

Source: ILO VIII 2.2.11 and Remark 2.3.5(ii), printed pp.91--92;
parent descent proof, Steps 5 and 8--9.
(blueprint: lem-trf-affine-resolution-descent-comparison).

Proof: choose a cover witnessing that B is an affine descent. For any other cover,
form the combined finite family, whose total space is the disjoint union of the two
total spaces. It is again embeddable. The component open immersions compare each
assigned subfamily tower with the contraction of the assigned combined tower.
If a label of the combined tower disappeared on one subfamily, its ideal would be
unit there. On any affine open in an intersection with a chart from the other
subfamily, the two open comparisons contract to the same assigned tower. Padding
restores precisely the missing unit ideals, so the combined ideal is unit on this
affine overlap as well. Such affine overlaps cover every chart of the other family
because the first family covers S. Their inverse images cover each lifted level.
The ideal is therefore unit throughout the combined level, contradicting its
nonempty center. Thus neither covering subfamily loses any label. This argument
uses the original label in the full tower, including across preceding deleted stages.
The padded-overlap comparisons now identify full towers on all chart refinements.
At level zero use the identity on S. Given the comparison at a level, the actual
center ideals agree because equality of sheaf membership is detected on the covering
opens: a section is in the ideal exactly when all its chart restrictions are in it.
The next blowups are identified by their universal property; their pulled-back
ideals are invertible by principalization. Reverse lifts show that the level maps
are isomorphisms, hence cartesian over the identity. Their uniqueness makes the
identifications agree on refinements and permits induction through all labels.
Apply this induction on the lifted chart overlaps of B and A(T). The level maps
glue on their source open covers, and their squares are cartesian locally on the
cover. This gives the required full map on the second cover. Any ideal J having the
prescribed pullback has the same chart restrictions as B's center. The same
sectionwise membership test proves J equals that center; this is DescendsIdeals. For another affine
descent
C, repeat the construction with its witnessing cover to obtain a cartesian map
between B and C over the identity. All labels and the entire center ideals are
preserved. Empty families have zero stages, and empty chart pieces do not change
any sheaf-membership test.
-/
theorem affine_resolution_descent_comparison {L : Type w} [LinearOrder L]
    (A : OrdinaryZariskiResolutionRule.{u, w} L) (_hpad : A.HasPaddedOverlaps)
    (S : RationalResolutionInput.{u}) (B : LabeledOrdinaryTower L S.scheme)
    (_hB : A.IsAffineDescent S B) :
    (∀ (T : RationalResolutionInput.{u}) (q : T.scheme ⟶ S.scheme),
      ResolutionAffineCover S T q → ∃ hT : T.IsEmbeddable,
        ∃ c : LabeledOrdinaryCartesianMap q B (A.tower T hT), c.DescendsIdeals) ∧
      (∀ C : LabeledOrdinaryTower L S.scheme, A.IsAffineDescent S C →
        Nonempty (LabeledOrdinaryCartesianMap (𝟙 S.scheme) B C)) := by
  sorry

end AlgebraicGeometry
