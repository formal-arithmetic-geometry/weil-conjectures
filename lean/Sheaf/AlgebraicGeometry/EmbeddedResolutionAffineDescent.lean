/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.AlgebraicGeometry.LabeledOrdinaryZariskiResolutionData

/-! # An assigned embedded resolution is an affine descent of its own chart family

Source: ILO, Travaux de Gabber, VIII 2.1.9, 2.2.11 and Remark 2.3.5(ii).
(blueprint: lem-trf-embedded-resolution-affine-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The rule's existing tower on an embeddable input is already an affine descent.
This asserts only the existence of one witnessing affine cover and its full map.

Source: ILO VIII Remark 2.3.5(ii), printed p.92;
parent descent proof, Step 10.
(blueprint: lem-trf-embedded-resolution-affine-descent).

Proof: choose a finite affine open cover of the input S. The Noetherian finite-type
argument makes every chart a rational input, and a polynomial presentation of its
finite-type coordinate algebra embeds it in smooth separated affine space. The
finite disjoint union T of those charts is therefore embeddable. Compare the tower
A(S) to each chart by the rule's open comparison, and similarly compare A(T) to
each coproduct component. A label of A(S) occurs on some chart: otherwise its
extended ideal is unit on every lifted chart and therefore unit on its level,
contradicting its nonempty center. The same argument on T shows that a label of
A(T) occurs on some component chart. The chart towers are identical in these two
computations, so the two towers have the same ordered labels. Their full restrictions
on a chart are the same padded version of the assigned chart tower. Flat base change
supplies these full restrictions, with unit-ideal identity stages restored at exactly
the missing labels. At level zero the chart maps are the given inclusions into S.
Inductively, the center ideals pull back equally to the chart levels; the blowup
universal property gives the next level maps. Uniqueness of blowup lifts makes them
agree on overlaps. Assemble their disjoint union to obtain a cartesian map from
A(T) to A(S), retaining every label and center. It witnesses IsAffineDescent for
A(S). In the empty case both assigned towers have length zero and the same
construction uses the empty coproduct.
-/
theorem embedded_resolution_isAffineDescent {L : Type w} [LinearOrder L]
    (A : OrdinaryZariskiResolutionRule.{u, w} L) (_hpad : A.HasPaddedOverlaps)
    (S : RationalResolutionInput.{u}) (hS : S.IsEmbeddable) :
    A.IsAffineDescent S (A.tower S hS) := by
  sorry

end AlgebraicGeometry
