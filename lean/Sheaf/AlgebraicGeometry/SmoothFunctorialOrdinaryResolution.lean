/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.RingTheory.StandardSmoothQuotientLift
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.AlgebraicGeometry.EmbeddedResolutionAmbientComparison

/-!
# Smooth-functorial ordinary resolution in characteristic zero

Source: Illusie–Laszlo–Orgogozo, Exposé VIII, Theorem 2.3.10, with
2.1.4, 2.3.1, 2.3.4 and Remark 2.3.5(i), printed pp. 87, 91–93
(blueprint: lem-trf-smooth-functorial-ordinary-resolution).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- There is a single ordinary resolution rule functorial for every smooth morphism.
Source: ILO VIII, Theorem 2.3.10 and Remark 2.3.5(i)
(blueprint: lem-trf-smooth-functorial-ordinary-resolution).

Proof:
1. Apply `lem-trf-embedded-resolution-ambient-comparison` to a reduced finite-type
scheme embedded in a smooth separated rational scheme. By
`lemma-nagata-strict-transform-ambient-closed`, the strict-transform tower is its intrinsic
ordinary blowup tower. Ambient comparison identifies its ideals and synchronization
labels independently of the embedding. Affine schemes embed in affine space using a finite
algebra generating set (`def-weil-pbc-finite-type-algebra`, `def-weil-closed-immersion`).
Apply this construction to a finite disjoint union as a single input.
2. For a smooth map between embeddable schemes use standard-smooth affine charts
(`lem-weil-pbc-smooth-locally-standard-smooth`). Lift the standard-smooth algebra through
the ambient quotient (`lem-weil-pbc-standard-smooth-quotient-lift`), with no nilpotence
assumption. The lift is smooth by `lem-weil-pbc-standard-smooth-is-smooth` and
`lem-weil-pbc-smooth-ring-map-iff-smooth-affine`; its ambient is smooth by
`lem-trf-smooth-composition`. Embedded ambient comparison gives equal extended ideals
and labels on these charts, even with varying relative dimensions.
3. The labels retained on a covering are exactly those whose centers meet some chart.
Induct on that common ordered list: equality of the local next ideals gives equality of
the global ideals and their blowups. Smooth maps are flat (`lem-pc-smooth-flat`), so
`thm-nagata-blowup-flat-base-change` and `def-nagata-blowup-flat-base-change-map`
identify this recursive comparison with cartesian pullback. Exactly unit ideals disappear.
4. For a general, possibly non-separated input, take a finite affine open cover, using
`def-weil-finite-type-morphism`, and resolve its disjoint union. Compare on affine opens
covering each overlap by step 3. Restore empty centers at missing synchronization labels.
At each stage the ideals glue and their blowups glue by open base change. Equality of
ideals gives triple-overlap compatibility. Intersections are not assumed affine.
5. Coherence of ideals, regularity and nowhere density of centers, and regularity of the
last scheme descend from the open cover. Nonemptiness follows from the surjective cover.
A disjoint union of two covers shows that neither covering family can lose a label, hence
the construction is independent of the cover. Three covers give transitivity.
6. For any smooth map take finite affine covers subordinate to inverse images of target
charts. Their induced map is smooth (`def-sbc-smooth-morphisms`,
`lem-trf-smooth-composition`). Step 3 compares the disjoint unions. Descend one label at
a time: an extended ideal is unit precisely when it is unit on every source chart, and
at a retained label its descended ideal is the source tower's center. Flat blowup base
change gives every cartesian comparison and preserves the original order.
7. The comparisons for identities and composites agree on affine blowup charts: the
canonical maps on rings B[I/a] commute with iterated tensor base change. They therefore
glue to identical level maps. Extending ideals twice equals extension along the composite;
a unit remains unit, so contractions compose. A surjective smooth map remains surjective
on every pullback level and meets every nonempty center, hence deletes no stage. For the
empty scheme the tower has length zero. -/
theorem exists_smooth_functorial_ordinary_resolution :
    Nonempty (SmoothFunctorialOrdinaryResolution.{u}) := by
  sorry

end AlgebraicGeometry
