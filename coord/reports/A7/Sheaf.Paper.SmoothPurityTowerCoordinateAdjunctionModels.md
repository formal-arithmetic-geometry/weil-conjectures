## What changed

Kept the original Models and theorem statements unchanged. Decomposed the one
existence hole into normalized root/tensor foundations, ordered projection
adjunctions, and finite compatibility of explicitly constructed chart pairs.
The ordered right comparison is defined by induction from zero and step; its
successor equation is reflexive and its zero equation uses the unit normalization.
The chart pair is constructed by composing the actual restricted étale adjunction
with the projection adjunction and transporting both functors by the specified
compact-support and pulled-twist comparisons. This includes actual unit/counit
and both triangles through Mathlib Adjunction.comp. A generic theorem calculates the ambient transported counit formula; the explicit
chart counit at the chosen intermediate compactifications specializes it.

Change record: coord/changes/A7-coordinate-adjunction-decomposition.md.

## Proved and sorry left

Closed the original hole
AlgebraicGeometry.ProEtale.SpCoordinateAdjunction.tower_coordinate_adjunction_models
by decomposition. The item itself has zero sorry left. Added three whole theorem
holes, all under AlgebraicGeometry.ProEtale.SpCoordinateAdjunction:

- coordinate_foundations (lem-sp-coordinate-foundations): ordinary comparisons,
  normalized projective presentations and admissible domains.
- coordinate_projection_models (lem-sp-coordinate-projection-models): affine/open
  integration, ordered projections and finite projection compatibility.
- coordinate_chart_models (lem-sp-coordinate-chart-models): evaluation and
  intermediate-compactification independence of the explicitly composed chart pair.

This closes one upper hole and adds three lower holes: a decomposition, not a net
sorry reduction. restrictedComposite_counit is proved; Foundations.iteration and
coordinateChartPair are explicit constructions with no holes. The fixed-choice
chart counit formula coordinateChartPair_counit is proved from restrictedComposite_counit. The standalone composition helper compiled cleanly in 11.4 seconds with the
full proof. The final five-module chain compiled cleanly with lcompile.py --all. The
required delivery tool runs the declaration axiom probe and server preflight.

## No longer needed

Removed the item's private imports of Sheaf.Paper.PurityFiniteKummerLevel,
Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses,
Sheaf.Paper.AmbTateRootProjectionReduction,
Sheaf.AlgebraicGeometry.FiniteRootSiteComparison,
Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine and Sheaf.Paper.RootTowerFiniteTensor.
Their mathematical results remain in the proof plan for the foundation lemma;
this delivery does not claim those nodes or modules globally unnecessary.
All original public imports remain. No module is withdrawn, and the P1/open,
ordered-projection and étale-composition unit route is preserved.
The parent now directly needs the four new nodes; its former proof dependencies
are carried by the relevant strict subarguments, rather than discarded.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies supply geometric ingredients but not the normalized
coordinate interface glue. In particular the P1 theorem takes a presentation,
whereas the original Models theorem also requires a presentation agreeing with
the given base and operations; the foundations obligation makes that gap explicit.
Likewise finite compatibility must cover all finite objects and cannot follow
from faithfulness of derived evaluation. The chart obligation keeps that full
finite domain and derives comparisons by evaluating the actual constructions.
No statement dispute or target change is introduced.

## New nodes

lem-sp-coordinate-foundations: root/tensor normalization and admissibility, only;
includes the explicit ordered iteration.

lem-sp-coordinate-projection-models: ordered projection adjunctions and their
finite normalization, with no étale chart pair.

lem-sp-coordinate-restricted-composition: proved ambient counit formula for the
explicit transported composition on full subcategories.

lem-sp-coordinate-chart-models: finite compatibility and compactification
coherence of the explicit chart construction, rather than chart existence.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
