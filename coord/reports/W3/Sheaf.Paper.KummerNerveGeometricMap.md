## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.kummerNerveMap_toBase` in
`Sheaf.Paper.KummerNerveGeometricMap`. The proof composes `coords.over n` with
`a`, substitutes `hj`, and uses the proved canonical parameter-projection
naturality equation `coefficientParameterProjectionCommutes`. It follows the
existing declaration's documented argument, without altering any signature,
definition, import, or node attachment. Both existing public imports are needed
by the derived comparison and geometric map definitions.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.CondensedRing.kummerNerveMap_toBase`
(node `def-sfb-kummer-nerve-geometric-map`). The item initially had 1 hole and
now has 0. Added 0 holes; split off 0 statements. The two existing definitions
are retained verbatim. Dependencies may still contain their separately tracked
holes; none are added or modified by this delivery.

## No longer needed

None. No import, node, or module is removed. The original documented proof route
is retained, using existing coordinate data and a proved projection equation.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The rework table has a historical quarantine
row for this module, but the current live source exists and is the version used
for this packet. No current return entry names this item. The proof is uniform
in `n`, including `n = 0`, and uses no nonemptiness or freeness assumption.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
