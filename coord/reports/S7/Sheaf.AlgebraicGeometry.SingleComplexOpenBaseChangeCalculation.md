## What changed

Repaired return C-32aed (delivery head `32aedbd007`, old base `d92f73d8e`):
rechecked the current shared tree and its rework entry before rebuilding the
delivery on the freshly fetched `sheaf-dag` base through deliver3.py. The current
Sheaf path is absent and its latest source remains in quarantine; that archive
is preserved. Comparing it with the current upstream calculation shows the
same theorem and proof, with only the copyright header and the corrected local
irreducibility command differing. No intervening proof change is overwritten.

Restored `Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation` as a
re-export of its already proved upstream twin. The quarantined copy redundantly
set `derivedPullback` locally irreducible, which Lean rejects now that upstream
uses `irreducible_def`. The upstream twin already fixes this exact problem and
contains the same theorem signature and complete adjunction-mate proof.

Reusing that theorem also removes the duplicate public declaration and five
private helper calculations from the Sheaf copy. The DAG's Lean attachment now
points to the upstream declaration. Its proof route is unchanged, as the same
calculation lives upstream. No upstream module is edited.

## Proved and sorry left

Zero sorries before and after; zero holes closed, zero holes added, none split
off. `AlgebraicGeometry.singleComplexOpen_baseChange_calculation`
(node `lem-pc-n3-open-base-change-calculation`) is re-exported from its existing
complete upstream proof, with precisely the same statement. The Sheaf module
introduces no new declarations or axioms.

## No longer needed

Removed the duplicate Sheaf implementation, including its five private helpers
`compose_of_equal`, `comp_map_identity`, `restrict_homEquiv`,
`open_baseChange_mate`, and `baseChange_homEquiv`.

Replaced four imports by one public import of the canonical calculation module:
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons`,
`WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap`,
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenCounitCompatibility`, and
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCube`.
Those dependencies remain needed transitively by the upstream proof; no DAG node
or dependency module is claimed as pruned. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

This item is a quarantined compilation repair with zero holes. Its original is
`quarantine/Sheaf/AlgebraicGeometry/SingleComplexOpenBaseChangeCalculation.lean`.
The original compiler error was reproduced through lcompile.py:
`failed to set [local irreducible], derivedPullback is currently [irreducible]`.
Removing that attribute made the original calculation compile cleanly in 30.7
seconds, but the delivery compile with its axiom probe exceeded 60 seconds.
The shortest route is the already proved upstream theorem, whose module has the
same public signature and already omits the redundant attribute. This reuses an
existing proof; it introduces no split or additional statement.

A direct import scan of lean/ finds no consumers of the quarantined Sheaf path;
tools/downstream.py reports it unknown. Current consumers use the upstream twin.
No consumer adaptations are required. Change record:
`coord/changes/S7-open-base-change-irreducibility.md`.

The previous reader passed the repair; the landing refused its stale base.
This retry retains the actual compilation repair and updates its documentation
against the current quarantined source; it is not a report-only rebase.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
