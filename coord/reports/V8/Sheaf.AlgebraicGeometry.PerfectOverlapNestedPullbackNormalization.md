## What changed

Repaired the returned no-op packet by changing the actual proof dependency of
`Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackNormalization`:
replace `import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle` with
`import all WeilConjectures.AlgebraicGeometry.PerfectHomComparisonTriangle`.
The proof now uses the adopted source's proved private `compositionTo` and
`compositionTo_triangle`, rather than their public copies in the Sheaf adapter.
Both imports are proof-only. The theorem's public signature, public imports,
docstring and complete coherence argument are preserved.

Updated the existing node's second proof step and `proof_origin` to describe the
source helper use. Its dependencies, statement and Lean attachment are unchanged.
The unit's realization route is preserved.

The revised module compiled cleanly in 9.8 seconds. A second compile (8.3 seconds)
with a temporary `#print axioms` reports exactly `propext`, `Classical.choice`, and
`Quot.sound`. The unchanged consumer `PerfectOverlapNestedSiteCompatibility` then
compiled against the revised module in 18.5 seconds. Neither the diagnostic command
nor the unchanged consumer is included in the delivery.

Change record:
`coord/changes/V8-perfect-overlap-nested-pullback-normalization-restoration.md`.

## Proved and sorry left

The current item starts with zero holes and ends with zero holes. Holes closed: 0.
Holes added: 0. Split off: 0. There are no declarations containing `sorry` in the
packet. Both `pinnedComposition_eq` and
`AlgebraicGeometry.perfectOverlapNestedPullbackSquare_on_image` retain complete
proofs; the latter now uses the source composition helper directly.
This is dependency pruning of an already-proved item, not a new hole closure.

## No longer needed

Removed this module's proof-only import of
`Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle`. Its public composition
helpers are unnecessary here because the adopted source contains the same proved
helpers. The adapter itself still has other consumers and is not withdrawn or
claimed to leave the targets' whole import closure.

No mathematical node, statement, definition or unit step is pruned: the triangle
node already points to the adopted source module. All other imports remain used.
The parent `PerfectOverlapNestedSiteCompatibility` and its dependency on this
normalization remain intact. Searches found generic Mathlib naturality and open
restriction results, not a replacement for this fixed derived normalization.

## Where the brief, the DAG or earlier work was wrong

The original restoration and attribute fix had independently reached the current
library before the previous packet was reviewed. Its Lean text was therefore a
no-op, exactly as the return reports. This packet contains a real import change
against current library text instead of repeating the restoration or rebasing it.
The original report's statements that the item and its consumer were absent are
obsolete: both are present now.

The DAG already attaches the triangle node to the adopted source module, so the
proof-only import now follows that attachment directly. No mathematical statement
repair, definition repair, new node, consumer adaptation, or further split is
needed.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
