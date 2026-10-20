## What changed

Withdrew `lean/Sheaf/AlgebraicGeometry/StrictHenselizationClosedFiberBackward.lean`
using `deleted.txt`. Moved its exact public theorem and proof into the sole direct
consumer, `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber`, and replaced the
consumer's private import of the withdrawn module with
`Sheaf.Paper.StrictHenselizationFunctoriality`. The existing theorem signature and
all downstream call sites are unchanged. Updated the node's Lean attachment to the
surviving declaration in the consumer. The change record is
`coord/changes/J4-strict-henselization-closed-fiber-backward-retirement.md`.

## Proved and sorry left

This was a zero-hole retirement item: 0 sorries closed, 0 sorries added, and 0
sorries left. The moved declaration
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_closedPoint_eq` compiles
with its complete existing proof and uses only the permitted axioms.

## No longer needed

The duplicate module `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberBackward`
and its imports are removed. No proof dependency or unit step is pruned. The source
library is unchanged. The upstream twin was not imported because it is stated for
`strictLocalization` and its structural map, while this consumer's retained theorem
uses `strictHenselizationScheme` and `strictHenselizationStructuralMap`; the two
interfaces are not definitionally equal in the current source tree.

## Where the brief, the DAG or earlier work was wrong

The queue marks this as a retirement item even though the module already had a
complete proof. The source twin is recorded as `DIFFERENT` in the retirement census:
it uses the all-neighbourhood strict localization rather than the small-model
structural map. A direct source import fails because both structural-map extension
modules declare `strictHenselizationStructuralMap_eq`; moving the unchanged theorem
to its sole consumer preserves the old API while allowing the duplicate module to be
withdrawn. No target statement or mathematical clause changed.

## Second reading by J4

No second reader is available in this dispatched worker session. The moved theorem
was compiled independently, and its node statement and proof are unchanged.
