## What changed

Restored the quarantined module `Sheaf.PoincareDuality.ConstructibleShiftSingle` and its
complete proof of `AlgebraicGeometry.ProEtale.boundedConstructible_shift_single`.
Changed its proof-only `import all` from the upstream derived-category module to
`Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`,
where the upstream sync moved the private, proved helpers `constructible_of_iso` and
`constructible_of_isZero`. Kept both archived public imports and the theorem signature and
body unchanged. Updated the existing node's proof text to name the new helper location.
No definition, target, hypothesis, or public declaration changes.

The first compile of the corrected proof import completed cleanly in 2.7 seconds.
The delivery preflight recompiles the final restored module and probes its axioms.
LeanFinder and Loogle confirm the existing shifted-single support and homology
isomorphism; local source search finds the two constructibility helpers at their new
location. No duplicate helper or new mathematical statement is needed.

## Proved and sorry left

The archived item has zero textual holes. Closed: zero. Added: zero. Left in the item:
zero. The complete existing proof of
`AlgebraicGeometry.ProEtale.boundedConstructible_shift_single` now compiles again.
This is an import repair, not a decomposition or a newly closed mathematical hole.
Its node remains `lem-poincare-constructible-shift-single`.

## No longer needed

Removed the stale proof-only
`import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
The same module's public import remains necessary for the statement. The helper module
remains necessary for the proof. No node or module is withdrawn or pruned, and both
existing proof dependencies are retained. The quarantined Poincare parent still uses
the theorem; its absence from the live import graph is not treated as withdrawal.

## Where the brief, the DAG or earlier work was wrong

The rework diagnostic is accurate: the scheduled upstream sync moved the private helpers
out of the upstream module, while the archived proof still used `import all` of their old
location. The node likewise named that obsolete helper location; its proof text is repaired.
The argument itself and its general, possibly noncommutative coefficient signature remain
valid. No new nodes, statement changes, forced consumer adaptations, or change of unit
route are needed.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
