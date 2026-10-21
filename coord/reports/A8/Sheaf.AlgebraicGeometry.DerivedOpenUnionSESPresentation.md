## What changed

Retired the Sheaf copy `lean/Sheaf/AlgebraicGeometry/DerivedOpenUnionSESPresentation.lean`.
Change record: `coord/changes/A8-retire-derived-open-union-ses-presentation.md`.

The corresponding DAG attachment now points to the existing upstream declaration
`WeilConjectures.AlgebraicGeometry.DerivedOpenUnionSESPresentation` at the same theorem
statement. The upstream twin is already imported by the live upstream consumer, and no
Lean module currently imports the Sheaf copy.

## Proved and sorry left

This is a human-authorized retirement item, so no proof hole is closed. The deleted Sheaf
module had zero `sorry` declarations before retirement; no new `sorry` is added. Its
statement remains available through the upstream twin.

## No longer needed

The retired Sheaf module and its Sheaf-specific proof dependency closure are no longer
needed by this route. There are no current Lean importers of the deleted module. The DAG
node remains and is attached to the upstream twin; no unit statement or realized unit step
is changed.

## Where the brief, the DAG or earlier work was wrong

The queue classified this module as a retirement item after the upstream twin became the
library implementation. The Sheaf and upstream theorem statements are the same, while the
upstream file uses the upstream dependency namespace. Keeping both copies would preserve a
redundant statement module and can create duplicate dependency environments, so the
human retirement record requires deleting the Sheaf copy and repointing the DAG attachment.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
