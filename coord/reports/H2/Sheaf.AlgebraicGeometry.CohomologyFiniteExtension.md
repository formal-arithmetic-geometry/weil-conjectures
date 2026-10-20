## What changed

The already proved duplicate module `Sheaf.AlgebraicGeometry.CohomologyFiniteExtension`
was withdrawn. Its DAG node now points to the identical upstream declaration
`AlgebraicGeometry.Scheme.Modules.finite_H_of_shortExact_extension` in
`WeilConjectures.AlgebraicGeometry.CohomologyFiniteExtension`, which is the module used by
the source library. No Lean module imports the Sheaf copy. The change record is
`coord/changes/CohomologyFiniteExtension-retire.md`.

## Proved and sorry left

The withdrawn Sheaf module had no `sorry`; its theorem had already been proved. No new
sorries were added.

## No longer needed

The withdrawn file `lean/Sheaf/AlgebraicGeometry/CohomologyFiniteExtension.lean` and its
Sheaf-only proof imports are no longer needed. The node's proof dependency is retained
semantically through the upstream twin, so no DAG proof step is removed.

## Where the brief, the DAG or earlier work was wrong

The item was queued as `retire` after the upstream sync even though the Sheaf module was
already proof-complete. The duplicate declaration is unnecessary because the upstream
module has the same statement and proof.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
