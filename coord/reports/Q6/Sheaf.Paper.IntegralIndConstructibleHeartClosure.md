## What changed

Restored `lean/Sheaf/Paper/IntegralIndConstructibleHeartClosure.lean` from the
quarantine archive named by its current `coord/rework.tsv` row. Added public
imports of `Mathlib.CategoryTheory.ObjectProperty.Kernels` and
`Mathlib.CategoryTheory.ObjectProperty.Extensions`, since the public theorem's
statement uses the kernel, cokernel and extension closure classes they define.
Every archived declaration, signature, proof, docstring and existing import is
preserved verbatim. The repaired module compiled without warnings in 18.6 seconds.

Change record: `coord/changes/Q6-integral-ind-heart-closure-restoration.md`.

## Proved and sorry left

This is a zero-hole restoration repair: 0 holes closed, 0 holes added, 0 holes
remaining, and 0 split off. No declaration contains `sorry` in the delivered file.
The complete archived proof of
`AlgebraicGeometry.ProEtale.integralIndConstructibleHeartClosure`
(node `lem-sfb-integral-ind-heart-closure`) now compiles. Its integral continuity
dependency remains an existing named theorem in its own module; this delivery
makes no claim to have closed that dependency's proof hole.

## No longer needed

None. No imports, declarations, nodes or modules are removed. The existing
canonical-presentation, kernel/cokernel, extension descent and finite-subsum
arguments, with their dependencies, are retained. There is no route change or
new node, so the current DAG proof and Lean attachment need no modification.

## Where the brief, the DAG or earlier work was wrong

The assigned item was absent from `lean/` because it was quarantined, not because
its mathematics had been withdrawn. Its archive has zero holes. The unrepaired
archive fails at line 278 with invalid fields `IsClosedUnderKernels` and
`IsClosedUnderCokernels`, and at line 279 with invalid field
`IsClosedUnderExtensions`, followed by three cascading `No goals to be solved`
errors. Private imports provide these declarations only to proofs; they do not
make them available while elaborating the exported statement. Direct public
imports of their defining Mathlib modules repair this visibility error.
No mathematical statement, definition, geometric hypothesis or unit route changes.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
