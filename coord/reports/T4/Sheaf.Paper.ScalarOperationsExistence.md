## What changed

The item now imports two proof-only modules. `semilinearScalarOperations` assembles
`ScalarSystems` from normalized scalar-data witnesses and the evaluation/transpose
package. The two lower statements are recorded as separate modules and DAG nodes.

## Proved and sorry left

Closed: `WeilConjectures.SemilinearSections.semilinearScalarOperations` (the original
hole), by a real Lean assembly from the two named lower declarations.

Added: `WeilConjectures.SemilinearSections.semilinearScalarData` in node
`lem-coef-semilinear-scalar-data`, and
`WeilConjectures.SemilinearSections.semilinearScalarEvaluationTranspose` in node
`lem-coef-semilinear-scalar-evaluation-transpose`. These are the two strictly simpler
normalization stages needed by the assembly.

## No longer needed

No existing proof dependency is removed. The assembly uses only the two new lower
modules; the earlier plan's generic K-flat and derived-comparison modules remain
available to the lower statements and are not imported into the item itself.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan bundled independent scalar-data construction, evaluation
comparison, and the mate identity into one theorem. The delivered proof makes these
interfaces explicit and keeps the parent statement unchanged. No target statement or
existing definition was changed.

## New nodes

`lem-coef-semilinear-scalar-data` records existence of normalized derived change-of-rings
data for the system map and each level map.

`lem-coef-semilinear-scalar-evaluation-transpose` records the strictly subsequent level
evaluation isomorphisms and their derived-adjunction transpose equation.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
