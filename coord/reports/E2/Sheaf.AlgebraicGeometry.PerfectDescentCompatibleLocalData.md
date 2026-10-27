## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PerfectDescentCompatibleLocalData.lean`
from its exact quarantine path in `coord/rework.tsv`. Replaced its public import
of the withdrawn `Sheaf.AlgebraicGeometry.PerfectDescentOnOpen` with the public
import of `WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen`, the module
recorded on `def-pc-perfect-descent-on-open`.

The archived theorem `AlgebraicGeometry.perfect_descent_compatible_local_data`
keeps its exact signature and complete proof. It obtains compactness and the
morphism-property instances, applies `perfect_descent_common_local_models`,
then `perfect_local_models_eventually_compatible`, and returns the composite
stage inequality. Both declared proof dependencies are used, so the DAG proof,
proof dependencies, Lean attachment and unit route require no change.

The restored item compiles cleanly through lcompile.py (8.9 seconds). The only
archived consumer is PerfectDescentOpenUnion; it is checked separately after
correcting its own stale predicate import in a temporary sandbox copy. That
two-file check compiled the restored module in 14.9 seconds and the consumer in
36.4 seconds, with no errors or warnings. The temporary copy is removed before
delivery; no consumer signature or source is delivered.

Change record: `coord/changes/perfect-descent-compatible-local-data-public-import.md`.

## Proved and sorry left

This is a zero-hole import repair, not a new proof or decomposition.
`AlgebraicGeometry.perfect_descent_compatible_local_data` already has a complete
proof in the quarantine archive; this delivery restores and recompiles it.
Holes before: 0. Holes closed: 0. Holes added: 0. Holes left: 0.
No declaration with `sorry` is introduced or delivered. Existing dependencies
retain their own proof obligations; none is moved into this module.

## No longer needed

Removed the import of `Sheaf.AlgebraicGeometry.PerfectDescentOnOpen`, an empty
withdrawn module; the definition is imported from its authoritative source
module instead. Both private proof imports and every other statement import
remain used. No mathematical node or required module is pruned, and no Lean
attachment or quarantined archive is withdrawn.

LeanFinder found only general affine-limit and scheme-gluing lemmas; Loogle
found the generic adjunction API; msearch grep found no exact Mathlib theorem.
Local rg found the archived theorem and its quarantined OpenUnion consumer.
There is no reason to replace the existing two-dependency proof route.

## Where the brief, the DAG or earlier work was wrong

The rework record accurately diagnoses the stale public import after the
upstream migration. The archived module's empty Sheaf import no longer exposes
PerfectDescentOnOpen to public signatures. Publicly importing the recorded
WeilConjectures module repairs that error without changing the mathematics.
The generic brief's expectation of holes does not apply to this repair: the
archive contains zero sorry. No new nodes or statement corrections are needed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
