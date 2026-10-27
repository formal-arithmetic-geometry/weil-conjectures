## What changed

Proved `AlgebraicGeometry.Scheme.Modules.unitCoherentRawClass_evaluation`.
The proof imports two proved intermediate Sheaf modules: the explicit raw evaluation
formula and the generic evaluation cancellation formula. The original theorem statement
and all existing definitions are unchanged.

## Proved and sorry left

Closed the one existing hole, `AlgebraicGeometry.Scheme.Modules.unitCoherentRawClass_evaluation`.
No sorries remain in the item or in the two new intermediate modules.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.SheafHDerivedNaturality` from the
item module; it is imported by the map intermediate module. No DAG dependency was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is correct. The nested raw evaluation equivalence exceeded the
per-file checker when reduced in the item; its two strictly simpler component identities
are now proved in separate modules and combined by the item.

## New nodes

Added `new-unit-coherent-raw-evaluation-formula-aux` and
`new-unit-coherent-raw-evaluation-formula-map-aux`, each a complete intermediate theorem
used by the item proof.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
