## What changed

Restored the quarantined module `lean/Sheaf/AlgebraicGeometry/CoherentFrobeniusComparison.lean`
from the current repository quarantine archive. The proof is unchanged and compiles in the
sandbox under the required module path. No imports, declarations, statements, or dependencies
were changed.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.coherent_frobenius_comparison` is proved with zero `sorry`s.
The restored module contains zero `sorry` declarations. Holes closed: 0 of 0; holes added: 0.

## No longer needed

None. The existing imports and DAG proof dependencies remain needed by the restored proof.

## Where the brief, the DAG or earlier work was wrong

The module was quarantined by the rework record because the published build lacked the object file
for `Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback`. The current dependency is present and the
restored module compiles cleanly against it. No mathematical statement or proof route was changed.

## New nodes

None.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
