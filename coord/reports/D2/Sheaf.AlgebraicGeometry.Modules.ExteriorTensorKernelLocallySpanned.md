## What changed

Retained the complete proof of
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_locally_mem_span`.
The proof compares `exteriorSheaf` with the adopted upstream `exteriorPower`,
uses the proved upstream stalk-kernel span theorem, descends span membership to a
neighborhood, and transports the relation span back through the comparison.  The
module documentation now records this adopted proof route.  The public statement,
imports, visibility, and DAG statement record are unchanged.

Validation with `lcompile.py` succeeds for the delivered module.

## Proved and sorry left

The assigned module contains zero `sorry`s before and after this delivery.  Holes
closed: 0.  Holes added: 0.  No theorem was split off.

## No longer needed

None.  The adopted upstream `ExteriorTensorStalkKernelSpan` theorem, the exterior
sheaf comparison infrastructure, and the local stalk-span helpers are all used by
the retained proof.  No imports, declarations, nodes, or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The current assignment is a zero-hole synchronization/review item: the module's
complete proof was already present in the shared tree.  Replacing it with a new
admission would lose the existing proof.  The delivered file therefore preserves
the proof and documents its current upstream route; no statement or dependency
record is changed.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
