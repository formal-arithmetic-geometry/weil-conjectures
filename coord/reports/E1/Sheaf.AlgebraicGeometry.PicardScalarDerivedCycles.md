## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PicardScalarDerivedCycles.lean` from its quarantined
source and retained the complete proof of
`AlgebraicGeometry.Scheme.picard_scalar_derived_cycles`. The proof combines
`picard_connective_model_comparison` with `picard_ordinary_scalar_coordinates`, constructs
the residue additive equivalence, and transports local ordinary cycles through the derived
comparison. Its public imports are the existing `WeilConjectures` modules required for the
statement; proof-only imports are the existing Sheaf comparison and ordinary-coordinate
modules. No declaration signatures or definitions were changed.

## Proved and sorry left

This is a restoration repair: the quarantined source has zero sorries, and the restored
module has zero sorries. No holes are closed or added by this repair. The complete proof of
`AlgebraicGeometry.Scheme.picard_scalar_derived_cycles` is preserved unchanged.

## No longer needed

No imports or DAG dependencies were removed. The proof uses both declared proof dependencies
`lem-sc-picard-connective-model-comparison` and `lem-sc-picard-ordinary-scalar-coordinates`,
as well as the existing derived-model-sections and ordinary-model-cycles definitions.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery was reverted by the merge queue during a cluster restore, while its
proof was complete. The quarantined file contains the intended proof and compiles against
the current library after restoring its source-level public imports. No mathematical or
statement correction was needed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
