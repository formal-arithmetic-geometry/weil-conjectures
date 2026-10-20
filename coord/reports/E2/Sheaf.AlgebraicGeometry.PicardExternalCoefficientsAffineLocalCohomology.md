## What changed

Restored `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineLocalCohomology`
from its exact quarantine source, replacing the stale public import of
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` with
`WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`.
The former is now an empty withdrawn module. The latter provides the operations
and public statement dependencies after the upstream move.

Every declaration, signature, docstring and proof body is preserved verbatim.
The original failed at public `X.Modules`; the repaired module compiles cleanly
with `lcompile.py` in 3.6 seconds. No proof-route change or new node is needed.
The change record is
`coord/changes/picard-affine-local-cohomology-upstream-import.md`.

## Proved and sorry left

Zero holes before, zero holes after; zero closed and zero added. This is the
assigned quarantine repair, not a new proof or decomposition.

The existing complete proof of
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_affine_local_cohomology`
(node `lem-sc-picard-external-coefficients-affine-local-cohomology`) and its
private `scalarCechIso` helper are retained. No declaration in the delivered
module contains `sorry`; no additional Lean module is delivered.

## No longer needed

Removed the empty compatibility import
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, replacing it
with its actual adopted-source counterpart. No mathematical dependency or node
is pruned: all of the existing affine-cover, Cech comparison and exact-tensor
proof route remains in place. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned repair with zero holes. The stale public import was
not updated when the operations module moved upstream; this caused the
quarantine compile error in `coord/rework.tsv`. The DAG statement and proof
plan agree with the restored proof, so no node edit is necessary. No target
statement or definition changes.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
