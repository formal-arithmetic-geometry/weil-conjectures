## What changed

Completed the three remaining proofs in `Sheaf.Paper.PbcRationalTransport`.
Generic exactness specializes `ScalarLocalization.extension_exact` from the existing
semilinear localization module to the identity ring map, identifying the two extensions
by uniqueness. The scheme theorem transfers linearity through the canonical coefficient
ring equivalence and handles the two localization module instances explicitly. The exchange
theorem uses compatibility with composition and natural-transformation uniqueness.

Added the proof-only import `Sheaf.CategoryTheory.SemilinearScalarLocalization` and four
private proved helpers. Updated the existing node's proof, proof dependencies and origin
to record this route. All existing statements and definitions are unchanged. Change record:
`coord/changes/pbc-rational-transport-proof-imports.md`.

## Proved and sorry left

Closed 3 of 3 holes:
- `CategoryTheory.ScalarLocalization.transport_exact`;
- `WeilConjectures.pbcRationalTransport`;
- `WeilConjectures.pbcRationalExchange`.

All realize `prop-weil-pbc-rational-transport`. Zero holes remain in the item, zero were
added and zero were split off. The existing localization triangulation and integral
triangulation dependencies remain in use; this delivery proves from their stated APIs.
The module compiled without warnings in 19.2 seconds before the final delivery checks.

## No longer needed

Removed the proof-only imports `Mathlib.LinearAlgebra.TensorProduct.Tower`,
`Mathlib.Algebra.Homology.DerivedCategory.Linear` and
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`; the remaining imports suffice.
No declared dependency node or module is pruned. The generic exactness proof reuses
`lem-pur-semilinear-scalar-localization`, whose module already proves the required
localization descent and shift normalization; this avoids duplicating that argument.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. Scheme tensor formulas elaborate through different
scalar-action instances. The private module-instance equality and explicit Hom-module
arguments prove their agreement without unfolding the full derived-category realization.
The original DAG did not list the existing semilinear extension theorem now reused in
step 4; its proof and dependency list have been updated. No unit route is bypassed.
The change record documents the static interface checker flag for private helpers and
proof-only imports; the public interface is preserved.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
