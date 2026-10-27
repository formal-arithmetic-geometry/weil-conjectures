## What changed

Reduced the rank-zero clause `AlgebraicGeometry.Etale.vectorBundleIntegration_zero`
in `Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent` to the explicit local
rank-zero counit calculation in the new proof import
`Sheaf.AlgebraicGeometry.VectorIntegrationRankZeroLocal`.

The private, proved helper `vectorIntegration_eq_of_normalization` uses full
faithfulness of the degree-zero embedding and the existing unique normalized
pair to show that any map with the prescribed frame restrictions is the
existing integration map. The rank-zero proof applies this to inverse exchange
followed by the identity compact-support counit, then cancels exchange.
No existing declaration signature or definition has changed.

## Proved and sorry left

This is a decomposition, not a net hole reduction: one original hole is closed
and one strictly local hole is added.

Closed original hole:
- `AlgebraicGeometry.Etale.vectorBundleIntegration_zero`
  (node `lem-pur-vector-trace-geometric-descent`), from the local calculation.

Three original holes remain unchanged in the item, all attached to
`lem-pur-vector-trace-geometric-descent`:
- `AlgebraicGeometry.Etale.vectorBundleIntegration_baseChange`;
- `AlgebraicGeometry.Etale.vectorBundleIntegration_directSum`;
- `AlgebraicGeometry.Etale.vectorBundleIntegration_swap`.

One new hole remains:
- `AlgebraicGeometry.Etale.vectorIntegration_rankZero_localIdentity`, node
  `lem-pur-vector-integration-rank-zero-local`, in its own new module.

The new theorem contains no global integration map or gluing construction. It
compares the specified exchange and identity counit on one frame to the
ordered local affine counit. The global uniqueness argument and cancellation
are proved in the item. Its statement also covers empty opens and the zero
coefficient ring; no nonemptiness or positive-rank assumptions were added.

## No longer needed

None. No existing imports, declarations, nodes or modules are withdrawn. The
other three geometric compatibility clauses still need the original route.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Step 7 described the zero-stage identity counit
but did not isolate the equality between the concrete local comparison maps.
The new node records that local step. The prescribed vector-bundle unit route
is retained.

## New nodes

`lem-pur-vector-integration-rank-zero-local`, in
`dag/nodes/sec-smooth-purity/lem-pur-vector-integration-rank-zero-local.json`,
records the local rank-zero exchange/counit equation from paragraph 2 of the
current blueprint vector-bundle purity proof. Its Lean declaration is in
`lean/Sheaf/AlgebraicGeometry/VectorIntegrationRankZeroLocal.lean`. The parent
node now names this step in its zero-rank proof and dependencies. No change
record is needed because no existing statement, definition or public import
was changed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
