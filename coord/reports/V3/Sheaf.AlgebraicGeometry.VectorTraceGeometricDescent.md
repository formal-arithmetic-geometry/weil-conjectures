## What changed

Reduced `AlgebraicGeometry.Etale.vectorBundleIntegration_swap` to the new
single-frame calculation `vectorIntegration_swap_local`, imported privately
from `Sheaf.AlgebraicGeometry.VectorIntegrationSwapLocal`.

The global proof constructs the isomorphism consisting of actual compact-support
exchange followed by the specified coefficient isomorphism. It transports the
existing trace back along its inverse. On any frame, restriction of biproduct
braiding and the explicit equality of ranks supply the other frame. The existing
trace's normalization and the local calculation show the transported map has
`VectorIntegrationNormalization`. The already proved uniqueness helper identifies
it with the actual integration, and the proof cancels exchange.

A private generic-morphism helper elaborates projection invertibility without
repeatedly unfolding the vector-bundle geometry. Explicit isomorphism instances
and local irreducibility keep the derived localization behind its API. This
addresses the 60-second timeout encountered compiling the unchanged item: in
particular the last symmetry factor now uses an explicit `Functor.map_isIso`
argument instead of an expanding instance search.
No existing public signature, definition, public import or instance is changed.

## Proved and sorry left

This is a decomposition, not a net hole reduction: one of the original three
holes is closed using one new, strictly local hole.

Closed original hole: `AlgebraicGeometry.Etale.vectorBundleIntegration_swap`,
node `lem-pur-vector-trace-geometric-descent`.

Original holes remaining in the item, both attached to that node:

- `AlgebraicGeometry.Etale.vectorBundleIntegration_baseChange`;
- `AlgebraicGeometry.Etale.vectorBundleIntegration_directSum`.

New hole:

- `AlgebraicGeometry.Etale.vectorIntegration_swap_local`, node
  `lem-pur-vector-integration-swap-local`, in its own new module.

The new statement refers only to the explicit local affine trace and a map k
whose restriction is prescribed on one supplied frame. It contains no globally
glued integration, no gluing theorem, and no global normalization hypothesis.
The global uniqueness argument and actual exchange cancellation are proved in
the item. Empty frames, rank zero and zero coefficient rings satisfy the same
local comparison; no extra nonemptiness assumption is used.

## No longer needed

None. No original import, declaration, node or module is withdrawn. Base change
and ordered multiplication retain the existing dependency route. Block exchange
uses the same linear trace invariance and exchange calculation, isolated locally.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Step 7 described coordinate invariance but did not
provide the concrete cross-bundle, single-frame exchange equation as an available
Lean declaration. The new node states precisely that calculation. The unit route
is retained. The unchanged module initially exceeded the compile limit in its
projection-isomorphism proof; the delivered generic helper avoids recomputing
the large geometric definitions there.

## New nodes

`lem-pur-vector-integration-swap-local`, in
`dag/nodes/sec-smooth-purity/lem-pur-vector-integration-swap-local.json`, records
the frame/exchange calculation from paragraph 2 of the current blueprint
vector-bundle purity proof and Step 7 of geometric descent. Its declaration is
in `lean/Sheaf/AlgebraicGeometry/VectorIntegrationSwapLocal.lean`. The parent's
proof and proof dependencies now record the normalization-uniqueness reduction.
No change record is needed: no existing statement, definition or public import
has changed.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
