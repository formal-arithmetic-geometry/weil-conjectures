## What changed

Proved `AlgebraicGeometry.ProEtale.FiniteModelQuotient.ordinary_free_complex` with its
statement unchanged. The proof constructs the comparison on finite biproducts, checks
matrix entries in the literal lifted Pi coordinates, and constructs the isomorphism
of mapped double complexes. Private helpers prove all categorical assembly steps;
empty biproducts and the zero objects outside degrees -1 and 0 handle zero ranks.

Added `Sheaf.Paper.FiniteModelOrdinaryScalar`, proving the scalar-compatible rank-one
comparison `ordinary_scalar`. It constructs the integral model's regular-module
isomorphism, extends it along the actual quotient, and uses the existing normalized
finite-discrete constant-model comparison. The existing proved `scalar_encoded` and
`regularLift_eq` helpers identify every scalar endomorphism with its actual residue.
Linearity and naturality of module sheafification finish the commuting square.

All additional imports are proof imports. No existing definition, public import,
statement, target, source-library declaration or consumer was changed. Updated the
item node's proof route and added the rank-one node. The unit route is preserved.

Validation: the finite-biproduct/matrix/double assembly compiled, and the complete
rank-one comparison compiled without warnings in 26.9 seconds. The final import-order
compilation of both modules passed without warnings. Delivery preflight checks the
axioms and unchanged signatures.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.FiniteModelQuotient.ordinary_free_complex`
(node `lem-sfb-finite-model-ordinary-free-complex`), the item's one original hole.
Added and proved: `AlgebraicGeometry.ProEtale.FiniteModelQuotient.ordinary_scalar`
(node `lem-sfb-finite-model-ordinary-scalar`). No `sorry` remains in either delivered
module; no new hole is split off. Both delivered modules compiled together in import
order without warnings.

## No longer needed

No module is withdrawn and no existing import is removed. All three original proof
dependencies remain used: finite constant model data directly and in the rank-one
proof, regular extension comparison in the rank-one proof, and normalized encoding
through the quotient data and existing scalar comparison. There is no unused planned
subargument or node to prune. The new scalar helper uses the already proved regular
module, scalar constant encoding, scalar action, and quotient discreteness APIs.

## Where the brief, the DAG or earlier work was wrong

The shared local checkout initially lacked the item source although its node, queue,
and server source existed. There was no rework/quarantine row or current return for
this item. Restored the unchanged server source into the sandbox before proving it.
The assigned mathematical statement and its planned route required no correction.
The existing proved private helpers make the normalized rank-one calculation possible;
the mere existence of finite-free isomorphisms would not retain matrix naturality.

## New nodes

`lem-sfb-finite-model-ordinary-scalar` records the proved rank-one scalar-compatible
comparison in `Sheaf.Paper.FiniteModelOrdinaryScalar`. It is strictly the rank-one
object-and-endomorphism part of the original plan; it has no matrices, arbitrary
finite ranks or complexes. Its complete proof is delivered, rather than another hole.
No change record is needed because no existing statement or definition changed.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
