## What changed

Completed the nine theorem proofs in `Sheaf.AlgebraicGeometry.VectorTraceGeometry`,
preserving every existing declaration's signature and every definition's body.
Private helpers establish the mapping property of the symmetric-algebra bundle
for an arbitrary source scheme. They extend a linear map to a sheaf-algebra map,
construct the associated scheme map on affine opens, and glue it. Equality follows
from the symmetric-algebra universal property and affine-local extensionality.

The tensor-pullback adjunction then supplies the base-change pullback. Intersecting
frame covers proves the rank of a biproduct. The biproduct mapping property supplies
the direct-sum pullback, and uniqueness of pullbacks gives the prescribed sum
isomorphism. The swap uses inverse symmetric-algebra maps; rank zero uses the
existing local trivializations and Zariski locality of isomorphisms. Updated the
existing node's proof route and proof dependencies. No other module is changed.

## Proved and sorry left

Closed all nine original holes, in namespace `AlgebraicGeometry.VectorTraceGeometry`:
`existsUnique_map`, `map_spec`, `baseChange_isPullback`, `biprod_rank`,
`existsUnique_sumIso`, `sumIso_isPullback`, `swap_isPullback`, `zero_isIso`, and
`zero_isPullback`. Their node is `def-pur-vector-trace-geometry`.

No holes remain in the item. No holes were added; no statement was split off.
All added private helpers are proved. The existing choices of bundle maps and the
sum isomorphism retain their original unique-existence specifications.

## No longer needed

The proof does not need the private import
`Sheaf.AlgebraicGeometry.RelativeSpecBaseChange` or its theorem node
`lem-weil-pbc-relative-spec-base-change`: the bundle mapping property and module
adjunction prove the required square directly. This removes that proof import
only; the general theorem and its module remain available to other consumers.
No existing declaration, module, or unit route is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original docstrings suggested applying general relative-Spec base change.
The direct mapping-property proof is shorter for these particular bundles and
also handles arbitrary test schemes, rank zero, and empty bases. The statements
and definitions require no repair.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
