## What changed

Replaced the sole `sorry` in
`lean/Sheaf/AlgebraicGeometry/PrincipalOpenCechSingletonAugmentationComponent.lean`
with a proof of `AlgebraicGeometry.principalSubsetInsertOne_singleton_augmentation`.
Its signature, visibility, docstring and imports are unchanged.

Two proved private helpers make the existing DAG argument explicit:
`sectionTransport_restriction` applies the presheaf naturality of the inverse
`Scheme.Modules.overFunctorEquiv`, then identifies the two restriction composites
by functoriality and uniqueness of morphisms between opens; `insertOne_reindex`
eliminates independent degree equalities and unfolds the explicit insertion.
The main proof identifies the singleton intersection, moves the coefficient equality
through restriction by naturality, applies the reindexing helper, cancels the
extension isomorphism in `alternatingCechZero`, and uses section transport naturality.
This implements the node's existing proof and keeps the unit route.

The argument permits all integer degrees and the zero ring. With `r = 0` the
nonempty subset parameter is uninhabited. No covering or nonvanishing assumptions
are introduced, and both helpers are proved rather than postponed.

## Proved and sorry left

Closed: `AlgebraicGeometry.principalSubsetInsertOne_singleton_augmentation`
(node `lem-sc-principal-open-cech-singleton-augmentation-component`): 1 of 1 holes.

Remaining in the assigned module: none. Holes added: none. Both private helpers
are completely proved. This is a proof, not a decomposition into further holes.

## No longer needed

None. The sole existing public import,
`Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion`, is required by the
statement. No imports were added, and no planned nodes or modules are pruned.
The existing DAG proof and dependency list still describe the implemented route.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib's `restrictAppIso` is definitionally the identity comparison, so its
restriction compatibility is used by definitional reduction while applying the
presheaf naturality of the inverse `overFunctorEquiv`.

## Second reading by J3

1. The delivered module was diffed against the repository version. The public
   theorem signature, visibility, docstring, and existing import are unchanged;
   only the proof body and private proof helpers were added. Verdict: pass.
2. The module compiles with `lcompile.py`; there are no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The proof
   uses only ordinary definitions and the permitted library axioms. Verdict: pass.
3. The two private helpers are strictly internal reductions (restriction
   naturality and degree/index reindexing), are fully proved, and add no nodes or
   statements. The public theorem proves exactly the existing node statement.
   Verdict: pass.
4. The proof follows the node's singleton route: identify the singleton
   intersection, use naturality, cancel the extension isomorphism, and apply the
   total inclusion. No shorter imported declaration was found, and the required
   import remains minimal. Verdict: pass.
5. The DAG node's theorem, proof route, dependencies, and unit realization agree
   with the Lean proof; no dependency or unit record needed adjustment. Verdict:
   pass.

Changed only the proof in the assigned module and appended this review record;
no holes were added and no imports or DAG nodes were pruned.
