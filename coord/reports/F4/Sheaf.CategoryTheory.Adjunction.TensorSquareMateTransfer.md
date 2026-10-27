## What changed

Filled both proofs in `Sheaf.CategoryTheory.Adjunction.TensorSquareMateTransfer` without changing
any existing signature, definition, public import or docstring. Added two private helpers: the
projection's counit transpose and its natural transformation on the product category.

The main proof follows all six existing node steps. It computes the first transpose using
`mateEquiv_counit`, naturality of `a`, and the projection transpose. For the second transpose,
naturality of `muP`, the same mate identity, and naturality of `dk` reduce to the assumed mixed
square. Bifunctoriality cancels `theta.hom` with `theta.inv`. The first path is natural by composing
the naturality equations for `di`, the projection, and the mate. Injectivity of the inverse
adjunction hom equivalence identifies the two paths. The ringed-site normalization is definitional.

## Proved and sorry left

Closed the two original holes:

- `CategoryTheory.tensorSquare_mate_transfer`.
- `SheafOfModules.tensorSquareProjectionMap_ringed`.

Both belong to `lem-sf-tensor-square-mate-transfer`. No holes remain in the item; no holes were
added or split off. The private helpers have complete proofs/constructions.

## No longer needed

None. No imports were removed, and no node or module is withdrawn. The original node's six-step
route and its statement dependencies are retained. The ringed-site equality uses the definitions
provided through `Sheaf.Paper.ProjectionMateExact` and needs no exactness theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The ringed-site equality has a shorter proof than the
suggested injectivity argument: the two displayed projection definitions are definitionally equal.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
