## What changed

Restored the assigned module from its quarantine source and replaced the body of
`AlgebraicGeometry.Etale.etaleOpenMixedTensorScalar`. Its statement and public
imports are unchanged. The proof packages the scalar tensor comparisons as
bifunctor isomorphisms, identifies the fixed open/scalar comparison by iterated
mates, transports the projection map from left-derived to exact restriction, and
applies the existing `CategoryTheory.Adjunction.projectionMap_mate`. Explicit
inverse cancellations give the original displayed orientation. The private proof
imports are `WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat` for
that mate theorem, the new restriction statement module for its tensor hypothesis,
and `import all Sheaf.Paper.EtaleProEtaleScalarMate` for the existing instance
caches. The caches and irreducibility attributes are local to this file.

The remaining restriction/tensor square is stated in the new module
`Sheaf.SixFunctors.EtaleOpenScalarRestrictionTensor`. It contains no extension by
zero, open projection morphism, or open/scalar q comparison. The parent supplies
the complete adjunction argument from this square. The new statement is exactly
the monoidality/descent step of the original proof plan, rather than a renamed
mixed projection assertion.

Only the item module, its node, the new statement module and its node are changed.
No shared definition, existing statement, source-library declaration, or target
is changed. Proof imports expose no new declarations to consumers.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.etaleOpenMixedTensorScalar`
(node `lem-coef-etale-open-mixed-tensor-scalar`), conditional on the restriction
square. Added one hole in
`AlgebraicGeometry.Etale.etaleOpenScalarRestrictionTensor`
(node `lem-coef-etale-open-scalar-restriction-tensor`). There are no holes in the
item module. This is a decomposition: one upper hole closed, one strictly smaller
hole added, net zero holes closed. All private helpers are proved.

Both delivered modules were accepted by `lcompile.py`: the new restriction
statement in the sandbox import-order compile, and the finished item in its
subsequent single-file compile. The final item compile returned exit code 0,
without warnings, and reported 11.2 seconds. The final delivery runs the server
preflight and axiom/sorry checks.

## No longer needed

The original file had only its statement import, which is retained. The proof
needs neither the preservation theorem of
`Sheaf.SixFunctors.EtaleOpenKFlat` / `lem-coef-etale-open-kflat` nor a K-flat model
of extension by zero. The projection-map mate theorem handles this passage for
arbitrary bifunctors, so this planned dependency is removed from the item's
proof dependencies.

`lem-pur-derived-change-of-rings` and
`lem-weil-pbc-site-derived-tensor-descent` are no longer direct proof dependencies
of the item: their remaining role is the restriction tensor square, and they are
recorded on the new node. These nodes and their modules remain needed there; no
global withdrawal is claimed. No existing module is withdrawn, and no source
library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The missing item was quarantined for a build failure, not withdrawn. Its archive
and Lean attachment were preserved. The dependency build issue does not authorize
withdrawing the assigned assertion.

The exact-functor tensor-square APIs do not cover arbitrary coefficient scalar
extension: their preservation-of-finite-limits assumptions would add an invalid
flatness requirement. The remaining normalization step is therefore stated using
the original arbitrary ring map. The unit's statement and route are retained. The already-proved
`lem-asd-adjunction-projection-map-mate` is used as a generic categorical tool:
it supplies the formal identity for arbitrary bifunctors and replaces no step
of this unit. The maintainer's `tool_uses` approval list is unchanged.

The existing created-node ancestry uses module names in `created.item`, so
`tools/blueprint_refs.py ancestor` returns no ancestor for this item. The new
node records the actual blueprint ancestor `thm-coef-finite-hom`, with the three
intervening open-comparison nodes in `via`; the existing nodes are not changed
outside the allowed proof fields.

## New nodes

`lem-coef-etale-open-scalar-restriction-tensor`, in
`dag/nodes/sec-six-functors/`, realizes the ordinary scalar/restriction monoidality
and K-flat descent portion of the parent plan. Its single public statement uses
the existing normalized comparisons, with a source and full proof in words. The
new square is tested conceptually on the identity open, empty schemes, zero rings,
and nonflat coefficient maps; none requires an extra assumption. No change record
is needed because no existing interface or definition changes.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
