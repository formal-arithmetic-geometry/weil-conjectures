## What changed

Restored `lean/Sheaf/Paper/CommonStageFiniteObjectLifting.lean` from the quarantine
path recorded in `coord/rework.tsv`. Repaired the invalid-projection errors by
moving the object formula, representative formula and stage-change calculation
into proved private helpers: `componentObject_spec`, `componentMap_spec`, and
`stageChange_spec`. Their rational stage objects remain visible during
elaboration. The large main theorem keeps `Stage` locally irreducible and calls
these helpers directly.

Kept large scalar-localization and full-subcategory category instances locally
irreducible, and made `catToReflQuiver` locally implicit-reducible. Reduced only
the product/pullback wrappers in the representative calculation. Removed the
initial settings disabling respect for transparency; retained synchronous
elaboration. All public signatures, definition bodies, imports and docstrings
are preserved verbatim. The two original generic private helpers are preserved.

The complete existing argument still uses the published pullback specification,
the exact finite supremum of coefficient fields, stagewise essential surjectivity,
and explicit representative stage-change isomorphisms. Updated only the node's
proof-origin note to record the repair. Change record:
`coord/changes/B3-common-stage-finite-object-elaboration.md`.

Validation: the complete proof compiled via `lcompile.py` in 9.3 seconds with
profiling enabled; the submitted file removes the profiling options. The exact
public theorem statement, public definition texts, import list, zero hole count
and 100-character line bound were checked against the quarantine source.
Delivery performs the final clean compile and preflight.

## Proved and sorry left

This is a repair with zero original holes: closed 0 of 0 sorries, added 0,
and 0 remain. The complete proof of
`WeilConjectures.PurityCommonStageLifting.finite_object_lifting`
(node `lem-pur-common-stage-finite-object-lifting`) is retained. All five private
helpers are proved. No split-off statements or new axioms.

The existing imported pullback specification has its own proof obligation; this
repair does not claim to close that dependency. The finite-supremum argument
includes an empty index type, an empty additional list, repeated fields and
identity inclusions without introducing extra hypotheses.

## No longer needed

None. No import, declaration, dependency node, module or unit step is removed.
The quarantined module's Lean attachment and all dependencies are preserved.
The library and quarantine trees contain no current direct Lean importers of
this module; its DAG parent `lem-pur-finite-product-field-coefficient-descent`
continues to cite it, so it is restored rather than withdrawn. No consumer
adaptation is required because no public interface changed.

## Where the brief, the DAG or earlier work was wrong

The archived proof has no sorries but fails current compilation: its local
irreducibility of `Stage` prevents Lean from validating underlying-object
projections while applying the imported pullback and transition specifications.
The initial reproduction reported invalid projections at the object formula,
the representative formula and the stage-change isomorphism construction.
Allowing Stage to unfold throughout the large theorem made elaboration too slow;
profiling identified the category-instance expansion and the stage-change
application. Private proved helpers and local category-instance sealing reduce
the complete compile to 9.3 seconds. This is an elaboration repair, with no
mathematical statement correction. The recorded proof and unit route are retained.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
