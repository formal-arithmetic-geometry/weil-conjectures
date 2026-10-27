## What changed

Proved `CategoryTheory.ConstantCompletion.coherentRingInverseImage_exists` in
`Sheaf.CategoryTheory.GeometricRingInverseImage`, with its statement and the public
`SheafOfModules.RingInverseImage` structure unchanged. Added private proof imports
of `Sheaf.CategoryTheory.InverseImageRingFunctor` and
`Sheaf.CategoryTheory.RouteInverseImageConstantComparison`.

The former supplies the ring lift and operation-comparison equations. Two proved
private categorical lemmas derive arbitrary binary-operation and constant-operation
graphs from those equations. Sectionwise extensionality supplies the source graph
factorizations; evaluating the resulting morphism equalities proves all four
ring-operation fields. Naturality is the underlying natural isomorphism's naturality.
The latter existing theorem then supplies the natural constant-ring isomorphism.
The two namespaces' existing ring-presentation records are connected by copying their
identical five fields inside this existential proof, with no new public definition.

Updated the item's theorem node's proof, proof_deps and proof_origin to this route.
The source read was Stacks `sites.tex`, proposition
`proposition-functoriality-algebraic-structures-topoi`, including its sextuple
paragraph for rings (Tag 00YV). Both reused nodes belong to `sk-thm-rationality`:
`lem-route-inverse-image-ring-functor` and
`lem-route-inverse-image-constant-comparison`. They are tools for the identical
algebraic transport and constant-object subarguments here; they do not replace any
step of the proper-base-change unit. Maintainer tool-use recording is requested at
review/landing; no worker additions to tool_uses have been made.

Validation: `lcompile.py` compiled the final item without errors or warnings in
7.9 seconds, compiling the two current unpublished dependencies in its private
overlay. Both proposed proof imports passed `tools/import_direction.py may`.
All delivered Lean lines have at most 100 characters.

## Proved and sorry left

Closed the one hole in
`CategoryTheory.ConstantCompletion.coherentRingInverseImage_exists`
(node `lem-weil-pbc-coherent-ring-inverse-image`).
Zero sorries remain in the item; zero holes added or split off.
The two private transport lemmas are proved completely.
The imported statements `CategoryTheory.inverseImage_ring_functor` and
`CategoryTheory.inverseImageConstantComparison` retain their pre-existing holes
in their own modules; this delivery proves the item from those existing statements.

## No longer needed

No modules withdrawn, no imports removed, and no globally pruned nodes.
The item's direct proof dependencies on
`lem-weil-pbc-sheaf-algebraic-structures-objects`,
`lem-weil-pbc-finite-product-ring-functor`, and
`def-weil-pbc-constant-sheaf` are replaced by the two existing higher-level statements.
The constant-sheaf node remains a statement dependency, and the algebraic-object
and finite-product constructions remain needed transitively by the ring-lift route;
no claim of global pruning is made for them.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid, but existing stated lemmas already package
the ring-functor and constant-comparison constructions. Reusing them leaves only
the generalized-section graph calculation, naturality and existential assembly here.
The source/target operation-graph identities use neither global-section generation
nor nonempty sites or nonzero rings; they hold for every test sheaf, including on
degenerate sites and for the zero ring. No hypotheses or conclusions were changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.GeometricRingInverseImage": "013e1e92d2b68770a032ab049171c2941150d63e"}, "results": {"Sheaf.Paper.ConstantCompletionInverseImageExists": {"hash": "f466df39841f8d9f78db27f62245b6a706c3cc56", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T05:07:42+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
