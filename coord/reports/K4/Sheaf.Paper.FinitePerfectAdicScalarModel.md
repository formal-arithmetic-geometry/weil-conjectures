## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.finitePerfectAdicScalar_model` by a
comparison of exact functors, followed by naturality at the supplied algebraic tower
transitions. The statement and its public imports are preserved.

`FinitePerfectAdicOrdinaryScalarModel` defines the ordinary source and target functors,
proves their exactness, and constructs their specified coefficient compositors. Its
remaining theorem asks for the ordinary natural comparison and its ordinary square.
It involves module sheaves only, with no derived category, perfectness or algebraic tower.

`FinitePerfectAdicScalarModelFactors` constructs the source and completed-target
factorizations. The completed factor uses the actual universal left derived pair and
uniqueness of left derived functors. A generic localization-pasting argument identifies
the specified derived source compositor with the localized ordinary one. The main
module proves the target compositor identity, transports the ordinary square, and
checks the original normalization arrows and the actual `ofOpSequence` model arrows.

The generic coefficient-pasting and universe-lift constructions avoid expensive kernel
reduction of large specialized composites. No existing shared definition was changed. The ordinary completed realization is
an abbreviation for the constant functor followed by completed scalar extension.
Exactness comes directly from completed constant algebra flatness and its normalized
completion comparison, avoiding the later tensor-cone modules.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finitePerfectAdicScalar_model` (one of one original holes).

Added one hole:
`AlgebraicGeometry.Scheme.finitePerfectAdicOrdinaryScalar_model`, node
`lem-weil-pbc-finite-perfect-adic-ordinary-scalar-model`.
Its docstring supplies the constant-unit, finite reduction, free presentation and
pure-tensor proof. Zero rings, zero modules and empty charts are included.

The source localization theorem
`AlgebraicGeometry.Scheme.finitePerfectAdicScalarModelSource_localization` and all
factorizations and generic helpers have complete proofs. There are no holes in data.
This is a decomposition with one upper hole closed and one ordinary hole added,
not a net hole reduction and not a completed proof independent of `sorry`.

## No longer needed

No existing import or module is pruned. The attempted proof imports
`FinitePerfectAdicFreeTensorCone` and `FinitePerfectAdicOrdinaryCoefficientComparison`
were removed: they reach this item through later tower-extraction modules and would
create a cycle. The explicit ordinary composite and lower-level flatness proof replace
them; their existing declarations remain untouched. The revised packet compiled in
import order in 7.1 s, 32.6 s and 13.6 s, respectively; its line-width warning was fixed. The bounded finite-projective representative
argument of the old plan is unnecessary for this reduction: exact localization and
naturality work for arbitrary algebraic complexes. Completed constant finite reduction
is still needed by the ordinary comparison; it is not withdrawn or claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The initial artifact compile did not detect an import cycle through the later
tensor-cone modules. The delivery source-graph check caught it; stale new-node
statement dependencies on the tensor-cone module were also removed. The packet now imports
only lower-level completed-flatness and completion-comparison modules for that step.

No statement defect was found. The original DAG described a representative-level
argument but did not state the ordinary natural comparison used by that argument.
The new route separates that ordinary calculation from the formal derived passage.
Perfectness is not used in this formal passage; the original hypothesis remains intact.

The current server queue records this as a proof item. There is no current repair row
or build-error record for the item. The existing node attachment is retained.

## New nodes

`lem-weil-pbc-finite-perfect-adic-ordinary-scalar-model` records the remaining ordinary
comparison in its own module. It is strictly the module-sheaf step, and does not assert
or assume any derived comparison, tower model or normalized derived tower equation.

`lem-weil-pbc-finite-perfect-adic-scalar-model-localization` records the proved formal
localization identity and its factorizations. Its generic proof uses exact-functor
composition, whiskering, naturality and cancellation, followed by the five specified
ordinary coefficient comparisons. Named isomorphism equalities avoid expanding the
large sheaf constructions in the final pasting step. It leaves no additional hole.

`coord/changes/K4-finite-perfect-adic-scalar-model-proof-support.md` records the
item’s file-local namespace opening and composition instances, flagged by preflight
as potential interface changes. No existing exported signature or public import
changes; all three related consumers compile unchanged. No other existing module or
node is changed.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModel": "f9eed3065c2400c91f78effc0cc640274591dd16", "Sheaf.Paper.FinitePerfectAdicScalarModel": "e92b2f3c429184375088f4a211d0311e9aaaf5d9", "Sheaf.Paper.FinitePerfectAdicScalarModelFactors": "b3dda743bc55501f2fb576331942c80bc4d9b4f1"}, "results": {"Sheaf.Paper.FinitePerfectAdicActualRealization": {"hash": "d28db9d0430e4f542d0cf1d54be4806b63bf1d90", "status": "OK"}, "Sheaf.Paper.FinitePerfectAdicFlatTensorComparison": {"hash": "9e44817be565708d889cf712a13761e365ba77d2", "status": "OK"}, "Sheaf.Paper.FinitePerfectAdicOrdinaryCoefficientComparison": {"hash": "3cfb7547b7aff903f01067cbd3803257444f09dd", "status": "OK"}}, "seconds": 111, "time": "2026-10-28T07:04:29+0800", "transitive": 2, "version": 1}
```

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
