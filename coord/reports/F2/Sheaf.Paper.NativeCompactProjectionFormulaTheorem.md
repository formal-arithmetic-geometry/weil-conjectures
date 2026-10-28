## What changed

Proved `AlgebraicGeometry.WeilComplex.native_compact_projection_formula` in
`Sheaf.Paper.NativeCompactProjectionFormulaTheorem`, with its complete statement unchanged.
Added private proof imports of `Sheaf.Paper.NativeProperProjectionRealization` and
`Sheaf.WeilSheaf.NativeBasicComparisons`. The proof lifts exact extension by zero to the
bounded constructible category, composes the proper comparison, open comparison and balanced
pullback compositor as natural isomorphisms, then restricts through the fully faithful inclusion.
The final component equation uses `projectionMate` and the definitions of whiskering.
Updated the assigned DAG node's proof to describe this assembly. Single-file compilation took 18 seconds. The local irreducibility
attributes avoid unfolding derived-category and closed-comparison constructions during elaboration.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.WeilComplex.native_compact_projection_formula`
(node `lem-sf-derived-weil-compact-projection-formula`).
No holes remain in the item; no holes or new statements are added.
The proper comparison is used as the declared dependency, whose existing theorem
`AlgebraicGeometry.ProEtaleWeilSheaf.native_proper_projection_realization` still has its own
hole outside this delivery. This is a proof from existing dependencies, not a new decomposition.

## No longer needed

No original import is removed, and no Lean module is withdrawn.
The assembly no longer needs separate uses of
`lem-weil-pbc-closed-immersion-base-change` or
`lem-pod-separated-finite-type-base-change`: the chosen compactification's existing
structure-map instances already supply its domain, and the proper/open comparison theorems
handle their own geometric base change. These two nodes are removed from this node's
proof dependencies; their independent users are unaffected. The remaining unit route stays.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The source-library lisse projection formula does not cover an
arbitrary derived second input. The already stated native proper and open comparisons do,
so their assembly closes the assigned hole without additional intermediate statements.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeCompactProjectionFormulaTheorem": "025b2c528a43454080169e9ddb62d387c80eaa10"}, "results": {"Sheaf.Paper.WeilCompactStructureTensorComparison": {"hash": "4af22f43d117514bcd7bffefad37846fa469680b", "status": "OK"}}, "seconds": 93, "time": "2026-10-28T09:37:50+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
