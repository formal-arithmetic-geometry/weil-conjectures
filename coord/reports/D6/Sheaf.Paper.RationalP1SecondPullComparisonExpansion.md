## What changed

Filled the only hole in `Sheaf.Paper.RationalP1SecondPullComparisonExpansion`,
`AlgebraicGeometry.ProEtale.RationalP1.second_pull_comparison_inv_expansion`.
The proof identifies the supplied residue-field invertibility families with the
canonical families used in `secondPullComparison` by `Subsingleton.elim`, substitutes
the equalities, unfolds that definition, and finishes by reflexivity.
The existing mapped expansion proof is retained. Both signatures and all imports
are unchanged. The two corresponding DAG proof records now describe the Lean proofs.
The unit route is unchanged.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtale.RationalP1.second_pull_comparison_inv_expansion`
(node `lem-sfb-rational-p1-second-pull-comparison-expansion`).
The already proved `second_pull_comparison_inv_map_expansion` now depends on a
completed expansion proof (node
`lem-sfb-rational-p1-second-pull-comparison-inv-map-expansion`).
No holes remain in the item; no holes or split statements were added.
Single-file compilation passed without warnings in 20.1 seconds.

## No longer needed

None. The sole public import, `Sheaf.Paper.RationalP1SecondPullComparison`, supplies
the fixed definitions required by the statements. No module, node, or import is
withdrawn, and no extra proof import is needed.

## Where the brief, the DAG or earlier work was wrong

The generic DAG coherence plans did not specify the only non-definitional issue:
`Invertible` is a type rather than a proposition, so the supplied instances need not
be definitionally equal to those installed internally by `secondPullComparison`.
Their uniqueness gives explicit equalities and makes the planned definitional proof
work. The mapped-expansion node described an unfinished coherence obligation even
though its existing Lean proof was already a rewrite from the first theorem;
its proof record now describes that rewrite. No mathematical statement was changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SecondPullComparisonExpansion": "597a5dbc6df1ebda8f7b2bec3edc520bcf4800c2"}, "results": {}, "time": "2026-10-28T11:54:33+0800", "transitive": 0, "version": 1}
```

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
