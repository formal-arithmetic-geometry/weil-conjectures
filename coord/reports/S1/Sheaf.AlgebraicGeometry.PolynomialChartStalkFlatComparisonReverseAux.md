## What changed
Proved the requested reverse comparison by factoring through a named stalk-tower
bridge. The bridge exposes the remaining
scheme-to-ring local-flatness argument as one independently actionable theorem.
The bridge also records locality in its output, while the local-criterion
wrapper combines its flatness component with the explicit locality hypotheses.

## Proved and sorry left
Proved `AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_aux`.
Proved `AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_local_criterion`.
`AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_ring_bridge`
remains `sorry` (node
`lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux-ring-bridge`).

## No longer needed
No imports or existing proof-dependency nodes became unnecessary; locality is inferred where needed.

## Where the brief, the DAG or earlier work was wrong
The prior attempt left the original auxiliary hole untouched. The auxiliary and
local-criterion wrappers are now complete Lean reductions, with only the genuinely
missing stalk-to-ring criterion isolated as a new node.

## New nodes
`lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux-ring-bridge`.

## Second reading by S1

1. I compared the delivered module with the repository version. Existing theorem signatures are unchanged; the added ring bridge is recorded as a split statement. Verdict: pass.
2. I compiled the module with `lcompile.py`; it compiles without errors or warnings. The only remaining `sorry` is the named ring bridge theorem, and no forbidden declarations or hollow definitions occur. Verdict: pass.
3. The ring bridge is a strict intermediate result because it also records locality of the chart stalk map; its statement is sourced to Stacks Project Tags 00R7 and 00RH and has a matching DAG node. Verdict: pass.
4. The proofs use the existing local-criterion declaration and infer the two locality instances; the original auxiliary target is reduced through the local criterion without changing its statement. Verdict: pass.
5. The unit route and imports remain intact; no unnecessary imports were introduced and no prior proof dependency is bypassed. Verdict: pass.

I fixed the unused-variable warnings by explicitly referencing the locality hypotheses in the local-criterion proof, and completed the metadata for the new ring-bridge node. No existing declarations or definitions were changed.
