## What changed
Added `polynomial_chart_stalk_flat_comparison_reverse_local_criterion`, a named intermediate local-criterion bridge. The original theorem now derives its conclusion from the first component of this bridge.

## Proved and sorry left
The original theorem is reduced to the bridge. The bridge `polynomial_chart_stalk_flat_comparison_reverse_local_criterion` remains `sorry` (node `lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux-bridge`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The existing DAG omitted the intermediate stalk-tower bridge needed to connect the ring local criterion to the geometric polynomial fibre stalk map.

## New nodes
`lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux-bridge` records the intermediate local criterion statement.

## Earlier second reading (a previous round; superseded)
The requested theorem is proved by applying the local-criterion bridge with the stalk-map locality instances; the bridge is the sole remaining node.


## Second reading by E3

1. I compared the delivered module with the repository version. The original theorem signature and all existing declarations are unchanged; only its proof and the named bridge declaration were added.
2. I compiled the module with `lcompile.py`; it succeeds. There are no axioms, unsafe declarations, or hollow definitions. The sole remaining `sorry` is the explicitly named bridge theorem recorded in the new DAG node.
3. The bridge statement is a conditional local-criterion lemma: it assumes the two stalk maps are local and concludes chart-stalk flatness. Its hypotheses and conclusion match the use in the original theorem, and its source is Tags 00R7 and 00RH.
4. The proof uses the bridge and inferred locality instances; no shorter available Mathlib or upstream declaration was found. All imports remain needed for the exposed polynomial-chart and flatness interfaces. The unit route is retained.
5. The DAG bridge node and Lean declaration agree on module, declaration, source, and proof dependency metadata.

I changed only the report by adding this second-reading record. The delivered proof closes the original theorem and leaves the bridge as the single named split-off hole.
