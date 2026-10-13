## What changed
Added a proof-only import of `PuncturedMatchingChartRestrictionLeftInverse` and proved `puncturedMatching_chart_section_injective` from its left-inverse property. Added the intermediate module and DAG node.

## Proved and sorry left
The target theorem `puncturedMatching_chart_section_injective` is proved. The intermediate theorem `puncturedMatching_chart_restriction_leftInverse` remains `sorry`, with node `lem-sbc-punctured-matching-chart-restriction-left-inverse`.

## No longer needed
None; both original proof-dependency imports remain available to the intermediate comparison statement.

## Where the brief, the DAG or earlier work was wrong
The original plan omitted the ring-homomorphic left-inverse statement needed to express the localized chart comparison in Lean.

## New nodes
`lem-sbc-punctured-matching-chart-restriction-left-inverse`: left inverse for the punctured matching chart restriction.

## Earlier second reading (a previous round; superseded)
The target proof compiles and preserves the target signature. The added statement is a localized chart comparison left-inverse and is strictly usable to derive the target by applying it to zero.

## Second reading by D3

1. **Statements unchanged.** Compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; the only interface addition is the separately declared split-off theorem, recorded by its new node.
2. **Proof validity.** Compiled both delivered modules with `lcompile.py`; the target proof has no `sorry`, and the only remaining `sorry` is the named intermediate theorem `puncturedMatching_chart_restriction_leftInverse`. The target proof uses its ring-homomorphic left-inverse and `map_zero`; no forbidden declarations occur.
3. **Split-off statement.** The intermediate theorem is a genuine stronger reduction (existence of a ring-homomorphic left inverse on the image), not a restatement of injectivity. Its docstring gives the source and construction, and its DAG node matches the Lean declaration.
4. **Pruning and route.** The proof-only import of `PuncturedMatchingChartRestrictionLeftInverse` is required. The existing formal-glueing import remains available for the split-off module; no unused import was removed from the target. The unit route is preserved through the new intermediate node, whose proof dependency is the formal-glueing localization node.
5. **DAG consistency.** Updated the target node's `proof`, `proof_deps`, and `proof_origin` to record the actual left-inverse reduction; the new node metadata and statement match the Lean source.

Changed the target proof metadata and added the above second-reading audit; no mathematical statement or definition was altered.
