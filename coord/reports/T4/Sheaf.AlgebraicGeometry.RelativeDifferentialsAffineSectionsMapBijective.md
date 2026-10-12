## What changed

The target theorem now combines separately stated injectivity and surjectivity lemmas. Two
new modules state those strictly smaller parts, and the target imports them. Their proofs remain
explicit stage-3 obligations because the affine comparison argument is not present in the library.

## Proved and sorry left

The target declaration `relativeDifferentials_affine_sections_map_bijective` is proved by
constructing `Function.Bijective` from the two component theorems. Sorries remain in
`relativeDifferentials_affine_sections_map_injective` and
`relativeDifferentials_affine_sections_map_surjective`, each with its corresponding new DAG node.

## No longer needed

No imports or existing DAG dependencies were removed. The original affine map module remains
needed to type the hypotheses.

## Where the brief, the DAG or earlier work was wrong

The planned proof is substantially longer than the available declarations; it requires the
full affine comparison construction. I split its injectivity and surjectivity consequences into
strictly smaller statements so the target has a compiling reduction.

## New nodes

`lem-sc-relative-differentials-affine-sections-map-injective` and
`lem-sc-relative-differentials-affine-sections-map-surjective` are added under
`dag/nodes/sec-picard-framework/` and are stated by the two new modules.

## Earlier second reading (a previous round; superseded)

The component statements are strict parts of the target and their conjunction has exactly the
target type. The unit route is retained; the unresolved affine comparison work is isolated in
the two new nodes.

## Second reading by T4

1. I compared the delivered target module and the repository version. The theorem signature and all existing declarations are unchanged; only proof imports and the target proof body changed. Verdict: pass.

2. I compiled all four sandbox modules with `lcompile.py --all`. They compile without errors or warnings. The target has no `sorry`; the two intentionally split component theorems retain exactly one named `sorry` each, with matching DAG nodes. Verdict: pass.

3. I searched the library and Mathlib for an existing affine relative-differentials comparison, injectivity, or surjectivity theorem. The available declarations provide the affine Spec comparison and universal-property infrastructure, but no theorem closing either component. The two split statements are true strict parts of bijectivity and are required by the target proof; they do not merely restate the target. Verdict: pass.

4. I checked the proof from the top downward. The target constructs `Function.Bijective` directly from the separately stated injectivity and surjectivity results. The unit route through the affine comparison and universal property is retained; no definition or target statement was changed. Verdict: pass.

5. I checked the two new DAG nodes against their Lean declarations, including statements, sources, proof dependencies, blueprint links, and module records. The node proofs describe the corresponding affine comparison arguments, and the unit record remains unchanged. Verdict: pass.

I changed the report by recording this second reading and clarified that the delivery is a decomposition: one target hole is closed while the two strictly smaller component holes remain open.
