## What changed
Added two intermediate theorem modules splitting the finite affine Cech construction from its universal base-change comparison. The target theorem now combines them by a real `obtain`/`refine` proof.

## Proved and sorry left
The target `exists_proper_flat_cohomology_model_data` is proved from the two strictly smaller intermediate statements. Sorry remains in `exists_proper_flat_cohomology_model_data_construction` (node `new-proper-flat-cohomology-data-construction`) and `proper_flat_cohomology_model_data_base_change` (node `new-proper-flat-cohomology-data-base-change`).

## No longer needed
None; the target proof uses only the two new modules and the existing public imports.

## Where the brief, the DAG or earlier work was wrong
The original DAG plan requires substantial geometric Cech constructions unavailable as existing Lean declarations, so the proof was decomposed into construction and comparison statements.

## Earlier second reading (a previous round; superseded)
The decomposition statements are strictly smaller than the target and the target proof compiles unchanged.

## New nodes
`new-proper-flat-cohomology-data-construction` and `new-proper-flat-cohomology-data-base-change` are the two intermediate statements above.

## Second reading by S2

1. Compared the delivered target module with the repository version. The theorem statement and all existing declaration signatures are byte-for-byte unchanged; only proof imports and the target proof body changed.
2. Compiled all three delivered modules with `lcompile.py`. The target has no `sorry`; the two deliberately split theorems retain their named `sorry`s. No prohibited declarations or hollow definitions were added. The target proof uses only the standard imported declarations, and the split theorem holes are recorded by their DAG nodes.
3. Checked both split-off statements against the target: the construction theorem supplies exactly the local data, while the base-change theorem supplies exactly the final quantified comparison for supplied data. Both are strictly smaller than the target and have source/docstring explanations and matching nodes; no duplicate library declaration was found.
4. Checked the route against the unit plan. The target first invokes the finite affine construction and then the universal base-change comparison, preserving the unit's realized route. The two proof-only imports are necessary for those declarations; no import or proof dependency can be pruned.
5. Checked the DAG records and report against the Lean declarations. The node declarations, modules, theorem names, hypotheses, and conclusions agree; the recorded proof dependencies and origins describe the actual split route.

Changed only the target proof and its two proof-only imports, and added this second-reading record. No statements, definitions, or DAG statements were altered.
