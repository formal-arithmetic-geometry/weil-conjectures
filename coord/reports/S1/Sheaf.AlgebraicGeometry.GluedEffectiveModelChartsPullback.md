## What changed

Added the local theorem `glued_model_chart_pullback_single` as the explicit chart-square verification step, and used it pointwise to prove `glued_model_chart_pullbacks`.

## Proved and sorry left

`glued_model_chart_pullbacks` is proved. The new intermediate theorem `glued_model_chart_pullback_single` remains `sorry`; it is the local gluing argument for one fixed chart and has node `lem-pd-glued-effective-model-chart-pullback-single`.

## No longer needed

None. All original imports remain needed for the public statement; the proof-only import of the new local theorem is required.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan omitted an explicit local-to-global chart-square lemma. The decomposition makes that missing step a named node.

## New nodes

`lem-pd-glued-effective-model-chart-pullback-single` in `dag/nodes/sec-picard-framework/lem-pd-glued-effective-model-chart-pullback-single.json`.

## Earlier second reading (a previous round; superseded)

The pointwise theorem has the exact fixed-chart signature and is strictly one conclusion of the target family. The target proof applies it for each index; the unit route and public target statement are unchanged.

## Second reading by S1

1. Compared the delivered target module with the repository version. The public theorem signature is byte-for-byte unchanged; only its proof and the new proof-only import differ. The added single-chart module introduces the split-off declaration documented by its node.
2. Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry` is the named theorem `glued_model_chart_pullback_single`, and no forbidden declarations or hollow definitions were added.
3. Checked the split-off statement against the target: it fixes one index and concludes exactly one member of the target family, so it is strictly simpler and needed by the pointwise proof. Its docstring gives the source and intended gluing argument, and its DAG node matches the Lean declaration.
4. Reviewed proof dependencies and imports. The target retains its public imports; the new theorem is imported privately for proof use. No old dependency can be removed, and the unit route remains the chart-square verification route through the split node.
5. Verified the DAG target node and unit identifiers agree with the Lean declarations. No statement or definition was changed, and no existing downstream interface was adapted.

Changed only the report to record this second reading; no further code repair was necessary.
