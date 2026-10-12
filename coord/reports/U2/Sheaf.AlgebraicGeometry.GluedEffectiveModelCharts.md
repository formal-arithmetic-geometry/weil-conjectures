## What changed

Proved `exists_glued_effective_model_charts` by decomposing the construction into two named intermediate theorems. Added proof-only imports for the intermediate modules.

## Proved and sorry left

The target theorem is proved by applying `exists_glued_model_data` and `glued_model_chart_pullbacks`. The two intermediate theorems retain `sorry` proofs and are recorded as new nodes.

## No longer needed

No imports or existing nodes were pruned; all original hypotheses are passed to the intermediate construction.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires substantial scheme gluing and pullback verification, so these were split into two strictly smaller intermediate statements.

## New nodes

`lem-pd-glued-effective-model-charts-aux` and `lem-pd-glued-effective-model-charts-pullback` are the two intermediate statements used by the target proof.

## Earlier second reading (a previous round; superseded)

The decomposition was checked against the target signature. The target applies the two intermediate statements without changing hypotheses or conclusion; both new statements are strictly smaller construction steps.

## Second reading by U2

1. Compared the delivered target module against the repository version. The target declaration signature is unchanged; the proof-only imports and proof body are the only target-module changes.
2. Compiled all three modules with `lcompile.py --all`; compilation succeeds with no errors. The two intermediate declarations remain the only named `sorry`s, with no sorry in definitions or forbidden declarations.
3. Checked the split statements. The original pullback split was under-specified because arbitrary `q₀` and `j` do not determine the required square. Added the necessary compatibility equation `q i ≫ j i = (U i).ι ≫ q₀` to both split statements and the target proof. This makes each split a strictly smaller, true construction/verification step.
4. The auxiliary and pullback imports are proof-only and minimal for the current proofs; no existing imports or nodes became unnecessary. The unit route remains the gluing construction followed by chart pullback verification.
5. Updated both DAG node Lean statements to match the repaired declarations. No target statement or definition changed.

Changed: repaired the auxiliary output and pullback input with the missing commutativity hypothesis, updated the target application, synchronized DAG node statements, and documented the review.
