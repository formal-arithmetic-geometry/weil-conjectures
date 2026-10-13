## What changed
Replaced the rejected restatement core with two strict intermediate theorems. The target module now applies the target-stalk estimate and the finite-normalization transfer theorem. Added imports for the two new modules.

## Proved and sorry left
- `stalk_normalization_boundary_dimension_two` is proved by composing the two intermediate theorems.
- `stalk_normalization_boundary_dimension_two_target` remains sorry; node `new-stalk-normalization-boundary-dimension-two-target`.
- `stalk_normalization_boundary_dimension_two_transfer` remains sorry; node `new-stalk-normalization-boundary-dimension-two-transfer`.

## No longer needed
The previous same-statement core reduction is removed. No proof dependency imports were retained solely for that restatement.

## Where the brief, the DAG or earlier work was wrong
The earlier core theorem had the identical statement and was correctly rejected as a restatement. The argument is now split into a smooth-pullback target dimension estimate and a finite integral going-down transfer, each strictly simpler than the target.

## New nodes
`new-stalk-normalization-boundary-dimension-two-target` records the smooth-pullback boundary estimate. `new-stalk-normalization-boundary-dimension-two-transfer` records the finite-normalization going-down transfer.

## Earlier second reading (a previous round; superseded)
Pending independent second reading; the target composition compiles and both new statements are strict decompositions of the original proof steps.

## Second reading by E4
1. Compared the target module with the repository version. The theorem signature is unchanged byte for byte; only the proof and proof-only imports changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; they compile without errors. The only remaining `sorry`s are the two named split-off theorems below, and there are no hollow definitions or forbidden declarations. Verdict: pass.
3. Checked the two split-off statements against the target and their source descriptions. The smooth-pullback estimate and the finite-normalization transfer are true strict reductions, with docstrings and matching DAG nodes; neither duplicates an existing library declaration. Verdict: pass.
4. The target now follows the shortest available decomposition: target stalk estimate followed by finite transfer. The direct imports needed by the target signature remain public, while the two proof modules are private imports. Verdict: pass.
5. Checked node statements, proof dependencies, proof origins, and the unit route. The target node records the composed route; both new nodes record the corresponding proof steps. Verdict: pass.

Changed: added this second-reading record and the new-node descriptions required by the delivery contract. No Lean statements or definitions were changed.

## New nodes
`new-stalk-normalization-boundary-dimension-two-target` states the smooth-pullback boundary dimension estimate and is declared in `StalkNormalizationBoundaryDimensionTwoCore.lean`.
`new-stalk-normalization-boundary-dimension-two-transfer` states the finite-normalization transfer and is declared in `StalkNormalizationBoundaryDimensionTwoTransfer.lean`.
