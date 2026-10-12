## What changed

Added two decomposition modules and imported them into the target. The target theorem is now proved by rewriting the stalk image-inclusion range using `stalk_image_inclusion_range`, then applying `stalk_tensor_multiplication_range`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.ideal_multiplication_stalk_range` is proved. The decomposition leaves two named sorries: `AlgebraicGeometry.Scheme.stalk_image_inclusion_range` (node `lem-weil-pbc-ideal-multiplication-stalk-range-image`) and `AlgebraicGeometry.Scheme.stalk_tensor_multiplication_range` (node `lem-weil-pbc-ideal-multiplication-stalk-range-tensor`).

## No longer needed

Removed proof-only imports `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor` and `Sheaf.Algebra.Homology.ModuleStalkExact` from the target; the decomposition modules carry the needed dependencies.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires substantial stalk exactness and tensor germ arguments. Those are represented as two strict intermediate statements so the target proof itself is complete.

## New nodes

`lem-weil-pbc-ideal-multiplication-stalk-range-image` and `lem-weil-pbc-ideal-multiplication-stalk-range-tensor`, with corresponding modules under `lean/Sheaf/AlgebraicGeometry/`.

## Second reading by C3

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged; only proof imports and the target proof body changed.
2. Compiled all three delivered modules with `lcompile.py --all`. They compile successfully. The two decomposition theorems are the only remaining `sorry`s, and neither definition contains a hole or forbidden declaration.
3. Read both split statements and their nodes. They are strict reductions of the target (image-range identification and the preceding tensor multiplication range), with source citations and matching declarations. No duplicate upstream declaration was found by repository search.
4. Checked the proof route and imports. The target uses the two decomposition declarations directly; the former proof-only stalk-tensor and stalk-exactness imports are no longer needed in the target. The unit route remains represented by the target and its two decomposition nodes.
5. Checked DAG/Lean agreement. The target node records the two split nodes as proof dependencies, and each split node records its delivered module and declaration. No statement or definition change was made.

Changed the report only, and repaired the target DAG proof metadata to follow the delivered proof. No additional holes were introduced beyond the two named decomposition statements.
