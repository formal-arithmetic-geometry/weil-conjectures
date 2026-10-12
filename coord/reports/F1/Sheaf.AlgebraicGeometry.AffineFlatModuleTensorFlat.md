## What changed

Added the stalk-flatness intermediate theorem module and proved the target theorem by reducing tensor exactness to flat stalks, using the stalk tensor comparison and stalk exactness criterion. The intermediate theorem remains `sorry` as a strictly smaller affine-local calculation.

## Proved and sorry left

Proved `AlgebraicGeometry.isFlat_of_affineFlatOver_identity`.
Left `AlgebraicGeometry.flat_stalk_of_affineFlatOver_identity` as the single split intermediate theorem, node `lem-pc-affine-flat-module-stalk-flat`.

## No longer needed

The filtered-colimit and localization nodes are used only by the split stalk theorem, so neither is pruned from the argument. Removed the redundant proof import `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` (already imported by `MonoidalFree`) and the unnecessary local closed-category instance. No node or module was pruned from the closure.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omitted the necessary explicit stalk-flatness intermediate declaration; it is now split out with its own node.

## New nodes

`lem-pc-affine-flat-module-stalk-flat`: affine-local flat sections imply flatness of each stalk; declared in `Sheaf.AlgebraicGeometry.AffineFlatModuleStalkFlat`.

## Second reading by F1

1. I compared `AffineFlatModuleTensorFlat.lean` with the repository version. The existing theorem signature and its documentation are unchanged; only proof imports, a private helper, and the proof body were added. The new stalk module is an independently declared intermediate result.

2. Both delivered modules compile with `lcompile.py --all`. The only remaining `sorry` is the named theorem `AlgebraicGeometry.flat_stalk_of_affineFlatOver_identity`, which is listed in the report and has the node `lem-pc-affine-flat-module-stalk-flat`. No definitions contain `sorry`, and no forbidden declarations were added.

3. The split-off stalk statement is a genuine affine-local reduction, strictly smaller than tensor flatness. Its documentation gives the filtered-colimit and localization argument, and its DAG node records the source, dependencies, proof route, and Lean declaration. I found no existing library theorem with this statement.

4. The target proof follows the unit route: affine-local stalk flatness, stalk tensor comparison, and stalk exactness. The helper closes the sheaf-level reduction directly; the imports removed by the worker are recorded above, and no additional pruning was found.

5. The target node's `proof`, `proof_deps`, and `proof_origin` match the proof. The new stalk node has matching statement, declaration, source, and dependencies. The unit remains `sk-thm-picard-coherence`.

I changed only this report section during second reading; no Lean proof or statement required repair.
