## What changed

Added `Sheaf.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct`, whose single theorem states the internal-Hom coproduct-to-product universal property and remains a documented `sorry`. Proved `CategoryTheory.homTensorSummandRestriction_ext` by constructing the total-degree coproduct cofan, proving its colimit property with the total-complex universal property, and applying the internal-Hom fan limit extensionality. Added DAG node `lem-sc-internal-hom-coproduct-fan`.

## Proved and sorry left

Closed `CategoryTheory.homTensorSummandRestriction_ext`. The new theorem `SheafOfModules.internalHomCoproductFanIsLimit` remains `sorry`; it is the strict tensor-Hom/coproduct universal-property subproblem represented by the new node.

## No longer needed

None. Both original imports are retained; the new proof imports the internal-Hom coproduct lemma.

## Where the brief, the DAG or earlier work was wrong

The earlier blocked attempt treated the mixed-universe tensor-Hom construction as unavailable. The existing `KFlat` module supplies the mixed-universe sectionwise construction, so the remaining argument can be isolated as the internal-Hom coproduct fan theorem.

## New nodes

`lem-sc-internal-hom-coproduct-fan`, stated by `SheafOfModules.internalHomCoproductFanIsLimit` in `Sheaf.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct`.

## Second reading by A2

1. **Statements unchanged.** Compared the delivered module with the repository version. The existing theorem signature is byte-for-byte unchanged; the added internal-Hom theorem is a separate documented split-off statement.
2. **Proof validity.** Compiled both delivered modules with `lcompile.py --all`. The target theorem has no `sorry`; the only remaining `sorry` is `SheafOfModules.internalHomCoproductFanIsLimit`, named in the report and represented by `lem-sc-internal-hom-coproduct-fan`. No forbidden declarations or hollow definitions occur.
3. **New statement.** Checked that the split-off theorem states exactly the needed internal-Hom coproduct-to-product universal property, with no extra hypotheses or weakened conclusion; its source, proof sketch, and DAG node agree.
4. **Pruning and route.** The proof constructs the total-degree cofan, proves its colimit property from the existing complex universal property, then applies the split-off fan limit. The proof-only import of `InternalHomCoproduct` is required; no imports or proof dependencies were removable.
5. **DAG and unit.** Updated the existing node's proof, proof dependencies, and origin to match the implemented route, and verified the unit route remains through the total tensor summand restriction node.

Changed the existing DAG node metadata as above and added this second-reading record; no Lean statements or definitions were altered.
