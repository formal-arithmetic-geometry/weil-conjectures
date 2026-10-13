## What changed

Reconciled the sandbox with the already landed upstream-review #1428 duplicate
repair, landing 20261013T222412-L-1226410, documented in
coord/changes/equivariantModulePresheafSheaf-duplicate.md.
The delivered module is the current declaration-free compatibility module;
its module documentation now explicitly identifies the retained scalar-restricted
AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf theorem
exposed by its public import of
Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf.

Removed all obsolete caller adaptations, node copies and the unlanded change
record from the delivery set. They are archived under scratchpad/superseded-attempt
for local history only. No existing declaration, signature, import or node changes.
No new interface change requires a change record.

Validation: compiled the current retained theorem, the delivered compatibility
module, TorsorAssociatedModuleFull, TorsorInvariantSections and
TorsorSectionEvaluationBijective together in import order with lcompile.py,
using fresh scratchpad outputs. All five compiled without warnings.
An explicit #print axioms check of the retained theorem reports only propext,
Classical.choice and Quot.sound.

## Proved and sorry left

Holes closed: none (0 of 0). Holes added: none. Split-off statements: none.
The assigned module has no declarations and no sorry. The duplicate removal was
already completed by the landed companion repair, not by this delivery.
The retained theorem is
AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf
in Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf, recorded by
lem-weil-pbc-torsor-equivariant-presheaf-sheaf and
lem-weil-pbc-torsor-equivariant-module-is-sheaf.

## No longer needed

No imports, nodes or modules newly pruned in this delivery.
The obsolete sandbox caller adaptations in TorsorInvariantSections and
TorsorSectionEvaluationBijective, their node edits, and
coord/changes/torsor-equivariant-sheaf-duplicate.md are not delivered.
The compatibility import remains necessary for the existing callers.
The landed duplicate repair already removed the second gluing implementation;
this delivery does not count that earlier pruning again.

## Where the brief, the DAG or earlier work was wrong

The repair queue still lists this module, although the companion R4 repair has
already consolidated both implementations. The earlier sandbox incorrectly
assumed that the retained theorem still had its coefficient-valued signature.
It now proves the scalar-restricted statement with explicit P, which the current
unchanged callers use directly. Adding scalar composition to those callers is
unnecessary and would not qualify as a forced adaptation.

The current DAG already points both sheaf nodes to the single retained declaration.
The unit route and all target statements remain unchanged. This delivery therefore
records the completed repair and corrects the stale sandbox instead of introducing
another theorem, decomposition or interface change.

## Second reading by R4

1. **Repository comparison:** Compared the delivered compatibility module with the repository version. The only change is module documentation; declarations, imports, visibility, and signatures are byte-for-byte unchanged.

2. **Compilation and axioms:** Compiled the module with `lcompile.py` successfully and checked the retained theorem `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`; its axioms are restricted to `propext`, `Classical.choice`, and `Quot.sound`. The compatibility module contains no declarations, `sorry`, forbidden commands, or hollow definitions.

3. **Statements and split-offs:** No statements were split off or added in this delivery. The existing node and theorem remain unchanged and the theorem is not duplicated in this module.

4. **Pruning and imports:** The single public import remains necessary because it exposes the retained theorem to existing callers. No obsolete proof dependency is introduced or removed here; the earlier duplicate repair is already represented in the landed module and DAG.

5. **DAG and unit route:** The DAG node points to the retained theorem in `TorsorEquivariantModuleIsSheaf`, and the unit route is unchanged. The compatibility module preserves that route by re-exporting the implementation.

Changed only the explanatory module documentation to describe the retained scalar-restricted theorem and its purpose as a compatibility import.
