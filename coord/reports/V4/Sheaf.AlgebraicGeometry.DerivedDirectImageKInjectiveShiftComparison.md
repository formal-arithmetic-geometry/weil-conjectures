## What changed

Added `Sheaf.AlgebraicGeometry.DerivedDirectImageKInjectiveShiftComparisonAux` containing the strictly lower auxiliary component identity, and imported it from the target module. The target theorem is proved by composing that identity with the localized shift isomorphism and simplifying its inverse/hom pair.

## Proved and sorry left

The target declaration `derivedModuleDirectImageKInjectiveIso_shift` is proved. The new declaration `derivedModuleDirectImageKInjectiveIso_shift_aux` remains a named sorry, with node `lem-pc-direct-image-kinjective-comparison-shift-aux`; it is the naturality component used by the target proof.

## No longer needed

No imports or existing DAG nodes were pruned. The existing private helper remains available for the original module context; the proof itself uses the auxiliary component identity directly.

## Where the brief, the DAG or earlier work was wrong

The original node proof plan omitted the component identity as a separately reusable intermediate theorem; the delivery records it as a strict lower node.

## New nodes

`lem-pc-direct-image-kinjective-comparison-shift-aux`: `dag/nodes/sec-picard-framework/lem-pc-direct-image-kinjective-comparison-shift-aux.json`.

## Earlier second reading (a previous round; superseded)

The target proof was compiled together with the auxiliary module; a second reading is requested for the new intermediate theorem and its source fidelity.

The interface change is recorded in `coord/changes/derived-direct-image-shift-aux.md`.

## Second reading by V4

1. I compared the delivered target module with the repository version. The target
   theorem statement is byte-for-byte unchanged; the only implementation change is
   its proof and the proof-only import of the auxiliary module. The auxiliary module
   is a new split-off declaration and is recorded by its DAG node and change record.

2. Both delivered Lean files compile independently and together with
   `lcompile.py --all`. The target theorem has no new axioms beyond the documented
   `sorryAx` inherited from the auxiliary theorem; there are no `axiom`, `unsafe`,
   `opaque`, `extern`, or hollow definitions. The sole remaining sorry is
   `derivedModuleDirectImageKInjectiveIso_shift_aux`.

3. The auxiliary statement is a strict component identity: it removes the final
   localized-shift hom from the target equation and is exactly the intermediate
   equality used by the target proof. It is sourced to Stacks Tag 079V, has a
   documented proof plan, and is not duplicated elsewhere in the library.

4. The target proof follows the shortest available route in this delivery: rewrite
   by the auxiliary identity, reassociate, and simplify the inverse/hom pair. The
   auxiliary theorem remains the required lower split-off hole. No imports or old
   proof dependencies became unused; the target DAG node was updated to record the
   auxiliary dependency and the actual proof route.

5. The unit route is preserved: the target still uses the K-injective comparison
   and localized shift identification, with the auxiliary node realizing the
   component step. The unit and chapter records are unchanged.

I changed the target DAG proof metadata to reference the auxiliary node and changed
the report only; no public declaration signatures or definitions were altered.
