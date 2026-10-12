## What changed

Proved `closedImmersion_algebraDirectImage_preservesFiniteColimits` by applying the general categorical theorem that a functor preserving homology preserves finite colimits. Added the strictly smaller intermediate homology statement in `Sheaf.AlgebraicGeometry.ClosedImmersionAlgebraDirectImagePreservesEpimorphisms`, left sorry for its stalkwise exactness proof.

## Proved and sorry left

Closed the target theorem `AlgebraicGeometry.closedImmersion_algebraDirectImage_preservesFiniteColimits`.
Added the sorry theorem `AlgebraicGeometry.closedImmersion_algebraDirectImage_preservesHomology` (node `lem-sc-closed-immersion-algebra-direct-image-preserves-homology`). No other intermediate theorem is added.

## No longer needed

No imports or proof-dependency nodes were removed. The new homology module is needed by the target proof.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the categorical homology-to-finite-colimits glue needed to make the stalkwise argument usable in Lean; this delivery records that glue as a separate intermediate node.

## New nodes

`lem-sc-closed-immersion-algebra-direct-image-preserves-homology`: homology preservation for the closed-immersion module direct image, sourced to Stacks Tags 00AE and 01AX. Its module is `lean/Sheaf/AlgebraicGeometry/ClosedImmersionAlgebraDirectImagePreservesEpimorphisms.lean`.

## Second reading by J1

1. I compared the delivered target module with the repository version. The target theorem's signature is byte-for-byte unchanged; the only change is its proof and the proof-only import of the new homology module. The intermediate module is new and introduces only the explicitly reported split theorem.

2. Both delivered Lean files compile with `lcompile.py`. There are no axioms, unsafe declarations, hollow definitions, or unnamed `sorry`s. The sole remaining `sorry` is the named homology theorem, which has a source, a proof docstring, and a matching DAG node. The target proof uses only the permitted categorical theorem and that intermediate instance.

3. The split-off homology statement is strictly weaker than finite-colimit preservation and is required by the target proof. Its stalkwise exactness claim is the closed-immersion result from Stacks Tags 00AE and 01AX, and it is not duplicated elsewhere in the project or Mathlib.

4. The proof follows the shortest available route in the current library: establish `PreservesHomology`, then apply `Functor.preservesFiniteColimits_of_preservesHomology`. No unused imports were found, and no old proof dependency can be pruned without removing the declarations used by the target module.

5. The target node and the new homology node agree with the Lean declarations, including their proof dependencies and origins. The unit route is preserved: the target still realizes finite-colimit preservation through the homology step, while the stalkwise argument remains the split node.

I changed only the instance binder from `haveI` to `letI` to remove a style warning, corrected the stale pruning note, and added this second-reading record.

## Earlier second reading (a previous round; superseded)

The target statement is unchanged and the homology intermediate is strictly weaker and sufficient. The proof keeps the closed-immersion exactness route.
