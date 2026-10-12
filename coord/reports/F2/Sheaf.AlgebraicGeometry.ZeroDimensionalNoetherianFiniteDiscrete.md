## What changed

Replaced the sorry proof with a proof using the existing zero-dimensional closed-subset theorem. The proof constructs the Noetherian and T0 instances, applies the theorem to the universal closed subset, transfers finiteness to the scheme type, and obtains discreteness from finite T1 topology.

## Proved and sorry left

Proved `AlgebraicGeometry.finite_and_discreteTopology_of_topologicalKrullDim_le_zero`. No sorries remain.

## No longer needed

None; the existing imports are used by the statement or proof.

## Where the brief, the DAG or earlier work was wrong

None.

## New nodes

None.

## Second reading by F2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof body differs.
2. Compiled the module with `lcompile.py` and checked `#print axioms`; it compiles and uses only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry`, `axiom`, `unsafe`, or hollow definition.
3. The proof uses the existing `IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero` declaration and introduces no split-off statements. The theorem remains exactly the node statement, including the empty scheme case.
4. Pruning review found a shorter direct route through the universal closed subset. The spectral-space dependencies from the old planned proof are unnecessary; the unit route is still represented by the same target node and its closed-subset step.
5. Updated the target node's `proof`, `proof_deps`, and `proof_origin` to match the proof. No statements or definitions changed.

Changed: recorded the direct proof route in the DAG and documented the second reading. No holes remain and no new holes were added.

The linter configuration change is recorded in `coord/changes/zero-dim-finite-discrete-linter.md`.
