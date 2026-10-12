## What changed

Replaced the proof of `isGeometricallyRegular_genericFormalFiber_of_regular_powerSeries` with a real combination of two strictly smaller intermediate obligations. Added proof-only imports for the Noetherianity and finite-purely-inseparable-regularity components. The target unfolds `Algebra.IsGeometricallyRegular`, obtains the two components, and pairs them.

## Proved and sorry left

Closed the original target hole in `isGeometricallyRegular_genericFormalFiber_of_regular_powerSeries`. Added two named intermediate holes: `isNoetherian_genericFormalFiber_of_regular_powerSeries` and `isRegular_genericFormalFiber_after_finite_purelyInseparable`, each in its own module and each a strict clause of the target definition.

## No longer needed

No imports or DAG nodes were pruned. The existing dependencies remain part of the stated proof route; the target now uses the two new component nodes directly.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combines Noetherianity, regularity, and characteristic arguments in one large obligation. The Lean definition of geometric regularity separates the first two into independent conjunct and universal clauses, so these are valid strict decomposition points. No target signature or existing declaration was changed.

## New nodes

`new-lem-weil-pbc-generic-formal-fibre-noetherian` in `Sheaf.RingTheory.GenericFormalFiberNoetherian`.

`new-lem-weil-pbc-generic-formal-fibre-purely-inseparable-regular` in `Sheaf.RingTheory.GenericFormalFiberPurelyInseparableRegular`.

## Earlier second reading (a previous round; superseded)

The component split and target combination were checked by compiling all three modules with the prescribed compiler.

## Second reading by N1

1. **Statements unchanged.** I compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; the proof only unfolds `Algebra.IsGeometricallyRegular` and applies the two component declarations.

2. **Proof and axioms.** All three delivered modules compile with the prescribed `lcompile.py` command. The two component declarations remain explicitly named `sorry` obligations with source and blueprint docstrings; the target itself has no `sorry`. No prohibited declarations or hollow definitions were introduced.

3. **Split statements.** The two new declarations are strict clauses of the target definition: one supplies `IsNoetherianRing` and the other supplies regularity after every finite purely inseparable field extension. Their hypotheses and fibre construction match the target exactly, so the decomposition is true and sufficient. Library and Mathlib searches found no existing declaration of either result.

4. **Pruning and route.** The target proof keeps the unit route by combining the two component nodes. The parent module's four old proof-only imports were unused after the split and have been removed; the target node's `proof_deps` now lists exactly the two component nodes. The public imports needed by the theorem signatures remain.

5. **DAG agreement.** The target node proof text, dependencies, and Lean proof now agree. Both new node files, declarations, source references, and `sorry` obligations are present and compile. The unit `sk-thm-p1` remains unchanged.

I changed the parent imports, updated the target node's `proof_deps`, and added this second-reading record. No theorem signatures or definitions were changed.
