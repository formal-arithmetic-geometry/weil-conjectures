## What changed

Restored Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison from its exact
quarantine path in coord/rework.tsv. Replaced the public import of the withdrawn
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations with the adopted
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations provider.
This is the only source change from the archive. The theorem signature, complete
proof, signed conclusion, docstrings, options, and other imports are unchanged.
Change record: coord/changes/G1-scalar-external-cup-upstream-provider.md.

The original archive was compiled to reproduce the assigned error. The repaired
module compiles against a fresh compile of the current, unchanged cup-compatibility
source. A scratch public consumer imports only this module, restates the entire
theorem signature, and applies the theorem. Delivery preflight supplies the final
compilation and axiom probes. No scratch consumer is delivered.

## Proved and sorry left

This is an assigned restoration repair with zero original local holes, zero holes
closed, zero holes added, and zero local holes left. The existing complete proof of
AlgebraicGeometry.Scheme.Modules.scalarExternalCup_moduleComparison is preserved
(lem-sc-scalar-external-cup-module-comparison). Nothing is split off. No other
Lean declaration is changed or added. Its proof still uses the existing
scalarCup_moduleCup_compatibility and scalar_moduleCohomologyPullback_comparison
lemmas; no claim is made to close their transitive proof obligations.

## No longer needed

The public import of the empty retired module
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations is replaced by its
adopted upstream provider. No mathematical dependency, theorem, or DAG node is
pruned. Both declared proof dependencies remain needed, and their imports stay.
The node's proof, proof_deps, proof_origin, lean attachment, and unit route remain
accurate without changes. The quarantined PicardScalarCechExternalCup parent still
cites and applies this theorem, so absence of current live importers is not grounds
for withdrawal.

## Where the brief, the DAG or earlier work was wrong

The archived import still named a retired public provider following the upstream
sync. This repair restores the intended visibility, without changing mathematics.

A first compile after replacing the provider encountered an absent generated
instance in the published compiled scalarCup_moduleCup_compatibility theorem:
FieldLinearModuleCohomologyOperations_monoidalCategory3. A scratch inspection of
that theorem found the absent reference. Compiling its current source, already
restored by K2, and then this module succeeds; no dependency source repair is
needed. The unchanged current dependency source may be included for compilation
only and contributes no source diff to the delivery.

LeanFinder returned no matching project comparison, Loogle returned no externalCup
match, and the Mathlib grep returned no corresponding theorem. Reading the current
project declarations confirms the existing short route: unfold externalCup, use
the signed cup comparison, and substitute the two module pullback comparisons.
The DAG already records exactly that route. No new statement or node is needed.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
