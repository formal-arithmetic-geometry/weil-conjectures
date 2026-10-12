## What changed

Split the theorem into quasi-coherence and local lower-bound components in two new
modules, and proved the original theorem by pairing those component theorems. The
component theorems remain `sorry` for parallel proof.

## Proved and sorry left

The original declaration `AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part`
is proved by combining the two component declarations. The new declarations
`AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part_qc` and
`AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part_bound` remain `sorry`.

## No longer needed

No imports or DAG dependencies were pruned; all original proof dependencies remain
available for the component proofs.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically appropriate but too large for this item;
it was split at its two independent conclusions.

## New nodes

`new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc` and
`new-lem-sc-rhom-supported-qcoherent-pseudo-part-bound` record the two component
statements and their source in Tag 0A6H.

## Earlier second reading (a previous round; superseded)

A second worker should verify that the two component signatures are strict parts of
the original conjunction and that pairing them reproduces the unchanged target.

## Second reading by A2

1. Compared the delivered target module with the repository version. The theorem signature is unchanged byte for byte; only its proof and the two component imports differ. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`; they compile without errors. The original theorem has no `sorry`; the two component theorems retain the named `sorry`s recorded in their nodes. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Checked both split statements against the original conjunction. Each is a strict conjunct, has the same hypotheses, and is needed exactly once to reconstruct the target. Searched the repository for duplicate declarations and checked the recorded Mathlib searches. Verdict: pass.
4. The target proof pairs the two component results directly. Removed the three old proof-only imports (`DerivedInternalHomRestrictOpen`, `AffinePseudoCoherentRHomQuasiCoherent`, and `AffineQCohDerivedEquivalence`) because the split proof does not use them; the component modules remain the only proof imports. Verdict: pass.
5. Checked the original and new DAG nodes and the unit record. The original node's proof and dependencies match the pairing proof, and both new nodes record the corresponding strict component statements. The unit route is preserved through the two components. Verdict: pass.

Changed the main module to prune unused proof-only imports and added this second-reading report. No theorem statements or definitions were changed.
