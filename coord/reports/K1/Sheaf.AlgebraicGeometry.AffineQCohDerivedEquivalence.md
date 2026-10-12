## What changed

The target theorem now combines two strictly smaller intermediate theorems.  The core theorem
packages the derived equivalence, tilde comparison, derived global-sections quasi-inverse, and
triangulated structure.  The shift theorem packages preservation of shifts of the free rank-one
module.  The target proof is a complete conjunction of these two results.

## Proved and sorry left

`exists_affineQCohDerivedEquivalence` is proved from the two intermediate declarations.
`exists_affineQCohDerivedEquivalence_core` remains sorry (node
`new-affine-qcoh-derived-equivalence-core`), as does
`affineQCohDerivedEquivalence_shift` (node `new-affine-qcoh-derived-equivalence-shift`).

## No longer needed

No imports or stated dependencies were removed; all imports retained in the target are used by
its statement or by the intermediate declarations.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan requires substantial derived-category infrastructure not exposed by the current
library, so the plan cannot be translated into a direct proof in this stage.  The two new nodes
are the corresponding substantive subarguments rather than a restatement of the target.

## New nodes

`new-affine-qcoh-derived-equivalence-core` is stated in
`lean/Sheaf/AlgebraicGeometry/AffineQCohDerivedEquivalenceCore.lean`.
`new-affine-qcoh-derived-equivalence-shift` is stated in
`lean/Sheaf/AlgebraicGeometry/AffineQCohDerivedEquivalenceShift.lean`.

## Earlier second reading (a previous round; superseded)

A second worker should verify that the target conjunction is assembled without changing its
signature, and that each intermediate theorem is a strict substatement of the target.

## Second reading by K1

1. Compared the delivered target module with the repository version. The target declaration is byte-for-byte unchanged; only its proof and proof-only imports were added.
2. Compiled all three delivered modules with `lcompile.py --all`; they compile cleanly. The two substantive split-off theorems remain named `sorry`s, with no hollow definitions or forbidden declarations.
3. Reviewed the split-off statements and nodes. The original shift statement quantified over an arbitrary equivalence and was false; it now requires the termwise tilde comparison and triangulated structure supplied by the core theorem. The core statement remains a strict substatement of the target. The shift node metadata was updated to match.
4. The route still follows the unit: the target assembles the core derived equivalence and shift normalization. No imports or proof dependencies were pruned.
5. Checked the proof dependencies and declarations against the Lean source; the node statements and proof records describe the delivered declarations.

Changed the shift theorem and its node to avoid the false arbitrary-equivalence claim, and updated the target application and report accordingly.
