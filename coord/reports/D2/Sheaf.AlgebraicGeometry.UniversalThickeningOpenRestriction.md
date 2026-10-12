## What changed

Added two proof-only imports and reduced `universalFirstOrderThickening_open_restriction` to a real Lean composition of the open-restriction data theorem and the conormal comparison theorem. Added the two corresponding intermediate modules and DAG nodes; both intermediate proofs remain named `sorry`s.

## Proved and sorry left

The target declaration `universalFirstOrderThickening_open_restriction` is proved by applying the two strictly smaller intermediate results. The new declarations `universalFirstOrderThickening_open_restriction_core` and `universalFirstOrderThickening_open_restriction_conormal` remain `sorry`, with nodes `lem-weil-pbc-universal-thickening-open-restriction-core` and `lem-weil-pbc-universal-thickening-open-restriction-conormal`.

## No longer needed

Removed the proof-only imports `Sheaf.AlgebraicGeometry.TensorPullback`,
`Sheaf.AlgebraicGeometry.Thickening`, and
`Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists` from the target module.
The original lower-level route is encapsulated by the two intermediate statements.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan is mathematically appropriate but too large for a single stage-3 proof. It was decomposed into the restriction-data and conormal-comparison subclaims, each a strict part of the plan.

## New nodes

`lem-weil-pbc-universal-thickening-open-restriction-core` records the open restriction maps, compatibility equations, and universal property. `lem-weil-pbc-universal-thickening-open-restriction-conormal` records formal unramifiedness of the restricted map and the conormal module isomorphism.

## Second reading by D2

1. The target declaration and its signature are byte-for-byte unchanged from the repository. The two added declarations are strict subclaims: the core omits formal unramifiedness and conormal data, while the conormal claim assumes the already-constructed restriction data. No definition or target statement changed.
2. All three modules compile with `lcompile.py --all`. The target proof contains no `sorry`; the only remaining holes are the two named intermediate theorems, each with a docstring and matching DAG node. No axioms, unsafe declarations, or hollow definitions were added.
3. The two split statements are true, strictly simpler than the target, and sourced from Stacks 04FA/04F3 and Definition 01R2. Their DAG dependencies no longer point back to the target, avoiding a circular proof graph; Mathlib searches found no existing declarations.
4. The target composes the core and conormal statements directly. The unit route remains the same (`sk-thm-p1`); the unused proof-only imports `TensorPullback`, `Thickening`, and `UniversalFirstOrderThickeningExists` were removed from the target module.
5. The target node's proof and proof dependencies now match the Lean composition, and each new node records its declaration, source, proof route, and dependencies.

Changed the target imports and proof, corrected the new-node dependency metadata, and added this second-reading review.
