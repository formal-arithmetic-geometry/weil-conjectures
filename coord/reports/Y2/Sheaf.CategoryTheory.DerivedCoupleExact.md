## What changed
`derived_couple_exact` is now proved from three strictly smaller intermediate statements and the existing exact-couple API. The `pageCouple_image` theorem remains open. Added proof-only imports for the three intermediate modules.

## Proved and sorry left
Proved: `CategoryTheory.BigradedExactCouple.derived_couple_exact`.
Sorry left: `CategoryTheory.BigradedExactCouple.pageCouple_image`; added `derived_couple_kernel_identities`, `derived_couple_map_uniqueness`, and `derived_couple_boundary_vanishes`.

## No longer needed
Removed the unused `PageCoupleImageCore` import and its attempted intermediate module.

## Where the brief, the DAG or earlier work was wrong
The element chases for the kernel/image identities, map uniqueness, and boundary vanishing are absent from the existing API, so they were split into strict intermediate statements.


## New nodes
`lem-sp-derived-couple-boundary-vanishes`, `lem-sp-derived-couple-kernel-identities`, and `lem-sp-derived-couple-map-uniqueness` record the three strict intermediate statements, each sourced to Stacks Tag 011R and used by the proved theorem.

## Second reading by Y2

1. Compared the delivered parent module with the repository version. The existing declaration signatures and definitions are unchanged; only proof-only imports and the proof body changed. Verdict: pass.

2. Compiled all delivered modules with `lcompile.py --all`; all four modules compile cleanly. The parent target has no remaining `sorry`; the only sorries are the named split-off theorems, with no forbidden declarations or hollow definitions. Verdict: pass.

3. Reviewed the three split-off statements and their docstrings. Each isolates a strictly smaller ingredient (kernel/image identities, uniqueness of induced maps, or boundary vanishing), is mathematically true under the exact-couple hypotheses, and is not a restatement of the parent target. Verdict: pass.

4. Checked the proof route and imports. The parent proof uses each split-off result and the existing differential square-zero theorem; removed `PageCoupleImageCore` is no longer needed. The unit route remains intact. Verdict: pass.

5. Checked the DAG records against the Lean declarations and proof dependencies. The three new nodes and the updated parent proof metadata are present; no statement was weakened or altered. Verdict: pass.

Changes made: added this second-reading section only; no Lean statements, definitions, or proofs were altered during review.
