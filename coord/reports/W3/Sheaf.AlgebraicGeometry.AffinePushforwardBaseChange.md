## What changed
Added the intermediate affine base change isomorphism theorem and used it to close `affinePushforward_baseChange`; restored the affine tensor comparison proof route.

## Proved and sorry left
`affinePushforward_baseChange` is proved by quasi-coherence plus `affinePushforward_baseChange_isIso`. Remaining sorry: `affinePushforward_baseChange_isIso` and `affinePushforward_baseChange_affine_formula`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The tensor comparison module was absent from the branch and had to be supplied in the sandbox.

## New nodes
`lem-weil-pbc-affine-pushforward-base-change-isIso`.

## Second reading by W3

1. Compared the delivered main module with the repository version. Existing theorem signatures are unchanged; the only proof change closes `affinePushforward_baseChange` and adds the proof-only import of the existing affine pushforward quasi-coherence theorem.
2. Compiled all sandbox modules. The main theorem now compiles; the two explicitly split affine computation statements remain the only `sorry`s, and the new `affinePushforward_baseChange_isIso` theorem is the named split node. No forbidden declarations or hollow definitions were introduced.
3. Checked the split statement and node against the affine base-change claim. `affinePushforward_baseChange_isIso` has exactly the needed hypotheses and conclusion and is strictly simpler than the target; its source and proof description are recorded in the node. The tensor-comparison module is unchanged from the repository and no duplicate statement was added.
4. The route remains the unit route: quasi-coherence is discharged by the existing affine pushforward theorem, while invertibility is delegated to the split affine computation node. No imports were removed; the added import is proof-only.
5. DAG and Lean agree: the new module and declaration match `lem-weil-pbc-affine-pushforward-base-change-isIso`, and the target node records the same target signatures and dependencies.

Changed the quasi-coherence proof to use `isQuasicoherent_pushforward_of_isAffineHom` from the source library's affine-morphism module, added its plain proof import, and appended this review. No target statements or definitions changed.
