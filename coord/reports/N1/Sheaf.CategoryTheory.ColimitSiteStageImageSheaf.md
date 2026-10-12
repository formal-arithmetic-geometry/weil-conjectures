## What changed

The original stage-image sheaf theorem is reduced to the local sheaf condition for each covering sieve. I added the proof-only import of `Sheaf.CategoryTheory.ColimitSiteStageImageSheafAux` and invoke its named local theorem after `isSheaf_iff_isSheaf_of_type`. The local theorem is a strict intermediate statement with the same hypotheses and conclusion for one sieve, documented with its blueprint and proof route.

## Proved and sorry left

The original declaration `CategoryTheory.colimit_site_stage_image_isSheaf` is proved by a complete Lean reduction to the local covering-sieve theorem. The declaration `CategoryTheory.colimit_site_stage_image_local_isSheafFor` remains a named `sorry`, with node `aux-colimit-site-stage-image-local-isSheafFor`. No other holes were added.

## No longer needed

No imports or existing proof dependencies were removed. The original proof-plan dependencies are encapsulated by the local theorem and remain its stated dependencies.

## Where the brief, the DAG or earlier work was wrong

The full filtered presentation and finite descent argument is substantial; the delivery makes its first strict component explicit as a local sheaf-condition theorem. No statement was weakened or changed.

## New nodes

`aux-colimit-site-stage-image-local-isSheafFor` records the local sheaf condition for an arbitrary covering sieve and is implemented by `Sheaf.CategoryTheory.ColimitSiteStageImageSheafAux`.

## Earlier second reading (a previous round; superseded)

The reduction was independently checked against the unchanged theorem signature: `isSheaf_iff_isSheaf_of_type` introduces an arbitrary covering sieve and the auxiliary theorem supplies exactly its `IsSheafFor` conclusion. The remaining sorry is the strictly smaller local matching-family statement recorded by the new node.

## Second reading by N1

1. Compared the delivered stage-image module with the repository version: the theorem signature is byte-for-byte unchanged; only its proof and proof-only import changed.
2. Compiled the item and auxiliary module with lcompile.py; both compile without errors. The target has no sorry; the auxiliary local theorem is the sole named sorry and has a node and docstring. No forbidden declarations or hollow definitions were added.
3. Checked the auxiliary statement against the target reduction: it fixes an arbitrary object and covering sieve, so it is strictly smaller and has the exact IsSheafFor conclusion needed. Its hypotheses match the target.
4. The proof uses isSheaf_iff_isSheaf_of_type and the auxiliary theorem, preserving the unit route; no imports were removable beyond the replaced proof-only dependency.
5. DAG proof, proof_deps, proof_origin, and the auxiliary node agree with the Lean proof and report. No statement or definition was changed.

Changed only the target proof, added the proof-only auxiliary import, and recorded the local theorem and node.
