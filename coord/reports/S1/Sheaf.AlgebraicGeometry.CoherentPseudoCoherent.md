## What changed
Proved `AlgebraicGeometry.Scheme.isPseudoCoherent_singleFunctor_obj_of_isCoherent` with its signature and imports unchanged. For each point, obtain the existing affine finite-free resolution, retain its bound and finite ranks, and compose Mathlib's `mapDerivedCategorySingleFunctor` isomorphism with the inverse of the localized augmentation. The quasi-isomorphism hypothesis is installed locally so Mathlib supplies `IsIso` for its image under `DerivedCategory.Q`.

## Proved and sorry left
Closed the one hole in `AlgebraicGeometry.Scheme.isPseudoCoherent_singleFunctor_obj_of_isCoherent` (node `lem-sc-coherent-pseudo-coherent`). No holes remain in the delivered module, and no holes were added. The proof uses the existing `AlgebraicGeometry.coherent_affine_free_resolution`, which remains a separate, already stated dependency with its own sorry; this delivery does not prove that dependency.

## No longer needed
None. Both planned dependencies (`lem-sc-coherent-affine-free-resolution` and `def-pur-pseudo-coherent-complex`) remain used. No imports were removed, no new modules or nodes are delivered, and the unit route is retained.

## Where the brief, the DAG or earlier work was wrong
None. The planned conversion from a local quasi-isomorphism to the derived-category isomorphism is provided by Mathlib, so no intermediate statement is needed.

## Second reading by S1

1. Compared the delivered module with the repository version. The theorem signature, definitions, and public imports are byte-for-byte unchanged; only the proof body was filled in.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or explicit `sorryAx`. The proof uses the existing finite-free-resolution theorem and Mathlib's derived-category map and `QuasiIso` instance, so it does not introduce an arbitrary witness or hollow definition.
3. Checked the theorem against the node statement and edge cases conceptually: the pointwise local resolution is exactly the defining condition for pseudo-coherence, including the degree-zero single complex. No new statement was split off, and the existing statement is unchanged and true.
4. Checked pruning and imports. The public imports are needed by the statement; `CoherentAffineFreeResolution` is proof-only and remains a plain import. Both DAG proof dependencies are used, and no old dependency or module can be removed.
5. Checked the DAG route: the proof retains the unit's local finite-free-resolution route and the node's proof dependencies. No unit step is bypassed, and no node or change record is needed.

Changed only this report by adding this second-reading record; no Lean declarations, imports, or DAG statements were changed.
