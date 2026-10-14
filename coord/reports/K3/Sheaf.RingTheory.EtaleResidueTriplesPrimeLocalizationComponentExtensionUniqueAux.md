## What changed

Replaced the proof of `etaleResidueTriples_primeLocalization_component_extension_unique_aux` by an application of the existing descended affine-model theorem followed by the existing localization epimorphism theorem. Added the two proof-only imports required by this route.

## Proved and sorry left

`etaleResidueTriples_primeLocalization_component_extension_unique_aux` is proved. No new sorry declarations were added.

## No longer needed

The original direct descent-and-localization proof text is no longer needed; no imported module was removed.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan described the descent argument but did not record that the affine-model and epimorphism conclusions were already available as separate declarations. The proof dependency record has been updated to match the actual route.

## Second reading by K3

1. Compared the delivered theorem signature byte for byte with the repository version; unchanged.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The proof-only imports are plain imports. The route uses the existing affine-model and localization-epimorphism declarations, whose remaining `sorryAx` status is upstream and recorded in their nodes.
3. The theorem statement is unchanged and no statements were split off by this delivery; the two cited declarations are existing nodes and no duplicate statement was added.
4. The proof takes the shortest available route through the existing model and epimorphism results. The unit route is preserved; no imports were removed because both proof-only imports are used.
5. Updated the node proof and `proof_deps` to match the two declarations actually applied. No Lean source changes were otherwise needed.

Changed: added the second-reading record and synchronized the existing DAG node's proof route and dependencies with the implementation.
