## What changed
Proved `affinePushforward_baseChange_isIso` by applying the existing affine-open section criterion for module morphisms. Added `AffinePushforwardBaseChangeIsIsoOnAffine.lean` with the affine-local section bijectivity statement left for a subsequent worker.

## Proved and sorry left
The target `affinePushforward_baseChange_isIso` is proved. The new theorem `affinePushforward_baseChange_app_bijective` remains `sorry` (node `lem-weil-pbc-affine-pushforward-base-change-app-bijective`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The DAG omitted the affine-local section bijectivity intermediate statement needed to use the library's local-to-global isomorphism criterion.

## New nodes
Added `lem-weil-pbc-affine-pushforward-base-change-app-bijective`, matching the new intermediate theorem.

## Earlier second reading (a previous round; superseded)
The target proof applies the standard affine-open local criterion without changing its statement. The new affine section theorem is a strictly simpler intermediate claim and is exactly the remaining affine computation.

## Second reading by E2
1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged; only proof imports and the proof body differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. They compile without errors or warnings; the only remaining `sorry` is the named split theorem `affinePushforward_baseChange_app_bijective`, and there are no forbidden declarations. Verdict: pass.
3. Checked the split theorem against the library and Mathlib searches. It is a genuine affine-section reduction, strictly simpler than the target, with a source, docstring proof, and matching DAG node; no duplicate declaration was found. Verdict: pass.
4. The target takes the shortest available route through `isIso_of_bijective_app_of_isAffineOpen`; the affine computation remains as the necessary lower statement. The proof-only imports are plain imports, including the corrected `LocallyFreeAffine` import. Verdict: pass.
5. The target node proof now records the local bijectivity step, and the new node records the split theorem and its source. The unit `sk-thm-p1` route is preserved. Verdict: pass.

Changed the new module's `LocallyFreeAffine` import from public to proof-only, and added this second-reading record. No theorem statements were changed.
