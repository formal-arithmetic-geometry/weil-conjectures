## What changed
Added the proof-only import of `RootNormalizationGenericSourceEtalePoint` and proved the original theorem by introducing the point and applying the pointwise reduction. Added the pointwise intermediate theorem as a named sorry with its own module and DAG node.

## Proved and sorry left
The original declaration `GaloisCover.root_normalization_generic_source_etale` is proved. The intermediate declaration `root_normalization_generic_source_etale_point` remains sorry, with node `lem-sbc-root-normalization-generic-source-etale-point`.

## No longer needed
None; all original imports remain part of the statement interface.

## Where the brief, the DAG or earlier work was wrong
The original proof plan requires a substantial pointwise Abhyankar calculation, so it was split into a fixed-point intermediate theorem before applying the universal quantifier.

## New nodes
`lem-sbc-root-normalization-generic-source-etale-point` is stated in `lean/Sheaf/AlgebraicGeometry/Morphisms/RootNormalizationGenericSourceEtalePoint.lean`.

## Earlier second reading (a previous round; superseded)
The pointwise declaration is a strict fixed-point substatement of the original universal conclusion; the main proof applies it after introducing the quantified point. The original signature is unchanged and the unit route is retained.

## Second reading by K2

1. Compared the delivered item module with the repository version. The target declaration's signature is byte-for-byte unchanged; only a proof-only import and proof body were added. Verdict: pass.
2. Compiled both delivered modules with lcompile.py --all. The original target is proved, and the only remaining sorry is the explicitly named pointwise theorem. No forbidden declarations or hollow definitions were introduced. Verdict: pass subject to the documented split theorem.
3. Checked the pointwise statement against the target and its source. It is the fixed-point specialization needed by the universal conclusion, with the same hypotheses and a strictly narrower conclusion. The node and docstring record its source and proof plan. Verdict: pass.
4. Checked pruning and dependencies. The original imports remain required by the public target signature; the new pointwise module is imported privately for the proof. The unit route through the generic source etale statement is retained. Verdict: pass.
5. Checked the DAG node and Lean declaration agree, including declaration name, module, statement, source, proof origin, and unit/chapter. Verdict: pass.

Changed only the item proof, added the proof-only pointwise module and its DAG node, and documented the remaining split theorem.
