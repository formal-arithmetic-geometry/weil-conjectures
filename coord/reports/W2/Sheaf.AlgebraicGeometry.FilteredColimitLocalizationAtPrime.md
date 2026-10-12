## What changed
Added `FilteredColimitLocalizationAtPrimeData` as an intermediate theorem carrying the localization-colimit construction, and proved the prime contraction and transition compatibility clauses in `filteredColimitLocalizationAtPrime`.

## Proved and sorry left
`AlgebraicGeometry.filteredColimitLocalizationAtPrime` is proved from the prime-comap lemmas, colimit naturality, and the intermediate theorem. `AlgebraicGeometry.filteredColimitLocalizationAtPrime_data` remains a named `sorry`, with node `lem-weil-pbc-filtered-colimit-localization-at-prime-data`.

## No longer needed
None beyond the imports used by the proof.

## Where the brief, the DAG or earlier work was wrong
The full fraction-level universal-property proof was too large for this session; it is isolated as a strict intermediate statement rather than left as an anonymous partial proof.

## New nodes
`lem-weil-pbc-filtered-colimit-localization-at-prime-data` records the intermediate localization-colimit construction.

## Earlier second reading (a previous round; superseded)
The target statement is unchanged. The added intermediate theorem is a strict existential part of the target and is the only remaining sorry.

## Second reading by W2
1. **No accidental visible changes:** compared both delivered Lean modules with the repository. The existing target declaration has the same signature byte for byte; the new data declaration is the only added declaration.
2. **Compilation and axioms:** compiled all sandbox modules successfully. The target has only the permitted axioms plus `sorryAx` from the explicitly named split theorem; there are no forbidden commands or hollow definitions.
3. **Split statement:** `filteredColimitLocalizationAtPrime_data` is true by the cited fraction construction and is exactly the existential remainder of the target. Its docstring, node, and `sorry` agree; no duplicate library statement was found.
4. **Pruning and route:** the target proof uses the Mathlib prime-comap and colimit-naturality facts plus the split theorem. Both imports are used, and the unit route is retained through the existential data theorem. No old proof dependency is removable.
5. **DAG agreement:** the target node records the new proof dependency and the data node records the split theorem, module, declaration, source, and proof route consistently.

Changed only the target proof by filling its two elementary clauses and added the explicitly tracked intermediate theorem and node; no statement or definition was weakened.
