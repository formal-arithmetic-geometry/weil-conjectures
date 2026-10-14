## What changed
Added the proof-only import of LocalMapPairDefect and reduced the target to a new core theorem asserting eventual PairDefectZero. The target converts PairDefectZero to PairCompatibility using the existing theorem.

## Proved and sorry left
The target theorem `finitePresentation_local_map_pair_eventually_composites_compatible` is proved. The new core theorem `finitePresentation_local_map_pair_eventually_composites_defect_zero_core` remains `sorry` (node `lem-pc-fp-local-map-pair-composites-defect-zero-core`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The DAG's stated route requires a substantial overlap-defect construction; this delivery isolates that construction as a separate core theorem.

## New nodes
`lem-pc-fp-local-map-pair-composites-defect-zero-core` records the isolated overlap-defect eventual vanishing statement.

## Earlier second reading (a previous round; superseded)
The target proof is checked by compilation; the new core statement is the overlap-defect portion of the argument and is strictly stronger input than the final compatibility conversion.

## Second reading by A4

1. **Statements unchanged.** Compared the delivered module with the repository version. The existing target theorem signature is byte-for-byte unchanged; the added core theorem is a separate named split-off statement, and its DAG node matches its Lean declaration.
2. **Proof correctness.** Compiled the module with `lcompile.py`; the target proof uses `finitePresentation_local_map_pair_eventually_composites_defect_zero_core` followed by `pairCompatibility_of_pairDefectZero`. The only remaining `sorry` is the named core theorem, with a matching node and source/docstring.
3. **Search and novelty.** Checked the local library and Mathlib for `PairDefectZero`, `PairCompatibility`, and the eventual composite theorem. The conversion theorem is already imported; no duplicate auxiliary declaration was added.
4. **Pruning and imports.** `LocalMapPairDefect` is required publicly because the new theorem's public statement contains `PairDefectZero`; all other imports remain required by the existing public signature or proof context. The DAG target proof and proof dependencies were updated to record the core theorem route.
5. **Unit route.** The delivery preserves the unit's overlap-defect route by isolating its eventual vanishing step and then applying the existing compatibility conversion.

Changed only the target module, the target node's proof metadata, the new core node, and this report. No existing declaration signature or definition was changed.
