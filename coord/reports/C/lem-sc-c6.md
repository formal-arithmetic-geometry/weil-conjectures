# Delivery report: lem-sc-c6

## Worker report

- Checked the C6 statement against the master blueprint at `sk-thm-p1/lem-sc-c6.md`.
- The statement already introduces the required objects and has the correct dependencies on `def-weil-pbc-eight-curve-assertions`, `def-sc-field-extension`, and `def-sc-curves`.
- Rewrote the imported proof as one complete sourced step: apply `thm-sc-constant-invariance` with `n = r`, then identify its pullback map with the maps in the two cited definitions. The cross-unit theorem is recorded as a reusable tool lemma (`tool_uses`), since this item uses its already-established invariance result as a black box.
- Added the proof source location and recorded LeanSearch, Loogle, and Mathlib-source grep searches. No Mathlib declaration states this curve cohomology invariance result, so no new leaf or split dependency node was created.
- No Lean was written and nothing was compiled.

## Review by C

Reviewed 2026-10-09. The statement agrees with the blueprint and the `sk-thm-p1` route. The proof uses exactly the existing theorem that supplies invariance for prime-to-characteristic constant sheaves and explicitly accounts for the map identification. The theorem is accepted here as a tool use, because it is consumed as a black-box result rather than replacing a unit proof step. The proof dependency union matches the step uses; the node has all three required Mathlib search kinds and is marked `split`. No new node is needed, and no files outside this item and its report are included.
