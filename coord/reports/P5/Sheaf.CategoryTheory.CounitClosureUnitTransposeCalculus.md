## What changed

Filled the three theorem proofs in
`lean/Sheaf/CategoryTheory/CounitClosureUnitTransposeCalculus.lean`, preserving
all existing statements, definitions, and imports. The proof follows the node's
Steps 1–9 using Mathlib's adjunction Hom equivalences, their naturality and
transport formulas, and ordinary natural-transformation naturality.
Two proved private helpers establish left and right naturality of `closureInput`.
The unique lift uses precisely the assumed Hom bijection on the specified full
subcategory. The ambient transpose is proved by cancelling Delta and using its
naturality and the target's counit equation. The closure transpose uses the
compatibility square, naturality of eta, and the transported adjunction.

## Proved and sorry left

Closed all three original holes:

- `CategoryTheory.CounitClosureTransposeData.calculus`.
- `CategoryTheory.CounitClosureTransposeData.naturality_left`.
- `CategoryTheory.CounitClosureTransposeData.naturality_right`.

All realize `lem-sf-counit-closure-unit-transpose-calculus`.
No holes remain, no holes were added, and no result was split off.
The required `lcompile.py` single-file check passed with no errors or warnings
(4.7 seconds). Existing public declaration headers are unchanged and every
Lean source line is at most 100 columns.

## No longer needed

None. Both existing public imports are retained because the statements use them.
All declared proof dependencies are Mathlib leaves and remain used. There are no
unused Sheaf or WeilConjectures proof imports, and no node or module is withdrawn.
The original DAG proof and the unit route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement defect was found. Mathlib already supplies the
required adjunction formulas; no extra intermediate statements are needed.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
