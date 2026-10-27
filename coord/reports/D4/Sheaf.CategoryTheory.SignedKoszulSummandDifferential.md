## What changed

Added the strictly smaller theorem `CategoryTheory.ringedNegativeKoszulBasis_d_succ` to the item module. It isolates the ordered negative Koszul pure-basis differential before tensoring with the arbitrary coefficient complex. The assigned theorem `CategoryTheory.ringedNegativeKoszulSummand_D₂_succ` remains unchanged with its original proof hole. No imports or existing definitions were changed.

## Proved and sorry left

No existing hole was closed. The new named theorem `ringedNegativeKoszulBasis_d_succ` remains a single split-off proof hole, with node `lem-cbc-signed-koszul-basis-differential`. The assigned theorem `ringedNegativeKoszulSummand_D₂_succ` remains its original proof hole, with node `lem-cbc-signed-koszul-summand-differential`. No definition contains `sorry`.

## No longer needed

None. The basis differential is a required lower-level part of the parent proof, and the existing imports remain necessary for its statement.

## Where the brief, the DAG or earlier work was wrong

The declared proof plan has a genuine intermediate calculation that was not represented as a separate node: the differential of the ordered pure basis itself. The full theorem additionally needs tensor scalar transport and coefficient regrouping. Those steps were not completed within this delivery.

## New nodes

`lem-cbc-signed-koszul-basis-differential` records the ordered-basis differential as a strictly smaller statement. Its source, induction proof, and Lean declaration are in `dag/nodes/sec-smooth-purity/lem-cbc-signed-koszul-basis-differential.json`.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
