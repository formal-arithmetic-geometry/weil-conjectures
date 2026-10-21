

## def-exc-proetale-sections-with-support (2026-10-16 01:04 UTC, branch head 4b7f0bed47)

L: independent stage-2 immutable head 4b7f0bed47ad: Existing source declarations define sheaves valued in one fixed coefficient category, while the node depends on modules over the varying finite-coefficient pro-etale ring sheaf; supply a canonical transport/interface and restate the functor on that category.

## lem-weil-pbc-frobenius-vector-bundle-kernel (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 7 (2620 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 7 (2620 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## prop-asd-smooth-base-change (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 1 (4395 characters); step 2 (4109 characters); step 4 (3769 characters); step 5 (2034 characters); step 7 (2683 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 1 (4395 characters); step 2 (4109 characters); step 4 (3769 characters); step 5 (2034 characters); step 7 (2683 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.



## lem-sf-integral-direct-image-constructible (dedicated repair handoff; head 100b8fa832869045abf34c00f31fca7b56574dfe)

The previous worker ended with: re-split (decision of the human, 2026-10-21): the proof in words is 9096 characters. We consider the current split too coarse: a node whose proof is over 3000 characters is rarely proved in one Lean module (stage-3 history: 11 attempts per module on average, more than half blocked). Make the split finer: every argument of the proof that is not elementary becomes a node of its own (statement, source, proof in words) that the step cites, until each node's proof is well under 3000 characters. Keep this node's statement unchanged; its proof becomes the short assembly of the new nodes. Longest steps: step 1 (922 characters); step 2 (1034 characters); step 3 (1003 characters); step 4 (1176 characters); step 5 (1582 characters); step 6 (1537 characters); step 7 (1318 characters). Lean module: Sheaf.Paper.SfIntegralDirectImageConstructible.

Compiler messages and attribution:
re-split (decision of the human, 2026-10-21): the proof in words is 9096 characters. We consider the current split too coarse: a node whose proof is over 3000 characters is rarely proved in one Lean module (stage-3 history: 11 attempts per module on average, more than half blocked). Make the split finer: every argument of the proof that is not elementary becomes a node of its own (statement, source, proof in words) that the step cites, until each node's proof is well under 3000 characters. Keep this node's statement unchanged; its proof becomes the short assembly of the new nodes. Longest steps: step 1 (922 characters); step 2 (1034 characters); step 3 (1003 characters); step 4 (1176 characters); step 5 (1582 characters); step 6 (1537 characters); step 7 (1318 characters). Lean module: Sheaf.Paper.SfIntegralDirectImageConstructible.
