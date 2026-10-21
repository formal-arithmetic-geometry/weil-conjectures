

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





## lem-sfb-ringed-site-strict-perfect-hom (dedicated repair handoff; head d17261b201a63e9843bb11669006577f9c7ee34c)

The previous worker ended with: re-split (decision of the human, 2026-10-21): the proof in words is 3221 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 1 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom

Compiler messages and attribution:
re-split (decision of the human, 2026-10-21): the proof in words is 3221 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 1 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom
