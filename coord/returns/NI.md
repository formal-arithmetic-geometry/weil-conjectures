

## lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away (2026-10-14 17:38 UTC, branch head 7db78add3d)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away: lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## def-weil-absolute-frobenius-scheme (2026-10-15 23:04 UTC, branch head 1b3ec2f5f2)

L: the delivery could not be prepared for review: NOT MERGED def-weil-absolute-frobenius-scheme: the report lacks the heading '## Review by NI' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.

## lem-weil-pbc-constructible-abelian-bounded-exponent (2026-10-15 23:09 UTC, branch head b80df5cadc)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-pbc-constructible-abelian-bounded-exponent: lem-weil-pbc-constructible-abelian-bounded-exponent: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.


## lem-weil-karoubi-envelope-triangulated (2026-10-16 04:53 UTC, branch head a98045f329)

L (re-issued by the launcher; the entry had been lost): sf-integral-compact-support-constructible --stage 1 --reviewer NT-Codex-Q38-b6578f712 --head b6578f7125ae58fc5c5f626358e59df698f8256d --spot-checked Read all required guidance, the complete item, report, unit/chapter route, all 35 cited node statements, and cited source locations. Verified hypotheses, coefficient categories, base-change morphisms, every proof step, edge cases, duplicate/cycle risks, and recorded searches. No new nodes or repairs are needed; review.md was written. --verdict PASS


## prop-weil-pbc-integral-tstructure (2026-10-16 04:53 UTC, branch head 8933bb49c0)

L (re-issued by the launcher; the entry had been lost): NT-Codex-NI-dbb05f32e --head dbb05f32eaa6e58f595028d584ab86a8bd44d934 --spot-checked Read the complete item, cited statements, master sources, report, and unit/chapter route. All four steps, associator directions, inverse calculations, edge cases, and dependency checks pass. Accepted lem-fix-operation-reduction as the declared comparison tool. No new nodes or repairs. Condensed-category and exchange-map comparisons remain separate target obligations; review.md records the checks. --verdict PASS

## sbc-def-admissible-lattices (dedicated repair handoff)

The previous worker ended with: The literature re-review (2026-10-16) returned this split. Keep the route; fix exactly the finding below and re-deliver.

Compiler messages and attribution:
B3 (exact statement dependencies): def-weil-pbc-witness-compatibility is extraneous in stmt_deps. The definition requires only membership in the finite-level essential images, explicitly without chosen witnesses or compatible witness towers; no WIT predicate or compatible witness data of that dependency is used. Remove this edge, retaining the existing essential-image condition unchanged.



## lem-amb-cartier-kummer-map (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 7 (2396 characters); step 9 (2132 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 7 (2396 characters); step 9 (2132 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-fin-normal-open-lisse-image (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 6 (2145 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 6 (2145 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## sk-lem-proper-heart-bound (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 4 (2028 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 4 (2028 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.



## lem-weil-pbc-kflat-fixed-tensor-triangulated (dedicated repair handoff; head d17261b201a63e9843bb11669006577f9c7ee34c)

The previous worker ended with: re-split (decision of the human, 2026-10-21): the proof in words is 8459 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 2 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated

Compiler messages and attribution:
re-split (decision of the human, 2026-10-21): the proof in words is 8459 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 2 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
