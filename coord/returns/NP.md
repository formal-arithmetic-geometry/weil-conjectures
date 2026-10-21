

## lem-sc-etale-section-zero-open (2026-10-14 17:37 UTC, branch head dbddb95786)

L: approved by the reader, but the landing refused it: NOT MERGED lem-sc-etale-section-zero-open: lem-sc-etale-section-zero-open: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## def-sf-fullcd-class (2026-10-15 21:14 UTC, branch head 0a3b4e4794)

L: approved by the reader, but the landing refused it: NOT MERGED def-sf-fullcd-class: coord/.merge.lock held for 120 s by pid 1890503: /usr/bin/python3 tools/merge_delivery.py Q17 thm-kun-0f1p --stage 1 --reviewer NT-Codex-Q17-7d0ed5a62 --head 7d0ed5a627017ec594ebdc5aecd28bbf5a5241f6 --spot-checked Reviewed the complete item, report, cited DAG statements, blueprint route, Stacks sources, hypotheses, coefficient category, base-change morphism, qcqs and finite-cohomological-dimension arguments, edge cases, and unit/chapter route. No new nodes or repair files are needed. Recorded a pre-existing typo in lem-kun-kunneth-via-0f1n's diagram (lower-right Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## prop-finite-compact-support-constructibility (2026-10-15 23:08 UTC, branch head 2e82ebea7f)

L: approved by the reader, but the landing refused it: NOT MERGED prop-finite-compact-support-constructibility: check_dag.py: route: lem-pod-compact-support-finite-coefficient-comparison (sk-lem-finite) depends on prop-finite-compact-support-constructibility (sk-prop-sf-cbc), outside its unit's route | route: lem-pod-compact-support-finite-coefficient-comparison (sk-lem-finite) depends on prop-finite-compact-support-constructibility (sk-prop-sf-cbc), outside its unit's route Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-exc-proetale-closed-exact (2026-10-16 01:19 UTC, branch head fea2ffc45e)

Major E1/E7/C4 coefficient-category and statement mismatch: the archived master declaration is for arbitrary Ring R and Sheaf(ProEt.topology X)(ModuleCat R), while the delivery proves only a finite constant-ring category and claims unsupported noncommutative extensions. B5: the item still cites Stacks Tag 09A9 although the report claims correction to exact Tag 09BM. Step-level checks and source locations are recorded in review.md.

## prop-exc-finite-etale-adjoint (2026-10-16 03:28 UTC, branch head 4def492a5b)

L: the delivery could not be prepared for review: NOT MERGED prop-exc-finite-etale-adjoint: the report lacks the heading '## Review by NP' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.


## def-pur-smooth-purity-map (2026-10-16 04:53 UTC, branch head cd45b5f6e3)

L (re-issued by the launcher; the entry had been lost): s/merge_delivery.py Q42 lem-kun-0f09 --stage 1 --reviewer NT-Codex-Q42-f3583ed62 --head f3583ed627e504efb6cbf29c1b4a8afbe7bf686b --spot-checked Reviewed item lem-kun-0f09, all six steps, cited DAG statements, Stacks Tags 0F09/0EYU/0EZT/015J/01SD, unit/chapter route, and archived master coefficient category. Verified hypotheses, coefficient corner, canonical exchange, spectral-sequence comparison, edge cases, searches, tool uses, and acyclicity. Wrote review.md; no repairs needed. --verdict PASS

## thm-sf-fullcd-class (2026-10-16 06:44 UTC, branch head 7dbc87e279)

L: approved by the reader, but the landing refused it: NOT MERGED thm-sf-fullcd-class: thm-sf-fullcd-class: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-weil-pbc-quasifinite-affine-etale-thickening-decomposition (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 4 (2074 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 4 (2074 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-asd-smooth-generic-direct-image (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 5 (2085 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 5 (2085 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## det-proper-heart-bound-torsion (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2653 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2653 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## prop-weil-pbc-descent-functors (dedicated repair handoff; head 5594c555399d0cb43e1ad335295749d4273c5e2b)

The previous worker ended with: re-split (decision of the human, 2026-10-21): the proof in words is 5328 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 1 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Paper.PbcDescentFunctors

Compiler messages and attribution:
re-split (decision of the human, 2026-10-21): the proof in words is 5328 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 1 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Paper.PbcDescentFunctors

## sk-def-sf-admissible (2026-10-21 08:13 UTC, branch head c9664d838c3)

L: independent stage-2 immutable head c9664d838c32: H13: the delivery rewrites the landed NW record of def-weil-finite-tor-amplitude (existing:true FiniteTorAmplitudeSites/finiteTorConstructibleEtale, used by 12 live modules) to FiniteTorAmplitude/finiteTorConstructible and drops finiteTorConstructibleEtale. A reviewer fix cannot change a dependency record. Correction: a superset record (Sites module publicly imports FiniteTorAmplitude, or the reverse, with both declaration families listed); the item module can stay unchanged. The item itself is faithful: FullCD over all sheaves and every V in Y.ProEt, every right adjoint preserves D^b_c, one signed pair (c-,c+) is chosen before G and a<=b, D^b_ctf preservation, all hypotheses as in the node, edge cases (n=1, cCD=0, empty interval) covered, no sorry, docstrings and verbatim statement correct. nt_compile --json: 32.6 s clean.
