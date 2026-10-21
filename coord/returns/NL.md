

## lem-sbc-integral-etale-cover-disjoint-refinement (2026-10-14 17:37 UTC, branch head 4ee6598da9)

L: approved by the reader, but the landing refused it: NOT MERGED lem-sbc-integral-etale-cover-disjoint-refinement: lem-sbc-integral-etale-cover-disjoint-refinement: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.



## sbc-thm-finite-proetale-smooth-base-change (2026-10-16 04:53 UTC, branch head c094128043)

L (re-issued by the launcher; the entry had been lost): Step 2 relies on sbc-thm-bounded-derived-smooth-base-change, whose statement omits the invertible torsion hypothesis required by Stacks Tag 0EYU. The delivery’s own characteristic-p Artin–Schreier example shows the unconditional statement is false, so adding N only to this item does not repair the dependency. Return under delivery-errors E1 and C4; correct the cited bounded theorem or use a correctly stated replacement.


## lem-kun-commutative-exchange-chart (dedicated repair handoff)

The previous worker ended with: The literature re-review (2026-10-16) returned this split. Keep the route; fix exactly the finding below and re-deliver.

Compiler messages and attribution:
B3: stmt_deps contains four nodes not used to state this result: def-sc-raw-restricted-cohomology-class, def-sbc-raw-affine-restricted-cohomology, lem-sbc-abelian-higher-direct-image-class-compatibility, and lem-sbc-abelian-higher-direct-image-natural-comparison. Remove these extraneous statement dependencies; the displayed chart uses the canonical cohomology-presheaf maps already supplied by sbc-lem-higher-direct-image-presheaf. The resolution and mate argument agrees with Tags 0736/07A7.

## lem-amb-linear-trace-invariance (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2367 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2367 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-kun-0ezt (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 4 (3399 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 4 (3399 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-exc-weakly-etale-nagata-j2 (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 9 (2032 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 9 (2032 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## det-proper-heart-bound-lattice (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 5 (5030 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 5 (5030 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-pur-derived-support-comparison-direct-image (2026-10-17 18:19 UTC, branch head 1e2785dc05)

L: independent stage-2 immutable head 1e2785dc05ab: A7/H4: item already stated by Q15 (Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison, theorem AlgebraicGeometry.ProEtale.derivedSupportDirectImageComparison, reviewed PASS, merged 2026-10-17 17:02 batch 630dadf2; ledger 31448, deliveries.log 8849). NL delivers a parallel module DerivedSupportComparisonDirectImage restating the same node and duplicating its notions (supportEtaleOpenKernel~supportEt, supportDirectImageAdjunction~supportDerivedAdjunction, pullback iso~supportDerivedOpenPullback). Its node copy keeps Q15's reviewed_lean but swaps lean, which would orphan the landed module; the report never mentions the existing statement. Correction: withdraw; any defect in Q15's statement goes to the report/HUMAN.md and is repaired in that one module. Secondary H3: clause 3 (open restriction) never relates b to the V-site support functors via rho; C=T only via evaluation at the top open; H11: second reading is the author's self-reading. Otherwise no hollow defs, sole sorry is the main theorem, docstrings ok, hypotheses A:Type(u+1) CommRing Finite with no stronger ones. nt_compile --json: 44.7 s with no error lines printed, rerun hit the 60 s limit under load.


## lem-weil-pbc-ringed-slice-pullback-mate-normalization (dedicated repair handoff; head d17261b201a63e9843bb11669006577f9c7ee34c)

The previous worker ended with: re-split (decision of the human, 2026-10-21): the proof in words is 5591 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 1 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Paper.RingedSlicePullbackMateNormalization

Compiler messages and attribution:
re-split (decision of the human, 2026-10-21): the proof in words is 5591 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 1 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Paper.RingedSlicePullbackMateNormalization

## lem-pur-roos-intrinsic-completeness-equivalence (2026-10-21 07:34 UTC, branch head 23f770385b3)

L: independent stage-2 immutable head 23f770385b3a: H13: the delivery replaces two landed dependency records with narrower one-generator integral special cases. def-weil-pbc-intrinsic-completion: Q22 IntrinsicCompletionCompleted (27 decls, 21 live importers) rebound to IntegralKoszulCompletion (14 integralKoszul* decls). prop-weil-pbc-koszul-reconstruction: Q18 KoszulReconstruction (koszulReconstruction already proved, 13 importers) rebound to a sorry'd integralKoszulReconstruction, orphaning the old modules. A reviewer fix cannot revert dependency records. Correction: drop both dependency node files; move the integral helpers (scalar with its ExistsUnique characterization, Koszul level/step/tower/product unit, one-minus-shift, signed fibre with (u,0) unit, mappingCocone(1-s) Koszul limit with its unit) into the item module or a new definition node the item owns; drop integralKoszulReconstruction; or give a superset record that keeps all old declarations. The item statement is otherwise correct: the five TFAE clauses match the node (sheaf-ideal local test with s=0 included, (t,1) Koszul tower, signed fibre with (dx,(1-s)x-dy) per Mathlib mappingCocone, published completionUnit and IsComplete), with no extra hypotheses and independent universes. All three files compiled clean via nt_compile --json (31.8/21.5/30.0 s).
