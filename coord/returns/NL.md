

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

## lem-pod-stratified-dualizable-bounded (2026-10-21 13:24 UTC, branch head ebe38b889e6)

L: independent stage-2 immutable head ebe38b889e66: H1: no Lean module, item lean record is null, report has only '## Review by NL' (no '## Second reading by NL'), and the report's listed new node lem-pod-constructible-strata-detect-zero and citations.json are absent from the snapshot and from live, though proof Step 5 cites the node. H2: JSON diff vs side-live shows proof, proof_deps, proof_origin, split_report, mathlib_searches and tool_uses rewritten and the landed reviewed record dropped; statement unchanged. A7/S1 supersession: ledger 11:15 records NU's stage-1 merge, so this competing 6-step split came after it. Correction: deliver a stage-2 Lean statement (sorry proof, docstrings with HRS Cor. 4.11/Lemma 4.10/Def. 3.3 and the blueprint id, verbatim lean record) on the live NU-split node with a proper second-reading section, or retire the claim. Nothing compiled (no Lean, no FIX).

## lem-sfb-continuous-algcl-tame-boundary-comparison (2026-10-21 13:35 UTC, branch head 6a13afbab11)

L: independent stage-2 immutable head 6a13afbab114: Superseded, and not a stage-2 delivery. NF 26a608e08's 8-step split of this item landed at 21:31:15 (FIX MERGED e00be35abc) and is reviewed live (NT-cc-NF-26a608e08), before this S2 review began at 21:32:40. NL 6a13afbab is the stage-1 head (6-step split, two new nodes lem-sfb-tame-stratum-inertia-descent and lem-sfb-continuous-tame-inertia-koszul, which duplicate the live lem-sfb-tame-stratum-kummer-descent and lem-sfb-tame-inertia-continuous-koszul) re-sent on the S2 lane. H1: no Lean module, no '## Worker report' or '## Second reading by NL' (report is the 'NL stage-1 report'). H2: item changed in proof/proof_deps/status/split_report, and there is no lean record. H11: no Lean statement to read. Correction: drop this delivery; any further NL contribution must rebase on the live split and its node ids. No fixes written, nothing compiled.
