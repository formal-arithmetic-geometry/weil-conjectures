

## def-weil-constructible-heart (2026-10-16 01:30 UTC, branch head 1d3ffc72f8)

L: independent stage-2 immutable head 1d3ffc72f8ef: file-only compilation failed: preliminary Sheaf/Paper/IntegralOperationsWellDefined.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [16.6 s]
preliminary Sheaf/Paper/SfIntegralReductionTower.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [9.9 s]
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [16.6 s]
library Sheaf/Paper/IntegralOperationsWellDefined.lean

[22.0 s]
sandbox Sheaf/Stage2/Sandbox1.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [10.1 s]
library Sheaf/Paper/SfIntegralReductionTower.lean

[10.3 s]
sandbox Sheaf/Stage2/Sandbox2.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [3.2 s]
library Sheaf/Paper/SfIntegralConstructibleTriangulated.lean

[5.2 s]
sandbox Sheaf/Stage2/Sandbox3.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [4.9 s]
library Sheaf/Paper/IntegralConstructibleLinear.lean

[8.4 s]
sandbox Sheaf/Stage2/Sandbox4.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [6.6 s]
library Sheaf/Paper/IntegralScalarExtension.lean

[7.3 s]
sandbox Sheaf/Stage2/Sandbox5.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [7.7 s]
library Sheaf/Paper/IntegralScalarExtensionConstructible.lean

[9.4 s]
sandbox Sheaf/Stage2/Sandbox6.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [15.8 s]
library Sheaf/Paper/RationalConstructibleCoefficients.lean
/tmp/nt-local-compile-te9zabir/lean/Sheaf/Paper/RationalConstructibleCoefficients.lean:6:0: error: object file '/home/ubuntu/weil-lean/.lake/build/lib/lean/Sheaf/Paper/IntegralScalarExtensionWellDefined.olean' of module Sheaf.Paper.IntegralScalarExtensionWellDefined does not exist

[0.4 s]

## cor-coef-finite-verdier (2026-10-16 02:30 UTC, branch head 4c0488cecf)

L: independent stage-2 immutable head 4c0488cecf20: Wrote review.md. All three snapshot modules compile through scompile.py. H3/H13: arbitrary categories and predicates replace the geometric constructions; cocycle quantifiers are incorrect; evaluation compatibility omits the comparison component; dependency modules omit required clauses. Also found H2 signature-record mismatch and H8 incomplete proof docstrings. Requires substantive re-delivery.

## lem-coef-finite-dualizing (2026-10-16 02:44 UTC, branch head 17030bd826)

L: independent stage-2 immutable head 17030bd826e5: Review explicitly requires re-delivery: H13/H3 missing geometric projection/counit compatibility; H13 incomplete exceptional-inverse-image restrictions and integral/rational/common-stage coefficient regimes; H13/H3 missing transported double-dual invertibility and restricted Verdier duality. Also H6 completed local naturality proof violates the sorry-only gate, and H2 all five owning-node statement strings lack verbatim formatting. Independent compiler reproduction has no final result recorded, so the review is incomplete. No files changed.

## thm-coef-finite-hom (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 3 (2938 characters); step 7 (5783 characters); step 8 (3355 characters); step 14 (2525 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 3 (2938 characters); step 7 (5783 characters); step 8 (3355 characters); step 14 (2525 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-a1-integral-pullback-completed-comparison (2026-10-17 23:04 UTC, branch head 0e473be282)

L: independent stage-2 immutable head 0e473be282bd: Errors H3/§1(C): the statement correction replaces the integral derived pullback (def-pur-integral-derived-operations, Lean integralDerivedPullback; Stacks 099N(5) RHS R lim Lf*(M⊗Λ/I^n)) with ordinary d.pull. Unfolding completedPullReduction, the Lean claims ordinary pullback of every intrinsically complete object is complete with invertible completion unit. Stacks 099N(2) defines Lf*_comp as Lf* followed by completion and does not say this, so the claim is unsourced and stronger, about a different functor. H8: proof steps 6-10 build gamma from the integral cone C(B_•) and do not prove the new statement. The shift clause was dropped because the subcategory lacks HasShift (not a source reason; it can be stated objectwise), while the docstrings still claim shift compatibility. Citer audit: all three citers marked holds:false with no repair. Correction: restore integral pullback vs completed pullback, with the coefficient identification integralTowerModules ↔ d.derived for (O_E,ϖ) as a §1(B) helper in this delivery (or Rlim of finite pullbacks identified with integralDerivedPullback); keep the old-direction projection clause and an objectwise shift clause; fix the docstrings. Checked fine: binders/universes, no extra assumptions, ℕ indexing, statement verbatim, source/blueprint docstrings, report sections, sorry only. Per-file nt_compile on the side overlay finished with no errors (6.7 s).

## lem-per-henselian-valuation-coarsenings (2026-10-19 01:46 UTC, branch head 770249ea4cb)

L: approved by the reader, but the landing refused it: NOT MERGED lem-per-henselian-valuation-coarsenings: lem-per-henselian-valuation-coarsenings: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.





## lem-weil-pbc-ordered-exchange-coefficient-comparison (dedicated repair handoff; head 5594c555399d0cb43e1ad335295749d4273c5e2b)

The previous worker ended with: re-split (decision of the human, 2026-10-21): the proof in words is 15922 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 5 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Paper.OrderedExchangeCoefficientComparison

Compiler messages and attribution:
re-split (decision of the human, 2026-10-21): the proof in words is 15922 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 5 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.Paper.OrderedExchangeCoefficientComparison

## det-def-sfb-filtered-two-colimit-characterization (2026-10-21 07:35 UTC, branch head a68ccc954d4)

L: approved by the reader, but the landing refused it: NOT MERGED det-def-sfb-filtered-two-colimit-characterization: det-def-sfb-filtered-two-colimit-characterization: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## sk-lem-nagata-sketch-dense-valuative (2026-10-21 07:39 UTC, branch head f7b2971e53f)

L: approved by the reader, but the landing refused it: NOT MERGED sk-lem-nagata-sketch-dense-valuative: cited node lemma-nagata-scheme-image-ideal-qc: statement changed since the reviewed delivery; rebase and revalidate the citation Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.
