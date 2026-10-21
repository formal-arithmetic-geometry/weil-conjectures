



## thm-amb-p1-decomposition (2026-10-16 04:53 UTC, branch head 11be63537e)

L (re-issued by the launcher; the entry had been lost): Major exact-target mismatch: the master source uses pro-etale A_{E,n}/completed coefficient objects, while delivery changes to ordinary-etale finite A with added N hypotheses. Resolve and record this target correction upstream before resubmission (B9, E7).

## det-pe-topos-functoriality-inverse-image (2026-10-16 17:57 UTC, branch head 95970f33a2)

L: independent stage-2 immutable head 95970f33a2a1: H1/H2/H11: the item has already landed at 6e45d0d0f5 (Q14, reviewed_lean pass, present in the delivery's base fe31ddf7a2). Delivery 95970f33a2 changes nothing in substance: the module differs only in 'Authors: Q14 -> ND', the node only in lean.by Q14 -> ND and lean.note, plus an ND report that presents Q14's landed module as ND's work without saying it had landed. Correction: do not land and do not re-deliver the same content; release the claim. Any real defect must be delivered as a change on top of 6e45d0d0f5, keeping Q14's attribution. Content verified anyway: clauses 1-5 match the node (base change Over.pullback @WeaklyEtale, lowerStar/sheafPullbackConstruction adjunction, colimits/finite limits, abelian underlying-set iso plus exactness, conjugate of lowerStarComp with a correctly typed unit equation); defs carry no sorryAx; statement verbatim; nt_compile clean. Existing H4 overlap of setPullback/setPullbackComp with Scheme.proEtaleSheafInverseImage/profinitePointSetComp is already in the landed version.



## det-sf-comparison-affine-continuity (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 1 (2349 characters); step 5 (2269 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 1 (2349 characters); step 5 (2269 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## det-lem-int-ext-continuity (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2342 characters); step 3 (2512 characters); step 4 (2169 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2342 characters); step 3 (2512 characters); step 4 (2169 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.



## prop-weil-pbc-scalar-extension (dedicated repair handoff; head 100b8fa832869045abf34c00f31fca7b56574dfe)

The previous worker ended with: re-split (decision of the human, 2026-10-21): the proof in words is 12653 characters. We consider the current split too coarse: a node whose proof is over 3000 characters is rarely proved in one Lean module (stage-3 history: 11 attempts per module on average, more than half blocked). Make the split finer: every argument of the proof that is not elementary becomes a node of its own (statement, source, proof in words) that the step cites, until each node's proof is well under 3000 characters. Keep this node's statement unchanged; its proof becomes the short assembly of the new nodes. Longest steps: step 1 (1520 characters); step 2 (1159 characters); step 3 (1036 characters); step 4 (835 characters); step 5 (1745 characters); step 6 (1525 characters); step 7 (1887 characters); step 8 (1069 characters); step 9 (1277 characters). Lean module: Sheaf.Paper.PbcScalarExtension.

Compiler messages and attribution:
re-split (decision of the human, 2026-10-21): the proof in words is 12653 characters. We consider the current split too coarse: a node whose proof is over 3000 characters is rarely proved in one Lean module (stage-3 history: 11 attempts per module on average, more than half blocked). Make the split finer: every argument of the proof that is not elementary becomes a node of its own (statement, source, proof in words) that the step cites, until each node's proof is well under 3000 characters. Keep this node's statement unchanged; its proof becomes the short assembly of the new nodes. Longest steps: step 1 (1520 characters); step 2 (1159 characters); step 3 (1036 characters); step 4 (835 characters); step 5 (1745 characters); step 6 (1525 characters); step 7 (1887 characters); step 8 (1069 characters); step 9 (1277 characters). Lean module: Sheaf.Paper.PbcScalarExtension.
