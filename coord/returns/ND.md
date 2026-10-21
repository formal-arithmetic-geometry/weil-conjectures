



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

## prop-weil-pbc-scalar-extension (2026-10-21 04:07 UTC, branch head f0d35797bf)

L: approved by the reader, but the landing refused it: NOT MERGED prop-weil-pbc-scalar-extension: cited node lem-sfb-kflat-scalar-comparison-normalization: statement changed since the reviewed delivery; rebase and revalidate the citation Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-closed-support-bounded-continuity (2026-10-21 04:08 UTC, branch head b5d521be4a)

L: independent stage-2 immutable head b5d521be4a42: H2: the delivery adds theorem node det-lem-formal-closed-support-adjunction to stmt_deps only for the plain defs supportModules (abbrev) and closedSupport (= supportKernel ⋙ supportPullback, no .choose) in Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction; no def node owns them. Re-deliver with an existing:true definition node on that unchanged module (declaration closedSupport; declarations supportModules, supportModules_grothendieck, supportPullback(+_additive), supportKernel, supportKernelι, closedSupport, closedSupport_additive; statement verbatim `def closedSupport …`; node statement Γ_Z(M)=i^*ker(M→j_*j^*M)), cite it in place of the theorem (theorem only in proof_deps if a step uses it); Lean can stay byte-identical, update lean.note. Otherwise substance correct: all hypotheses/clauses match (arbitrary comm condensed Λ, NoetherianSpace T only, complement orientation, small filtered Type (u+1) diagrams, cohomological IsGE bounds, colimit.post on functorial K-injective models, D^{≥c} preservation for all c), statement verbatim, docstrings/H8 ok, sorry only. nt_compile could not run (published build lacks mathlib package .lake: 'unknown module prefix Mathlib'); relied on delivery's clean scompile 11.4/10.3 s.
