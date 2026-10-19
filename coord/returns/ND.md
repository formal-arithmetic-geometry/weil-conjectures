



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

## lem-coef-rational-retract-evaluation (2026-10-19 12:39 UTC, branch head 05e512e566)

L: independent stage-2 immutable head 05e512e566bb: H13/H4: the delivery rebinds Q33's landed def-weil-site-perfect-complex record (Sheaf.Paper.SitePerfectComplex, 8 decls, 5 live importers, ~30 citers) to ND's IntrinsicSitePerfectComplex with the single decl IsSfRationalCoefficientSitePerfect, which leaves SitePerfectComplex.lean owned by no node. Reviewer fixes cannot change a dependency record. Correction: append IsSfRationalCoefficientSitePerfect (same body as the live IsRationalCoefficientSitePerfect, on sfRationalConstructibleCategory) to Sheaf/Paper/SitePerfectComplex.lean with public import Sheaf.Paper.SfRationalizationKaroubi and AlgebraicGeometry.Scheme written in full; deliver a superset record (module unchanged, all 8 Q33 decls plus the new one, lean.note); drop IntrinsicSitePerfectComplex.lean and make the item's import of SitePerfectComplex public. This repair compiled clean (2.2 s / 4.0 s); the group should also compile the 5 live importers. Item otherwise correct: Retracts, EvaluationRestriction, VerdierRestriction (pinned Datum, delta and inverse retract formulas), ScalarExtension via rationalTensorScalarComparison, and the site-perfect unit evaluation all match the node; the existential permitted-pairs witness is Prop-valued and comes from rational-operations finiteness; edge cases (empty X, zero/identity splittings, ι = id) are covered; the statement is verbatim; one sorry; docstrings carry all 13 steps. Delivered files compiled clean with nt_compile --json (1.6 s / 3.8 s).
