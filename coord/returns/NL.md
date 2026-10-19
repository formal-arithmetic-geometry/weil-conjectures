

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

## def-sf-cup (2026-10-19 22:28 UTC, branch head 096576b329)

L: independent stage-2 immutable head 096576b3292b: H2 (theorem stmt_dep finding): def-sf-cup adds theorem node lem-fix-projection-compactification-comparison to stmt_deps only for FixProjectionCompactification.identitySquare, a plain def (not .choose of the theorem) in Sheaf.Paper.FixProjectionCompactificationComparison. Correction: put identitySquare under a definition node (e.g. a new def node with an existing:true lean record on that declaration and module, module unchanged) and have def-sf-cup cite it in stmt_deps instead of the theorem; do not redefine the square privately (H4). The rest checked out: all clauses match at the finite, integral, rational and common stages (finite-Tor inputs; projection with second input Ra_*L on the point; Ra_!(1 tensor counit); the datum's own stage operations; no coherence properties asserted). Edge cases and universes ok; no hollow defs or sorry; docstrings present. nt_compile --json on the snapshot module: 3.8 s, rc 0, clean. Advisories: finite stage is in the fixed-ring presentation with _S unused, consistent with the datum's finiteExchangeProjection; Second reading section is the standard placeholder.
