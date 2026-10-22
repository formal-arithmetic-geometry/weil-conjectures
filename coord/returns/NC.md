

## lem-pur-coprojection (2026-10-15 23:15 UTC, branch head 739422f007)

L: approved by the reader, but the landing refused it: NOT MERGED lem-pur-coprojection: coord/.merge.lock held for 120 s by pid 3154669: /usr/bin/python3 tools/merge_delivery.py Q32 lem-pur-twist-sheaf-locally-free --stage 1 --reviewer NT-Codex-Q32-57ebf6020 --head 57ebf6020c63e81ec6f497a759f5070ec6a4ad9e --spot-checked Read the full item, all twelve steps, all 32 cited-node statements, and available cited sources. Verified compatible roots, completed-coefficient comparisons, K-flat reductions, and the actual Roos-triangle maps. Empty-scheme correction is valid; no cycles, duplicate nodes, or repairs found. Accepted all fifteen declared tool uses. Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.



## fix-prop-projection-formula (2026-10-16 05:18 UTC, branch head ac37762a80)

L: independent stage-2 immutable head ac37762a805a: Wrote review.md. All five immutable modules compile through scompile.py, but H3/H13 substantive failures remain: arbitrary maps, Tor predicates and compatibility propositions replace the canonical constructions; four dependency modules do not define their nodes. Also documented H2, H8 and H11 corrections. Branch unchanged.



## lem-weil-pbc-strict-tower-exchange-mate-normalization (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 5 (2096 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 5 (2096 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-weil-pbc-etale-constant-shriek-rel-dim-1 (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 4 (2617 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 4 (2617 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-sf-compact-coefficient-composition (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2391 characters); step 7 (2048 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2391 characters); step 7 (2048 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## det-lem-int-ext-bound (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 6 (2975 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 6 (2975 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-zl-immersion-weil-local-behavior (2026-10-17 21:07 UTC, branch head e1d66eb0f0)

L: independent stage-2 immutable head e1d66eb0f04e: H1: missing stage-2 Lean module/lean record and required report sections; redeliver with scompile evidence.

## lem-zl-affine-geometric-components-finite-extension (2026-10-17 22:33 UTC, branch head 408006eebd)

L: independent stage-2 immutable head 408006eebdb1: --apply-fixes: coord/reports/NC/lem-zl-affine-geometric-components-finite-extension.md: a stage-2 fix is only DIR/<basename of a module>.lean (AffineGeometricComponentsFiniteExtension.lean), DIR/lem-zl-affine-geometric-components-finite-extension.lean-record.json, DIR/lem-zl-affine-geometric-components-finite-extension.statement-change.json, DIR/<new node id>.json (no new node), DIR/lem-zl-affine-geometric-components-finite-extension.report.md or a new module DIR/lean/Sheaf/<Topic>/<Name>.lean

## lem-trf-algclosed-curve-model (2026-10-19 03:59 UTC, branch head 7e15823029)

L: approved by the reader, but the landing refused it: NOT MERGED lem-trf-algclosed-curve-model: lem-trf-algclosed-curve-model: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-ramified-cartier-supported-purity (2026-10-22 01:06 UTC, branch head e0817c53dd8)

C1/F + G4. I read all 8 steps; there are no new nodes. The statement is unchanged and there is no repair note. The item and its citer lem-sfb-root-coordinate-supported-vanishing are live. Step 3 proves that P_D is an isomorphism, which is part of the statement. It does this by codim-1 absolute (Gabber) purity on arbitrary Noetherian regular affines, ILO XVI 3.1.3/3.1.1. It cites four nodes from the 2026-10-19 artin-gabber section of side-live coord/route-pivot-dropped.txt, unchanged since 10-19 21:37: lem-per-strict-local-snc-kummer-cohomology (l.1923), lem-per-divisor-purity-strict-local-criterion (l.1502), lem-per-gysin-coefficient-cone-triangles (l.1627) and lem-per-regular-immersion-class-calculus (l.1869, also in tool_uses). All four are essential. No live node can replace them. An rg search for absolute/regular-pair/Gabber/punctured purity, filtered against the drop list, finds only thm-pur-regular-immersion-purity and lem-pur-gysin-structure, which cover X smooth over a perfect k or A^1_Y over finite-type k. The lem-sbc purity nodes are pi_1 purity. Using any of them would weaken the target. The broad lem-per-gabber-regular-pair-purity is dropped as well and is cyclic (N7 review). This is the same Step-3 route as ND 65522eb4, after earlier RETURNs N7 d79cff6d and ND eef0e17d, and the report says nothing about those returns. The other steps are correct: Step 1 is the twisted arrow; Step 2 is the unique lift via j^*Q_D=0 and Hom exactness (Stacks 0A45); Step 4 checks D_e=V(g^e) as Cartier without regularity or flatness, with q an isomorphism on stalks; Step 5 is the extension E_e with frame u g^{-e} -> (1,a(u)+em), which vanishes on the complementary frame; Step 6 gives beta_e=beta∘e and uniqueness gives kappa_{D_e}=e kappa_{D'}∘q; Step 7 cancels k_{D'}; Step 8 gives the degree-2 sheaf and the edge cases e=1, D or D' empty and l^s|e. Batch-5 findings: the path through lem-asd-cartier-boundary-existence to lem-pod-etale-stalk-tensor-scalar is a generic stalk computation, so I accept it. The three trf leaves (closed-immersion-strict-localization-cartesian, adjunction-standard-simplicial-homotopy, bounded-below-derived-adjunction) are generic, but they are reached only through the dropped citations. Maintainer: a route decision is needed. Either restore a codim-1 absolute purity node, or restrict the item and its root-coordinate citer to finite-type stages smooth over k. Until then every re-delivery will loop.

## lem-sfb-ultrametric-orthogonal-extension (2026-10-22 01:11 UTC, branch head 73224163b5c)

L: independent stage-2 immutable head 73224163b5cd: A7/A6 (H2 credit): eleventh NC head 73224163b5cd of lem-sfb-ultrametric-orthogonal-extension, which NK already landed (ledger 2026-10-21 22:38/22:48; live lean.by=NK, reviewed_lean NK pass). Module sha256 a6eee1d3 identical in all 11 NC heads; node sha256 5fe09271 identical to returned tenth head 6a65a0f73fb7 (returns/NC.md:58-60, 'do not re-push'). Against side-live: node differs only in lean.by NK->NC and lean.date; module only in Authors line and one redundant minimizer docstring sentence; signature identical; nothing else differs in dag/nodes or lean/Sheaf. Mathematics re-read and correct (coefficientExtensionAbsoluteValue, NNReal ultrametric norm, Finset.sup covers n=0, sInf minimality, Fin.snoc family, span = W + span{x}, independent universes, sorry only), so nothing to repair. Do not re-push; dispatcher/maintainer must retire NC's stale claim and keep NK's credit. Maintainer note: S2 preflight still accepts already-merged items. No compile (no file changed).
