

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

## lem-sp-normalized-error-tower-vanishing (2026-10-21 13:35 UTC, branch head 9b8687c4160)

L: independent stage-2 immutable head 9b8687c4160d: H2: the delivery added theorem stmt_deps det-sp-coefficient-towers-abelian and lem-weil-pbc-total-tensor-homotopy-cone-signs only for plain defs: spCoefficientCommRings (SmoothPurityCoefficientTowersAbelian) and TotalTensorSigns.Modules/tensor/total/ι (TotalTensorHomotopyConeSigns). Neither is a .choose and no definition node owns them. Correction: drop both from stmt_deps and either (a) add existing:true definition node(s) in sec-smooth-purity on those declarations and cite them, or (b) use Mathlib map₂CochainComplex/ιMapBifunctor via def-pc-tensor-complex-sheaves and inline a CommRing tower in the item's module; do not cite the theorems. lem-coef-derived-tower-counit-projections supplies Prop Functor.Additive instances, so it is genuine (PASS on that point). The mathematics is otherwise correct: hypotheses (semilinear q with id and cocycle law, K-flat over B_n, hnorm pinned by the x⊗b↦b q(x) formula), ε uniquely pinned by inr≫ε=reduction, generator-pinned transitions, a and assoc, a distinguished triangle in D(towers), a powered-shift quasi-isomorphism, levelwise quasi-isomorphism ρ, limit_zero, identity-cone diagonal, the exact composite IsIso, m=0 standing for the paper's m=1, unbounded complexes, independent universes. I ran no compile because I changed no file; the worker's scompile is reported clean (22.8 s / 20.3 s).

