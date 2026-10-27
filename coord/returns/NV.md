

## lem-pur-co-smooth-etale-locality (2026-10-15 23:16 UTC, branch head e369579c3e)

L: approved by the reader, but the landing refused it: NOT MERGED lem-pur-co-smooth-etale-locality: coord/.merge.lock held for 120 s by pid 3168532: /usr/bin/python3 tools/merge_delivery.py NC lem-kun-stalk-faithful-derived --stage 1 --reviewer NT-Codex-NC-376d23af5 --head 376d23af57cb5d5b5b131991c9e26642789df863 --spot-checked Read all five steps, the new cone leaf, cited statements and sources. Verified Stacks 05QR/015F/03Q1/04JN/04JQ/03PT/03PU and the exact Mathlib declarations. Unbounded ordinary étale coefficients, hypotheses, edge cases, duplicates and dependency cycles checked. No repairs needed; accepted generic tool uses documented in rev Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-pur-smb-extraordinary (2026-10-16 04:53 UTC, branch head a5f1e764ce)

L (re-issued by the launcher; the entry had been lost): .lock held for 120 s by pid 1872115: /usr/bin/python3 tools/merge_delivery.py N6 lem-amb-p1-diagonal-integrals --stage 1 --reviewer NT-Codex-N6-02637d96f --head 02637d96f89402c7f22bc8648601962ae70decb4 --spot-checked Reviewed the item, all seven proof steps, cited node statements, blueprint/unit route, source locations, Mathlib searches, and edge cases. The finite ordinary-etale coefficient repair and corrected exchange/stalk arguments are sound; review.md records the full audit. --verdict PASS




## lem-weil-pbc-proper-smooth-curves-prime-coefficients (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2185 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2185 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-weil-finite-duality-site-comparison (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2364 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2364 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-per-algebraic-dualizing-torsion-hull (2026-10-19 01:49 UTC, branch head eefb6754e45)

Route-pivot RETURN (2026-10-19 dropped section of clones/side/coord/route-pivot-dropped.txt, decision recorded in coord/repair-notes/lem-per-artin-gabber-affine-curve.json). The item lem-per-algebraic-dualizing-torsion-hull is itself dropped (line 1411), and so is the cited def-per-algebraic-normalized-dualizing (line 1368). Its only citer, lem-per-algebraic-local-duality (line 1414), is dropped, and so are that node's citers: local-cohomology-top-nonvanishing (1680), algebraic-completion-rhom (1405) and algebraic-torsion-completion-hom (1416). No target reaches this chain. Finding 1, the item citing def-per-algebraic-normalized-dualizing: no step justifies it, and the dependency is the statement's own hypothesis, so it cannot be removed. Finding 2, the new lem-per-finite-length-dualizing-hom citing the same def: same reason; the node exists only for the dropped item. The mathematics is otherwise sound and I read it in full. The statement is Stacks Tag 0A82, with RΓ_m equal to RΓ_Z for Noetherian A. Step 1 cites Tag 08Y3 (injective hulls exist over any ring), which removes the earlier circular cite. Step 2 shows A/m^n has finite length. Step 3 uses Tag 0954 (any ring, finitely generated ideal) and Tag 0A7Q (functorial finite-length duality) to get H^q = 0 for q ≠ 0. Step 4 uses evaluation at 1 and Tag 08Z4 (E = ∪E[m^n]). Steps 5–6 are the elementary transfer and the good-truncation zigzag. The four new nodes are faithful general Stacks lemmas, not restatements. No forbidden ingredient appears (no Qbar_l, adic or middle t-structure route, no Gabber or alterations). Precedents: Q159, Q110, Q26, Q86, Q35. Maintainer: withdraw the lem-per-algebraic-* local-duality items from dispatch.

## lem-pur-transport-qbar-common-stage-counit (2026-10-23 18:08 UTC, branch head 948910c75ed)

I read the item in full: its unchanged statement and its nine steps (there are no new nodes). I read every cited statement and the source sk-thm-purity-transport.proof.md Step 3 (lines 31-42, 'the transport is well defined because the purity isomorphisms are transitive in coefficient extensions'). The same gap that got the nine earlier deliveries (Q160 25b6, Q32 008a, NW 3f2a/63f9, Q128 b836, Q72 da12, NF 6d05, Q126 a02d, NH ab74) returned is still open. E4/E1+C4 (Step 2): the assumed compatibility is written with the b_{L/F}, a_{L/F} of sk-lem-sp-field-extension, which live on the raw scalar localizations D^b_c(T,E) of def-weil-rationalization-karoubi. The step applies them to Phi_F on the condensed D_ctf of sk-def-sfb-constructible and sk-thm-sfb-qlbar-two-colimit(4). No node identifies the two categories, or identifies the raw comparisons with the condensed gamma^!. C4/E5 (Step 3): presentation independence for models at E and at L needs b_{Q/E} = b_{Q/L} o S(b_{L/E}) under the associators. det-prop-scalar-six-compact-support has no coefficient-composition clause (only compactification independence and R(gf)_!). Pullback(3) covers f^* and a_! only, not Rp_*. E5/C4 (Step 9): 'with target Q it holds by the same transitivity and Step 2' asserts transitivity on mixed chains E->F->Q, but sk-lem-sp-field-extension gives finite chains only, and only on the raw side. det-sp-unique-adjoint-coefficients only transfers a composition identity from c_f to c_J, and its categories are def-sf-categories. Steps 4-8 are correctly typed algebra (counit formula, unique gamma, conjugation, mate formula) once Phi is well defined. I searched with rg -L for a bridge. lem-sf-constructible-exceptional-coefficient-coherence and lem-sf-rational-left-coefficient-localization are in the def-sf raw/pair framework and are not condensed; the lem-pur-compact-support-scalar-* nodes are integral E<F only. No bridging node exists, so this is a major missing lemma, not a FIX. No SGA citations, no fixes written.

## lem-sfb-stack-higher-images-flat-comparison (2026-10-24 17:47 UTC, branch head 3efddc4318b)

L: independent stage-2 immutable head 3efddc4318be: --apply-fixes: dag/nodes/sec-six-functors-basics/def-sfb-stack-big-etale-module-functors.json: a stage-2 fix is only DIR/<basename of a module>.lean (StackBigEtaleModuleFunctors.lean, StackFppfModuleFunctors.lean, StackHigherImagesFlatComparison.lean, StackModuleSites.lean), DIR/lem-sfb-stack-higher-images-flat-comparison.lean-record.json, DIR/lem-sfb-stack-higher-images-flat-comparison.statement-change.json, DIR/<new node id>.json (def-sfb-stack-fppf-module-functors, def-sfb-stack-module-sites), DIR/lem-sfb-stack-higher-images-flat-comparison.report.md or a new module DIR/lean/Sheaf/<Topic>/<Name>.lean

## lem-sfb-normal-semiabelian-biextension-extension (2026-10-24 17:47 UTC, branch head d3fd567637b)

L: independent stage-2 immutable head d3fd567637bd: the new node def-sfb-line-biextension exists on sheaf-dag now (another delivery created it): return the delivery

## lem-trf-binomial-root-correction (2026-10-24 18:41 UTC, branch head df5329aec28)

L: approved by the reader, but the landing refused it: NOT MERGED lem-trf-binomial-root-correction: lem-trf-binomial-root-correction: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

