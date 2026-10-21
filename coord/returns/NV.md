

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





## lem-sf-immersion-completed-pullback-comparison (2026-10-21 07:40 UTC, branch head 3eb1dc03e64)

Faults C5, D1/D2 and the 2026-10-21 re-split note. The statement is unchanged and the assembly is 1963 characters. The mathematics is sound and complete against old Steps 1-6: sign map (x,y)->(-y,x), mate beta = Roos product isomorphism via the augmentation clause with gamma = counit, alpha = beta F_D(eta_K), FK completeness, integral Step 3 with [r,s]. The fault is in the division of the work: both new nodes restate existing DAG nodes. (1) lem-sf-actual-immersion-roos-normalization: its middle paragraph is lem-cbc-exact-product-functor-strict-limit (split, pass, 2026-10-17): lambda = theta^-1 kappa F_D theta, evaluation compatibility, F_D(a_gamma) -> a_{F gamma}; its hypotheses hold through immersion-limit-preservation and countable-products-exact. Its K-flat tower clause is lem-weil-pbc-reduction-pullback-derived-tower, which the report itself named as a duplicate of a rejected node. The only new content is old Step 5's factorization alpha_K = beta F_D(eta_K) and the Lu* = F_D counit normalization. (2) lem-sf-integral-adic-presentation-normalization: its Roos-complete => specified unit invertible / intrinsically complete is lem-pur-roos-intrinsic-completeness-equivalence (i)=>(iv),(v), which is in the snapshot. Its R^ULift/e_T/E_T transport is def-pur-completed-coefficient-presentation-transport. The datum checks are only citations. (3) Under the re-split note, the roos node bundles old Steps 2, 4 and 5 into one 3600-character chunk instead of separate arguments. Repair: item Steps 1-2 cite those four existing nodes directly, and new nodes are created only for the factorization, the counit normalization and, if needed, the Koszul sign identification. That restructuring is more than a small FIX. Nothing is in the route-pivot dropped list. No SGA is used. Note: in the snapshot only the sec-smooth-purity symlink resolves; I read reduction-pullback-derived-tower from clones/side-live.
