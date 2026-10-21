

## lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away (2026-10-14 17:38 UTC, branch head 7db78add3d)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away: lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## def-weil-absolute-frobenius-scheme (2026-10-15 23:04 UTC, branch head 1b3ec2f5f2)

L: the delivery could not be prepared for review: NOT MERGED def-weil-absolute-frobenius-scheme: the report lacks the heading '## Review by NI' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.

## lem-weil-pbc-constructible-abelian-bounded-exponent (2026-10-15 23:09 UTC, branch head b80df5cadc)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-pbc-constructible-abelian-bounded-exponent: lem-weil-pbc-constructible-abelian-bounded-exponent: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.


## lem-weil-karoubi-envelope-triangulated (2026-10-16 04:53 UTC, branch head a98045f329)

L (re-issued by the launcher; the entry had been lost): sf-integral-compact-support-constructible --stage 1 --reviewer NT-Codex-Q38-b6578f712 --head b6578f7125ae58fc5c5f626358e59df698f8256d --spot-checked Read all required guidance, the complete item, report, unit/chapter route, all 35 cited node statements, and cited source locations. Verified hypotheses, coefficient categories, base-change morphisms, every proof step, edge cases, duplicate/cycle risks, and recorded searches. No new nodes or repairs are needed; review.md was written. --verdict PASS


## prop-weil-pbc-integral-tstructure (2026-10-16 04:53 UTC, branch head 8933bb49c0)

L (re-issued by the launcher; the entry had been lost): NT-Codex-NI-dbb05f32e --head dbb05f32eaa6e58f595028d584ab86a8bd44d934 --spot-checked Read the complete item, cited statements, master sources, report, and unit/chapter route. All four steps, associator directions, inverse calculations, edge cases, and dependency checks pass. Accepted lem-fix-operation-reduction as the declared comparison tool. No new nodes or repairs. Condensed-category and exchange-map comparisons remain separate target obligations; review.md records the checks. --verdict PASS

## sbc-def-admissible-lattices (dedicated repair handoff)

The previous worker ended with: The literature re-review (2026-10-16) returned this split. Keep the route; fix exactly the finding below and re-deliver.

Compiler messages and attribution:
B3 (exact statement dependencies): def-weil-pbc-witness-compatibility is extraneous in stmt_deps. The definition requires only membership in the finite-level essential images, explicitly without chosen witnesses or compatible witness towers; no WIT predicate or compatible witness data of that dependency is used. Remove this edge, retaining the existing essential-image condition unchanged.



## lem-amb-cartier-kummer-map (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 7 (2396 characters); step 9 (2132 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 7 (2396 characters); step 9 (2132 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-fin-normal-open-lisse-image (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 6 (2145 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 6 (2145 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## sk-lem-proper-heart-bound (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 4 (2028 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 4 (2028 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## sk-thm-purity-transport (2026-10-21 08:19 UTC, branch head 77fb41c66d8)

First split of the imported item: 11 steps, 0 new nodes. The statement is kept verbatim behind a k=F̄_q, separated finite-type preamble; maintainer note: citer sk-def-sp-trace is over a general field and should be narrowed. Steps 1–3 (finite purity, finite-ring reduction squares, purity-bc-factors and composition-factors) and Step 9 (det-sp-unique-right-adjoint, right direction) check out. The same faults that got NN a34be139 and Q29 c11ba1dc returned are still there. (1) C3/E5, Steps 8–11: det-sp-comparison-brown-explicit (still imported) says only that the counit is 'explicit … normalized by integration'. Its identification with the transported purity trace is proof content only. So the γ defined in Step 9 as the transpose of τ is never linked to the j of Steps 1–7. Step 10's base-change and composition squares for τ 'already established in Steps 3, 5–7' are equations for j and def-pur-smooth-trace, not for τ. (2) E5, Steps 4–5 and 7: thm-pur-adic-reconstruction says no lift is unique. The step mixes the reconstruction lift, which prop-pur-adic-reconstruction-trace-coherence is about, with the lem-pur-adic-purity-scalar-naturality choice and with γ^H = R lim γ_• of det-sp-integral-adjunction-bijection. No cited statement identifies them. Base fault: the proof of prop-pur-rational-purity-trace-coherence has the same gap. (3) C4, Steps 7–8: f^! comes from sk-prop-sf-existence, sk-thm-existence(4) and the Brown comparison on module-object categories. The Q̄ℓ common-stage and raw-rational E categories are never identified with them: sk-thm-sfb-qlbar-two-colimit(4) and a rational localized-Hom node are not cited. (4) C4/E1, Step 10: det-sp-unique-adjoint-coefficients covers only A_{E,n}, O_E, E and Q̄ℓ, not arbitrary finite A→B, which the statement claims. Batch-5 flags accepted as generic: lem-pod-lisse-tensor-and-scalar-extension (stalk algebra), lem-trf-proetale-unit-leray-chain-formula (K-injective unit formula), lem-trf-oriented-closed-base-localization (closed subtopos) and lem-trf-bounded-below-derived-adjunction (D^+ adjunction). None is part of the trace-formula or Poincaré-duality proof. Process note: I ran one read-only git log by mistake, which showed the review-service repository's last commit; no repository was changed. Details in review.md.
