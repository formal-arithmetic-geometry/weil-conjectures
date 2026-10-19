# Worker report — Q154

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-integral-twist-derived-scalar.json`: statement; split into eight proof steps; not a Mathlib leaf. No new nodes, no Mathlib leaves.
- `citations.json`: one exact statement quotation for each of the 28 step/node citations. Whole statements are quoted where their hypotheses matter.

## Attachments

None. I searched the read-only slopmaster2 project for the exact item tag and for integral twists, derived scalars, and twist/base-change terminology. There is no declaration for this item. `AlgebraicGeometry.Picard...pullFunctor_obj_twist` concerns twisted descent data, and the finite-coefficient Tate-object declarations and `nonempty_rightDerivedLowerShriek_comp_iso` do not assert the completed integral coefficient comparison here. No reference-source sorry declaration was treated as a proof.

## WANTED

None.

## Audit and changes

The item statement is unchanged. Its proof was empty. I supplied the balanced inverse of its displayed chain map, verified the K-flat representatives on both sides, checked naturality through the K-flat localization, and wrote the completed comparison as
`beta_C = (chi_C)(m) o alpha_C o inverse(chi_{C(m)})`.
I removed two statement dependencies used only in the proof (K-flat change of rings and closed sheaf tensor), retaining them as proof dependencies. No hypotheses or coefficient categories were changed. The ordinary tensor is over the completed ring sheaf, never the discrete constant integral ring.

I read the fixed chapter record, the `sk-prop-sf-existence` unit record, SETUP's three levels and tool-use rule, GOAL, and dag-sync. This is a tensor/coefficient tool below the exceptional-adjoint unit; it replaces no geometric unit step. I retained the item's historical blueprint ancestor `prop-weil-twist-preserves` and its precise final-sentence place. The current parent's steps 10–11 identify the line base change and the comparison this item supplies. The parent depends on the item, so citing the parent would be circular; I instead used the existing lower-level line-completion interface. Searches of the complete DAG and `blueprint_refs.py search` found no exact blueprint duplicate for this item.

The earlier Q53 Mathlib search records were preserved. The seven new searches in `searches.jsonl` were run with `msearch.py`, and their query strings and results were recorded. I tried a second semantic phrasing and corrected the invalid multiple-name Loogle query with `TensorProduct.AlgebraTensorModule.distribBaseChange`. The relevant hit, read at `Mathlib/LinearAlgebra/TensorProduct/Tower.lean:441` and its pure-tensor formulas, is ordinary algebraic tensor base change. It neither gives the sheaf-derived descent nor the prescribed natural comparison with completed integral scalar extension. Other hits give generic exactness, complex tensor hypotheses, or free-sheaf maps. No declaration states the item in one specialization. There were no unavailable searches in this run; the invalid Loogle query is recorded as invalid, not as evidence of absence.

## Not duplicates

No new nodes were created. In particular I reused the existing sheaf-tensor universal properties, K-flat change-of-rings, integral line tensor comparison, and constructible scalar-extension nodes rather than creating special cases of them.

## Review by Q154

I read the item's source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/prop-weil-twist-preserves.md`, especially its final integral/common-stage sentence, together with the current DAG parent's complete proof. I checked Stacks `sites-modules.tex`, Tag 03EK (`section-tensor-product`), including the exact scalar-change tensor formula and the sheaf bilinear universal property; Tag 03EL (`lemma-tensor-product-pullback`); and the internal-Hom definition in 04TT. I read the K-flat definition/construction and resolution in `sites-cohomology.tex` (06YN, 06YS, 06YU), the tensor-K-flat associativity argument, and derived pullback 06YY. I read Bhatt–Scholze Definitions 3.4.10 and 3.5.2, Lemma 3.4.12(4), and Proposition 3.5.1 in the available PDF. No SGA source is used. There are no new-node sources to audit.

For step 1 I opened `lem-weil-integral-twist-base-change`: its statement gives exactly theta for every integer m and not merely for the first twist. I opened `lem-pur-twist-sheaf-locally-free`: clauses 3–4 give the integral first line and its finite reductions. `def-coefficient-twists-detailed` specifies powers, the zero twist and duals; `lem-sfb-localized-site-tensor-restriction` preserves pure tensors on the slice, and `def-pur-sheaf-hom` defines its Hom on that slice. The evaluation/local-gluing argument establishes all remaining integer-line assertions directly. It does not invoke the parent twist-preservation theorem.

For step 2, `lem-pc-sheaf-modules-tensor-closed` states the actual symmetric monoidal structure and closed adjunction; the inverse evaluations from step 1 give inverse tensor equivalences. The short kernel/cokernel universal-property argument establishes exactness rather than obtaining it from a definition. `def-pc-flat-sheaf-modules` then identifies the proven exact tensor functor with flatness. `lem-weil-pbc-exact-functor-complex-cohomology` explicitly states the natural cohomology formula used here.

For step 3, `lem-pc-kflat-resolution` gives both K-flatness and flat terms with no boundedness hypothesis. `def-pc-kflat-complex` tests every acyclic module complex; the proof performs that test. `def-pc-tensor-complex-sheaves` gives the direct-sum total tensor and differential signs, and the closed adjunction supplies the direct-sum rebracketing. This proves, rather than assumes, that tensoring P with the degree-zero line is still K-flat with flat terms.

For step 4, the two cited bilinear/sheafification universal-property statements really extend restriction-compatible balanced formulas and determine the maps uniquely. I checked the inverse on both iterated pure inputs, the B-balancing relation, and the chain differential. Theta is supplied by the exact all-integer line base-change node. This is an explicit argument for the chain clause, not a new lemma restating that clause.

For step 5, I opened `lem-pur-derived-change-of-rings`, which states the derived computation and resolution independence, and `lem-pur-kflat-change-of-rings`, whose hypotheses require the flat terms already checked. `lem-weil-pbc-site-derived-tensor-descent` states both the computation on two flat-term K-flat complexes and the localization equivalence. That is enough to extend the displayed chain-map naturality to roofs and inverse quasi-isomorphisms. I fixed the site universe large enough for module sheaves, as required by that statement and the pro-etale site convention; no large-index colimit is taken.

For step 6, `lem-sf-integral-line-tensor-comparison` applies to any scheme with ell invertible, any complete C and any locally free rank-one completed-coefficient line. These are exactly the hypotheses verified, without a qcqs assumption. Crucially its statement specifies the canonical map into the strict reduction-tower cone and its finite reductions. The map is consequently the first map required by `def-weil-derived-complete`, not a freely chosen map into an arbitrary derived limit. K-flat change of rings verifies the quotient computations. I checked by dependency traversal that this cited line-comparison node does not depend on the item.

For step 7 I checked both definitions of constructibility and integral uniform bounds. The pullback-tensor statement applies to the locally closed stratum immersions, so the tensor used on a stratum is the restriction of the actual global tensor. Refining covers gives the same finite constant module models; there is no assumption that the global trivializing cover is finite. The cohomology formula preserves one fixed interval at every level. Completeness comes from step 6, so every clause of the integral category definition is met.

For step 8, the finite-free completed-scalar comparison explicitly assumes completeness, which is now verified for both C and C(m), and states that chi is natural with exactly the strict-tower scalar-extension target in the definition. `lem-weil-integral-scalar-extension-constructible` asserts membership for every integral constructible input, with no finite-Tor assumption. Thus both completed outputs lie in the required full subcategory. I checked the direction and types of all three factors of beta and its inverse.

Small cases: m=0 gives the tensor unitor; negative m uses a genuine dual basis and does not confuse an element of a dual with an element of the original line. E=F gives multiplication and the natural completeness comparison. C=0 and the empty scheme give zero complexes without invoking nonempty support. A ramified extension is allowed: the proof uses K-flat change of rings and the finite-free completed comparison, never flatness of a same-index finite quotient. Neither the proof nor a new node imposes an additional boundedness or Tor condition. No statement dispute was found.

I checked delivery-errors B–E against the open sources and cited statements. There are no new statements that could be elementary, duplicate, relabelled clauses, or unsearched Mathlib facts. All eight proof steps have citations to their non-elementary inputs; citations.json uses verbatim statement text. No non-elementary step exceeds 2000 characters. I declared off-unit citations as generic tools in split_report, not as maintainer-owned tool_uses. The server `review_split` check passed with zero new nodes, and the separate server `check_dag` invocation exited successfully. No compiler or Lake command was run.

## Unfinished work

None within this one-level split; existing unsplit dependencies remain the independent queue items they were. The required full delivery dry run and push follow this report.
