# Worker report: lem-amb-linear-trace-invariance

## Files written

- `dag/nodes/sec-smooth-purity/lem-amb-linear-trace-invariance.json`: repaired item, split into eight proof steps.
- `dag/nodes/sec-smooth-purity/lem-amb-compact-action-base-change.json`: new statement-only unsplit node for compact-support automorphism action and base-change coherence; Mathlib searches found no matching declaration.
- `citations.json`: one verbatim statement quote for every cited node at every proof step.

## Attachments

No Lean declaration attachment was found. I searched the source checkout under `WeilConjectures/` for the item tag and for linear-trace, compact-support, and affine-space trace names; no finished declaration states this item.

## WANTED:

None. The proof is written from the current blueprint proof text and existing DAG statements; no unavailable literature document is needed.

## What was repaired

The item statement, its `lean` record, hypotheses, and conclusion are unchanged. The returned version had a 2367-character non-elementary second proof step. I replaced that step by two steps: a 1072-character geometric-hypothesis check for bounded-below compact-support exchange, and a 1084-character application of the new compact-support action/base-change statement. The remaining steps and route are retained, with internal references renumbered from old steps 3/5/2 to new steps 4/6/3. The new node is strictly smaller than the item: it packages only the exchange action and its identity and base-change coherence, and has no proof claimed at stage 1.

I searched the whole DAG and blueprint for this auxiliary statement before creating it. No existing node or blueprint node states the compact-support automorphism action with its Cartesian-model and base-change coherence. The recorded Mathlib searches for the new node (LeanSearch, LeanFinder, Loogle and grep) returned only ordinary sheaf pushforward or algebraic base-change declarations, so it is marked `unsplit` with `mathlib_match: null`.

## Not duplicates

`lem-amb-compact-action-base-change` vs `thm-cbc-finite-torsion`: the existing theorem gives an exchange isomorphism for an arbitrary compact-support Cartesian square; the new node additionally constructs the automorphism action from a coefficient isomorphism, proves its identity case, and proves compatibility of that action with base change.

`lem-amb-compact-action-base-change` vs `lem-amb-affine-space-top-trace`: the existing trace node gives the affine-space counit trace and its base-change formula; the new node concerns the independent compact-support exchange action of an automorphism and does not assert a trace or its invariance.

## Review by Q124

I read the current `main-20261015` blueprint proof for `lem-amb-linear-trace-invariance`, the imported item node, the `sk-prop-an` unit record, and every source node cited by the repaired proof. The item statement agrees clause by clause with the blueprint node: finite commutative A killed by N, Noetherian S with N invertible, ordinary etale derived categories and finite Tate twists, the projection p_d, the specified coordinate-tower counit trace, the pullback action defined by finite-torsion compact-support exchange, and the equality t_p composed with rho_g equals t_p, including d=0. No Lean declaration in either source search states the item with a finished proof.

Step 1 is the universal-matrix construction. I checked `def-sbc-affine-space`, `def-weil-affine-spectrum`, `def-pc-scheme`, `def-weil-finite-type-morphism`, and `lem-weil-pbc-finite-type-over-noetherian`: they provide the relative affine scheme, affine charts, finite-type notion, and Noetherian conclusion used in the displayed construction. The inverse matrix formula, sections s_g and e, and the d=0 case are elementary consequences of those definitions.

The former long step 2 is now steps 2 and 3. Step 2 checks exactly the hypotheses taken from the cited nodes: bounded-below input, finite-type affine/projective charts, Noetherianity, separatedness from the coordinate diagonal, the standard quasi-compact open A^d_T in P^d_T, proper projective projection, and therefore applicability of `thm-cbc-finite-torsion`. I read both Nagata statements and verified that they say the standard open immersion and properness of projective space. Step 3 cites the new node `lem-amb-compact-action-base-change` for precisely the automorphism action, its identity value, and the equation C_u composed with u^* rho_a equals rho_aT composed with C_u; it also cites `lem-asd-etale-finite-twist-pullback` for the canonical coefficient comparison. The new statement explicitly supplies the Cartesian comparison, compactification independence, and pullback coherence used here, so no proof-only material from that node is assumed.

Step 4 uses `lem-amb-affine-space-top-trace` for trace isomorphism and base change, `lem-weil-pbc-derived-single-fully-faithful` only for degree-zero module-sheaf maps, and both constant-sheaf section nodes for the scalar section and its locally constant representative. I verified that the cited full-faithfulness node states the degree-zero Hom bijection, while the constant-ring node supplies local constant representatives. The multiplication-by-b argument and conjugation identities are elementary after those statements.

Step 5 proves connectedness of every residue-field fibre directly from the domain k[x_ij][1/det]; the determinant is nonzero by evaluation at the identity, and the generic-prime argument shows every nonempty open contains (0). The finite-type-over-a-field Noetherian assertion uses the cited Noetherian node. I checked the edge cases d=0 and the empty scheme separately: the fibre ring is k in dimension zero, and the later scalar assertion on an empty base is unique.

Step 6 uses `lem-weil-pbc-connected-locally-constant-map`, whose statement is exactly that a locally constant map on a nonempty connected space is constant. The identity point evaluates the pulled-back action to rho_1=1, so the scalar is one on every fibre. Step 7 uses `def-pc-fibre-product` for the residue-field lift to a fibre, the additive constant-sheaf section bijection for b=1, and degree-zero full faithfulness to return from alpha_0=1 to the derived morphism. The cited statements provide each of those facts; the empty-base clause is immediate. Step 8 uses the new node's base-change equation from step 3 and `lem-amb-affine-space-top-trace` for trace base change, then cancels the stated isomorphism C_sg. The d=0 case is the identity adjunction.

Every non-elementary step is now below 2000 characters (769, 1072, 1084, 1396, and 646 characters); the two remaining short steps are marked elementary and use only explicitly cited fibre-product/section facts and cancellations. `proof_deps` is exactly the union of step uses. `citations.json` quotes the complete statement of each cited node verbatim, so every quote contains the sentence or formula used by its step. No new node duplicates an existing DAG or blueprint statement, and the new node has all required Mathlib search records with their actual queries and results.

The only outstanding work is normal maintainer review and landing of the split; no proof or compiler action is part of this stage-1 repair.
