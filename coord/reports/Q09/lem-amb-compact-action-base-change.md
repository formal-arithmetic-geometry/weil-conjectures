## Files written

- `dag/nodes/sec-smooth-purity/lem-amb-compact-action-base-change.json`: statement node, split; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim citations for every proof-step dependency.

## Attachments

None. I searched the read-only slopmaster2 source for the item id, blueprint tag, and the compact-support action terminology; no sorry-free declaration states this item exactly.

## WANTED

None.

## What was checked and corrected

The imported item was unsplit and had no proof. I retained its statement and hypotheses, including the finite coefficient ring, separated finite-type Noetherian morphism, supplied quasi-compact compactification, bounded-below ordinary etale derived object, the Cartesian comparison `(a,f)`, the identity clause, and the arbitrary Noetherian base change clause. I added a five-step proof and set `proof_deps` to its cited nodes. No definition or sublemma was duplicated: the finite-coefficient compact-support exchange theorem already supplies the needed exchange isomorphism, naturality, identity, pasting, and compactification-independence properties.

## Review by Q09

I read the item source, `lem-amb-linear-trace-invariance.proof.md`, at proof paragraphs 1 and 2, and the statements of every cited node. Step 1 uses the fibre-product universal property from `def-pc-fibre-product` to verify that `(a,f)` is the Cartesian comparison, then invokes the compact-support-square definition to identify the required base-changed compactification. Step 2 uses `thm-cbc-finite-torsion` for the exchange isomorphism, its naturality, and compactification-independent meaning, and uses `def-amb-etale-compact-support` for functoriality on the coefficient isomorphism. Step 3 checks the identity clause from the same exchange theorem and the identity action of the compact-support functor. Step 4 reads the base-changed square and compactification from `def-cbc-compact-support-square`, then uses the theorem's naturality and horizontal/vertical pasting to derive the displayed base-change equation; the inverse-image composition comparison is explicitly retained. Step 5 uses the theorem's canonical refinement comparisons and the compact-support definition's compactification-independent notation to justify arbitrary chosen compactifications on `X_T`. I checked that all hypotheses required by the cited theorem are present: finite commutative coefficients, separated finite type, a supplied quasi-compact compactification, and bounded-below `K`; the theorem imposes no condition on `u`. I tested the edge cases `a=1_X`, `theta=1_K`, and an identity base change, where each equation reduces to the identity by the cited clauses. The only correction was to replace the empty imported proof with these explicit steps and citations; no source statement was changed.

## Resumption corrections

The previous attempt had completed the split and searches before its transport failure. I retained that work, compared its statement against the current repository (unchanged), and reused the recorded Mathlib results. I placed the deliverable under the required dag/nodes/sec-smooth-purity path. The first dry run was started before these repairs, as instructed.

In step 4 the old first equation was ill-typed: C_u(K) cannot follow u^*E_a(K), whose target has coefficient a^*K. I replaced it by D composed with u^*E_a(K), where D is C_u(a^*K) followed by the explicitly named inverse-image comparison. The displayed three-equality calculation now proves the claimed intertwining relation. This is a proof repair, not a statement dispute. I also fixed doubled backslashes in proof TeX and marked the expanded blueprint-only proof as agent-written.

For step 4 I additionally read lem-pod-separated-finite-type-base-change and lem-weil-pbc-finite-type-over-noetherian: their statements supply exactly stability under arbitrary base change and Noetherianity of a finite-type source over the Noetherian T. They are generic tools, declared in split_report.tool_uses. Step 5 now cites only thm-cbc-finite-torsion, which actually asserts the canonical comparison coherence; def-amb-etale-compact-support explicitly defers that property and is not evidence for it. All citation quotes were recopied verbatim from the current statements. No new node, partial attachment, unverified Mathlib match, or changed hypothesis was introduced. The item is not the key statement of its unit, so no unit record is edited.
