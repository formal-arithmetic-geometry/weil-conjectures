# Stage-1 delivery: lem-sf-clopen-composite-counit-normalization

Group Q106; 2026-10-22. Direct delivery, self-reviewed under the dispatched brief.

## Files written

- dag/nodes/sec-six-functors/lem-sf-clopen-composite-counit-normalization.json — statement, split; the unchanged statement is not a Mathlib leaf. Five proof steps, no new nodes, no new Mathlib leaves.
- citations.json — 14 entries, one verbatim statement quote for each step/node citation.
- report.md — this report. searches.jsonl is the actual search-command log; write_split.py is a sandbox helper, not a delivery node.

## Attachments

None. Searched WeilConjectures for the exact blueprint ID and for clopen/composite/unit/counit normalization. ClopenIdempotent.lean has useful underived comparisons and exact-derived models, but none of its declarations gives every clause of this item, especially the arbitrary q composite and its prescribed compositor. UpperShriekComposition and UpperStarCompCoherence concern other comparisons. No incomplete declaration was treated as a finished proof.

## WANTED

None. The blueprint sources and the needed Stacks sources are present.

## Findings and corrections

The starting item was statement-only; there was no previous sandbox split or report to reuse. Its statement, statement dependencies, source and blueprint ancestry are unchanged. No statement dispute was found.

Read the immediate source, main-20261015 prop-sf-pf-coherence.proof.md, especially compactification-independence and the following open-restriction/mate argument. Read the nearest blueprint ancestor lem-fix-weil-operations.proof.md, final paragraph, concerning projection as a composite of tensor and counit maps. The item's proof supplies the smaller clopen normalization used inside that argument, without assuming the projection formula. Read the chapter and sk-rem-sf-pf-done unit records, and kept their route and realization fields unchanged: this item is not the unit's key statement.

A potential C4 error was avoided: lem-sf-ambient-clopen-restriction-uniqueness and lem-sf-ambient-exact-clopen-comparison-localization require finite-type k-schemes and the special rings A_n; they do not cover arbitrary schemes and every finite commutative ring. Likewise lem-weil-pbc-clopen-section-direct-image concerns etale, bounded-below categories and a section, and lem-cbc-clopen-extension-zero-comparison concerns etale sheaves. Neither was cited as a pro-etale unbounded comparison. Instead the general ringed gluing and unbounded localization statements already supply exactly the needed scope.

The canonical right-adjoint compositor is not an arbitrary natural isomorphism. Step 4 explicitly transposes its defining conjugate equation to obtain the pasted-unit equation. Step 5 writes both naturality substitutions and the resulting right triangle identity. This repairs the possible hidden content of the words “normalization” or “cancellation” without creating a node that restates the item.

All five steps are under 1,200 characters. Steps 3--5 are finite formal calculations from previously established facts and the cited Hom formulas. No long step hides an independently needed comparison lemma.

## Mathlib and duplicate searches

Ran the prescribed msearch wrapper, with the actual queries recorded in searches.jsonl and copied into the item's mathlib_searches. LeanFinder with two phrasings, LeanSearch, Loogle and grep all returned successfully. LeanFinder's clopen search returned Zariski structure-module restriction maps, not the pro-etale constant-module derived comparison. The second phrasing returned the generic right-triangle and composite-unit/counit API. Loogle returned comp_counit_app and its related formulas. Grep confirmed those generic facts. Read pinned Mathlib CategoryTheory/Adjunction/Basic.lean:109--118,160--182,566--584 and Unique.lean:102--140. The generic ingredients are already represented by existing nodes, rather than new Mathlib leaves. The existing searches imported with the item were retained as provenance; the appended searches are the ones run by Q106.

Searched the whole DAG for clopen, open and closed, composite adjunction, composite counit, right adjoint uniqueness, and the relevant IDs. Ran blueprint_refs.py ancestor on the item and blueprint-wide searches for clopen, extension by zero, composite adjunction, module gluing and counit normalization. No blueprint node states this entire normalization result. The item's existing same_as: [] is retained. General clopen gluing/localization and counit-compatible uniqueness are reused; no new node is needed.

## Not duplicates

No new nodes. The existing general statements cited here are dependencies rather than duplicates of the item. Narrower ambient comparison, etale section and exceptional-adjoint clopen nodes were read and distinguished above.

## Review by Q106

I checked B--E of delivery-errors.md with the item, each cited statement and its source open. No new statement needs a separate source or search record because no new node is created. The only edited node is the assigned item, and all writes stay inside its sandbox. I read Stacks sites.tex Tag 04TS, label lemma-mapping-property-glue, which gives the covering gluing equivalence; the module-valued, finite disjoint-cover formulation used here is precisely the existing lem-pur-clopen-ringed-module-gluing statement. I read derived.tex Tag 015F, label lemma-right-derived-exact-functor, including the unbounded clause and the fact every complex computes the derived functor. Tag 05RU is the unbounded derived localization definition. I read categories.tex Tag 0037, label definition-adjoint and the following formulas, and Tag 0DV0, label lemma-compose-counits, which give the unit/counit calculus. I corrected an initial source-label spelling from lemma-compose-adjoints to the actual lemma-compose-counits. The proof is honestly marked agent-written: the blueprint does not spell out this normalization, and the cited sources support its explicit expansion.

For step 1 I checked the four cited statements. The gluing statement covers an arbitrary scheme and arbitrary ring sheaf, so Lambda_X and the two clopen pieces satisfy its hypotheses even when one piece is empty. It gives the exact product equivalence and the sectionwise formula. The localized-site extension theorem gives exact extension and its Hom adjunction. Under product coordinates, the product Hom formula identifies zero insertion with that left adjoint; I wrote the representing-maps/injectivity argument rather than assuming it. The operations definition states the ordinary direct-image formula, so s_* really is zero insertion. No etale-to-pro-etale transfer is silently used.

For step 2 the localization statement explicitly supplies the unbounded derived product equivalence, degreewise functors, and localized units/counits, not merely isomorphisms on cohomology. The exact-derived-adjunction definition identifies the localized open maps; the open normalization node supplies the identity-on-open unit. The product Hom formula constructs P_s adjoint to J_s with counit u_s inverse. Both this right adjoint and the stipulated S_s are right adjoints of exactly P_s, so det-sp-unique-right-adjoint applies with its correct orientation J_s to S_s. Its statement identifies the comparison as the transpose of the J_s-counit; hence the comparison is exactly t_s and is invertible. I did not infer equality of derived morphisms from stalks or from evaluations.

For step 3 I checked the transpose formula in lem-weil-pbc-adjunction-of-natural-bijection, then typed the composite P_sF -> P_sJ_sP_sF -> P_sS_sP_sF -> P_sF. The defining equation for t_s cancels the open unit from the clopen projector. Both transposes are identities, proving the claimed unit equality. Invertibility of a follows by applying a functor to an inverse pair and composing with the assumed compositor.

For step 4 I checked that def-weil-pbc-composite-adjunction states the pasted unit in the right order. The conjugate node gives the mate bijection and inverse-isomorphism rule; combined with the explicit Hom transpose formula it gives epsilon_r P_r(c) = epsilon_composite after the stipulated pullback comparison. Thus both transposes in step 4 are the identity by the left triangle, and injectivity supplies the unit equation. This calculation needs no separate geometric theorem.

For step 5 I checked the domains of naturality of t_s at epsilon_r,M and of c at that same arrow. The first replaces J_s by S_s, step 3 replaces t_s pi_s by eta_s, step 4 identifies the composite unit with eta_r, and the right triangle finishes. These are the specified derived natural transformations throughout. Every non-elementary geometric/localization ingredient has its own existing node in uses; elementary formal calculations are written out, with their Hom-formula citation. proof_deps is exactly the union of uses, and every cited statement has a verbatim quotation in citations.json.

I tested the identity immersion, an empty U, an empty complement, the zero coefficient ring, M=0, arbitrary unbounded M, and arbitrary nonproper q. Identity s reduces to the ordinary right triangle for q; empty U and zero coefficients give zero categories; none of the calculations imposes a hidden properness, boundedness, constructibility or Tor condition. In particular the clopen inverse-image unit is a projection, not generally an isomorphism; only t_s and a are claimed invertible. There are no new-node restatements or elementary new nodes, no borrowed proof-only objects, and no new source or target definition changes. Off-unit general gluing, localization, localized open adjunction, and open normalization are declared in split_report.tool_uses as tools, not a replacement of the unit route.

## Unfinished work

No mathematical gap remains in this one-level split. Existing statement-only dependencies remain for their own workers as required by stage 1.

## Validation

The required server deliver.py --no-push exited 0 and printed OK (not pushed), preflight passed, at 0a83978610e. The earlier citation check rejected the direct-image quote because it was shorter than 40 characters; I expanded it to the complete displayed inverse/direct-image formula copied verbatim from the same cited statement. No proof change was needed. The final report is revalidated before the push.
