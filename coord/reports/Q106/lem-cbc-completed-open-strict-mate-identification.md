# Q106: lem-cbc-completed-open-strict-mate-identification

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-completed-open-strict-mate-identification.json: eight-step split of the unchanged statement; no Mathlib match for the complete assertion.
- citations.json: one verbatim statement extract for each of the 23 step/node citations.
- report.md: this report. searches.jsonl retains the five searches actually run for this item; write_split.py is sandbox scratch work only.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written or compiled.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, completed/open exchange, strict-tower and mate terminology, and read the nearby pro-etale ModuleObject/Derived/OpenLowerShriekBaseChange.lean. Its ordinary/bounded-constructible open exchanges do not state the completed strict-tower identification, both displayed equalities, or the specified normalized limit comparison. They therefore do not attach this item.

## WANTED

None. The supporting literature and current blueprint are available locally. No SGA source is used.

## What needed changing

The item had a statement and searches but no proof. Its statement already distinguishes the completed coefficient sheaf from constant A, assumes the quotient/open identification and completeness of j_!K, and specifies an actual strict finite exchange. I kept those hypotheses, its statement, source, origin metadata, chapter and unit unchanged. In particular the proof never treats derived evaluation as faithful and never introduces etale-origin witnesses or a uniform lower bound.

The current blueprint's short extension/limit proof says reductions commute with open extension by exactness and describes product preservation too tersely. Neither inference follows just from exactness. This item's hypotheses already provide the quotient comparison, and the existing ringed-open-products lemma supplies the actual product comparison for the quasi-compact open. Steps 5--7 use these statements, rather than the terse inferences in the blueprint. This is a clarification of the node-level proof, with no change to the unit's route or statement.

The item belongs to the older sec-smooth-purity/sk-prop-sf-cbc DAG records. I read those chapter and unit records, the three-level rule in SETUP.md, and the current main-20261015 six-functors chapter/unit text. The proof follows the prescribed finite exchange followed by derived limit route. I did not change the records or any target. This is not the unit's key statement, so it requires no realized-field edit.

## Not duplicates

There are no new nodes and hence no new/existing node pairs. Searches of dag/nodes and blueprint_refs.py searches for "strict mate" and "completed open" found no replacement blueprint statement. The ancestor command gives thm-cbc-complete-proetale, as recorded in the item. I reused the existing strict finite exchange, finite scalar compatibility, constant-tower calculus, open tensor normalization, and normalized exact-product/strict-limit nodes. In particular I did not create separate nodes for either equality of the item, conjugating an inverse, applying a functor to an equality, or scalar restriction of the explicit open-unit formula.

## Mathlib searches

I ran msearch.py with leanfinder, loogle, grep and leansearch, then a second leanfinder phrasing of the open unit transpose. All services answered. LeanSearch returned zero-map and generic derived-category facts; Loogle returned Adjunction.homEquiv and its unit/counit formulas; the first LeanFinder returned ModuleCat.restrictScalarsComp and extendScalarsComp facts; the second returned SheafOfModules.pullbackObjUnitToUnit and ordinary adjunction identities. The recorded CategoryTheory grep returned zero hits. These are not the completed strict-tower assertion or a one-line specialization of it. I read the relevant Adjunction/Basic.lean, ModuleCat/ChangeOfRings.lean and Sheaf/PullbackFree.lean source portions. The unit object in PullbackFree is the rank-one module sheaf, not the open-extension adjunction unit. The item retains its inherited searches and appends precisely the five logged queries from this session.

## Review by Q106

I read coord/delivery-errors.md B--E in full, the item, its cited-node statements, Stacks sites-modules.tex Tag 03DI (lemma-extension-by-zero), and the current blueprint files lem-cbc-completed-extension-zero-comparison.proof.md, def-cbc-completed-exchange-map.md and thm-cbc-complete-proetale.proof.md. Tag 03DI gives the direct-sum presheaf and the explicit adjunction transpose. It does not assert the strict derived or completed normalization; those refinements are agent-written and marked so in proof_origin. No new node needs its own literature source.

For Step 1 I checked that the strict finite-exchange node really states simultaneous strict maps, completed-ring linearity, quotient-transition compatibility, the inverse unit transpose and naturality for arbitrary K. Its hypotheses are precisely the adic datum and cartesian open square present here. The assumed open quotient comparison identifies the source with Q; this is not an additional conclusion silently taken from the node.

For Step 2 I checked the statement of constant-completion-equivalence: its comparisons commute with transitions and are canonical finite tensor comparisons, natural in the coefficient object and pullback. The restriction-of-scalars definition keeps abelian sheaves unchanged. The two presheaf/sheafification definitions really give the same direct sum and its abelian sheafification after restriction. Open-tensor-normalization states that the unit is the same section on the open, including arbitrary diagram coefficient rings. On a flat representative, reassociating tensor factors leaves a local pure tensor unchanged; the unit leaves its section unchanged. This supplies the unit compatibility needed for a and b, rather than assuming scalar restriction automatically respects an unrelated adjunction.

For Step 3 I read the open clause of strict-tower-proper-open-calculus, which specifies beta inverse as the transpose of the pulled-back open unit, for arbitrary constant B including infinite A. Open-tensor-normalization explicitly extends to strict ringed diagram topoi with arbitrary coefficient transitions. Finite-open-exchange-scalars states compatibility of the units, counits, and transitions, not merely invertibility of finite exchanges. Using the stated mate formula, both inverse maps are J(t) followed by the same counit. Thus equality is established on strict representatives. It is not an argument from evaluation in derived categories. Step 4 uses the actual uniqueness/composition clauses of localization-universal-property to descend that equality; inversion and cancellation then give exactly b r(omega) = beta a.

For Step 5 I checked each hypothesis of exact-product-functor-strict-limit. Quasi-compact-base-change applies to the specified cartesian square, so j prime is quasi-compact. Ringed-open-extension-products covers this open, any coefficient ring sheaf, and the canonical projection comparison. The localized ringed adjunction supplies exactness. Pro-etale-countable-products-exact covers both module categories with constant A. Thus lambda is the lemma's normalized comparison, not just some isomorphism of the two endpoints.

For Step 6 I checked that completed-pullback defines its value by the derived limit of the actual pulled-back strict tower, that constant-completion-equivalence identifies these limits and their completion units, and that exact-product-functor-strict-limit equates its Roos normalization to the ordinary-limit/resolution comparison. Its augmentation clause covers the quotient completion maps. These statements justify the endpoint normalizations including their units.

For Step 7 the completed-extension-zero-comparison statement specifies the map as finite exchanges followed by the extension/limit comparison. Derived-limit-functoriality allows applying L to the strict equality. Writing all three conjugating factors gives lambda inverse, then L(b), L(r omega), L(a) inverse in that order. Substitution of Step 4 yields the requested formula without swapping factors. Step 8 uses naturality already stated by the strict exchange and normalized comparison; finite evaluation is only applied after constructing omega.

I tested the argument for K=0, the empty open, identity opens and identity base change. The zero cases give zero maps, the identity cases reduce to the normalized units/identity exchange, and the order of lambda remains lambda inverse. Unbounded complexes cause no extra hypothesis: the cited diagram and strict-limit statements are explicitly unbounded. I also checked that no assertion uses an isomorphism u inverse A_T = A_T prime: only the projection-induced structural map and finite-reduction comparisons occur. No proof step exceeds 2000 characters. There is no new clause lemma or hidden induction. Generic tools from other units are declared in split_report.tool_uses, without modifying top-level tool_uses.

## Unfinished work

No part of the stage-1 mathematical split is left unfinished. Existing cited nodes remain independent DAG obligations; this delivery does not claim their Lean proofs are complete. The required server dry run and direct delivery follow this review.
