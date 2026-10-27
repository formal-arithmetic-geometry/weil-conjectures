# Worker report: lem-sf-projection-base-change-common

## Files written

- dag/nodes/sec-six-functors/lem-sf-projection-base-change-common.json: statement, split; six proof steps, no new nodes and no Mathlib leaves. The statement and its specified compactification and comparison maps are unchanged.
- citations.json: one verified verbatim statement quotation for each of the 17 step citations.

## Attachments

None. I searched the project WeilConjectures/ source for the item tag, projection/base-change notions and theorem names, and read lean/Sheaf/Paper/ProjectionFormulaCoherence.lean:619–681. The exact common-stage theorem at line 648 ends in `sorry`. The source's finite étale projectionMapOfCompactification_baseChange and pro-étale module-object results concern different coefficient categories, not this pair-category statement. I do not attach them.

## WANTED

None. I used the current blueprint and existing DAG statements, not an unavailable reference or any SGA source.

## What needed correction

The live node was an unsplit extraction of the common-coefficient clause of prop-sf-pf-coherence. Its retained docstring is construction material, not a completed proof. The integral open-square node cannot be applied directly at algebraically closed coefficients: it only covers finite and completed integral coefficients. Steps 2–4 supply this missing passage using raw localization, common-field representatives and the prescribed endpoints. Likewise the proper-factor equation is derived directly at the common stage, rather than assuming the whole projection/base-change theorem as a coefficient law.

No statement dispute or change was needed. In particular, neither g nor the structure morphisms acquire a separatedness hypothesis; arbitrary K and L are retained. The proof never reduces a rational object and never infers equality of completed arrows from separate finite reductions. It does not use fix-lem-exchanges, whose statement assumes separated horizontal arrows, and it does not rely on the rational sibling with a mismatched family of stage data.

## Earlier work and provenance

The prescribed abandoned-directory listing returned no matching directory for this item in any group. The active sandbox contained only dispatcher briefs; it had no item node, report or search log. I copied the live unsplit node, retaining the source notes, candidate theorem and NB's pre-existing Mathlib search entries. Those entries are inherited evidence attributed to NB through the node's original created record; they are not presented as searches I ran. Five additional NV searches were actually run with msearch.py and are recorded in searches.jsonl and appended with their literal tool/query and returned log records.

## Searches and reuse

I read the chapter and unit records and the newest blueprint prop-sf-pf-coherence.proof.md. Whole-DAG and blueprint searches for projection/base change, open base change, open tensor and monoidal square found the already existing open-factor, mate and compactification-pasting nodes. I opened every cited statement. The common-projection factor/transport nodes were also examined; they prove single-arrow coefficient squares, not the desired base-change identity. No new node is needed because the only extra assembly here is applying functors to an existing open identity and cancelling its prescribed endpoints.

NV Mathlib searches: two semantic phrasings with LeanFinder, one LeanSearch phrasing, Loogle `CategoryTheory.Adjunction, CategoryTheory.Functor.Monoidal`, and the logged projection/baseChange grep. All services answered. The semantic hits were slice pullback adjunctions, projective-spectrum pullback equations, condensed projectivity facts, and the general mate-counit identity. Loogle returned monoidal adjunction unit/counit laws. None states the common-coefficient compact-support equation; the grep found no hits. These general category-theoretic facts do not replace the existing categorical-projection-mate-square node or the required geometric normalization.

## Not duplicates

No new nodes. The existing integral open identity is reused, not copied into a new field-level lemma. No clause of the item's conclusion has been moved to a new node.

## Review by NV

I read the current blueprint base-change paragraph against its chapter and unit route. It first separates the open and proper factors, then uses monoidality and the ordinary counit mate calculation, and then composes them for a chosen compactification. The six steps implement precisely this route. The proof is marked agent-origin because its coefficient bookkeeping is my assembly of the blueprint and the cited statements. I also read Stacks sites-cohomology.tex, Tag 07A4 (lemma-pullback-tensor-product) and Tag 0E48 (remark-compatible-with-diagram). The latter explicitly omits the verification; I use the existing categorical node supplying that calculation, whose project source ProjectionMapMate.lean was read, rather than treating the Stacks remark as a proof. No SGA source is used.

Step 1 uses def-sf-operation-stages for the actual push stage, ordinary adjunctions and comparisons, and def-weil-finite-tor-amplitude for the explicit equality of the field Tor and bounded-constructible categories. There is no claim that bounded constructibility alone implies finite Tor at finite coefficients. All symbols are exactly the proper/open factors of the supplied compactification.

Step 2 uses lem-sf-pf-open-base-change-square for its displayed completed open equation. I checked that its horizontal map is arbitrary, that its first input has no Tor restriction, and that its second input does have one. Applying it with the proper factor equal to the identity permits an arbitrary integral P_0. The separate lem-coef-integral-residue-tor statement supplies this P_0's uniform finite-reduction interval, so no hypothesis is dropped. This is an equality of completed arrows, exactly as the cited node states.

Step 3 uses the literal pair-category model in def-weil-algebraically-closed-coefficients and the same-object raw localization in def-weil-rationalization-karoubi. Thus K and P admit simultaneous finite-field models and integral object representatives; there is no idempotent completion or claim that a field object has a finite reduction. def-exchange-projection's higher-stage clause explicitly defines the maps as rationalized and common-field classes with scalar comparisons intertwining units, counits and comparisons. def-sf-operation-stages supplies the same normalized open/pullback/composition endpoints, not separately chosen isomorphisms. def-pur-completed-pullback-tensor-comparison specifies the actual common-field tensor-pullback representative; lem-pur-derived-pullback-tensor-iso states scalar and composition compatibility. I read these clauses and the corresponding commonStageComparison and commonStageExchangeComparison fields in SixFunctorOperationDatumStages.lean:351–544,902–988. No theorem about an unrelated coefficient category is being invoked.

Step 4 is elementary preservation of the step-2 equality by localization and inclusion. For each constituent r the equation is r_common = c_target C(r) c_source^{-1}; composing two such expressions cancels the middle endpoints. The displayed calculation spells out the entire transport, and the identity/tower clauses already cited in step 3 make its class independent of an enlargement. It neither assumes faithfulness of evaluation nor assumes the desired complete base-change square. This short application of functoriality is a step, not a new node.

Step 5 uses the composition law and naturality explicitly stated by lem-pur-derived-pullback-tensor-iso. Both paths in its displayed tensor square compute the tensor comparison of the same map ph=gp' using the actual two compositors. This verifies the ComparisonCompatible hypothesis, rather than appealing just to the existence of a tensor isomorphism. lem-sp-categorical-projection-mate-square then gives precisely the displayed proper-factor equation with d=(1 tensor theta^{-1})mu_H. The two adjunctions are those of the supplied stage, and def-exchange-projection defines the actual exchange and projection as that mate and counit projection. No invertibility of these arrows or adjunction for g is used.

Step 6 uses the statement of lem-sf-pf-compactification-pasting, which expressly assumes exactly the two preceding factor identities, and identifies the resulting target comparison. I checked its L-domain against step 1. The normalizations of def-exchange-projection and composition compatibility of lem-pur-derived-pullback-tensor-iso identify its target with the item's explicit kappa, in the order A J F_p -> J' H F_p -> J' F_p' G. These are precisely the supplied factorizations f=pj and f'=p'j', not arbitrary isomorphisms. The compactification is retained throughout, so no refinement-independence theorem with extra hypotheses is needed.

For edge cases I checked j the identity (the open equation reduces to its canonical tensor square), empty X (all open-factor inputs are zero), f proper with identity-open compactification (the result is the proper mate identity), and repeated coefficient fields (the identity scalar cocycle removes the redundant transition). A nonseparated horizontal map is allowed in the cited integral open-square statement, and the proper mate theorem is categorical with no geometric condition on its horizontal functors. The actual data supply the domains at the common stage. There are no new statements requiring additional small-case tests. Each step is shorter than 2000 characters; none hides an additional lemma beyond the stated existing dependencies. I checked B–E: statements are unchanged, all non-elementary inputs have nodes, no duplicate or restated clause was created, the cited statements provide the facts used, and the exact maps and hypotheses are retained.

## Unfinished work

No mathematical part of this one-level split remains. Dependencies remain the existing nodes for their own future work. Server validation and delivery results are recorded below after they run.

## Validation

The first dry run rejected two citation excerpts shorter than its 40-character minimum. I expanded them to the full relevant field-domain and raw-localization clauses, and made the proper-mate and compactification-exchange quotes specific to their proof steps. No mathematical statement or proof step changed.

The second dry run exited successfully: `OK (not pushed) deliver/NV/lem-sf-projection-base-change-common at f3759d2e640: preflight passed`. All checks ran through the required server delivery command; no Lean compilation or local DAG/preflight script was run.
