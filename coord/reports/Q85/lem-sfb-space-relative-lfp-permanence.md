# Stage-1 delivery: lem-sfb-space-relative-lfp-permanence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-lfp-permanence.json: statement, split into three steps; not a Mathlib leaf. No new nodes.
- citations.json: eight entries, one for every step/node citation, checked as exact substrings of the cited statements.
- searches.jsonl: five actual msearch calls and their returned records; the item retains its inherited searches as well.

## Attachments

No attachment for this item: searches by its blueprint tag and by algebraic-space terminology in lean/WeilConjectures found no declaration of algebraic-space cancellation. The existing node lem-a1-map-over-base-finite-presentation already belongs to AlgebraicGeometry.locallyOfFinitePresentation_of_comp, WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:53–57. I read its scheme statement and proof; it supplies the scheme step, not the algebraic-space item.

## WANTED

None.

## Problems found and changes

No statement dispute. The item agrees exactly with Stacks 05WT, including the absence of separation and quasi-compactness assumptions. The imported empty proof needed an explicit account of why U -> X, V -> Y are surjective etale and why U -> W has local finite presentation. Its inherited blueprint.from.node is null: blueprint_refs.py ancestor prints None. I retained this inherited provenance and its detailed place/via chain rather than fabricating an ancestor. The latest blueprint's direct-images proof (3) now states the proper/open compactification route; the item's inherited provenance describes the existing supporting alteration/Picard branch, not an additional literal lemma in that blueprint. Searches of the whole blueprint index for finite presentation, finite-presentation-permanence, and algebraic spaces found no exact counterpart. The supplied item is not the unit's key statement, so no unit record is changed.

Mathlib searches were performed with the prescribed msearch command: two semantic phrasings, Loogle, LeanSearch, and source grep. All services returned successfully. I read RingHom.FinitePresentation.of_comp_finiteType at Mathlib/RingTheory/FinitePresentation.lean:442–446 and the scheme finiteness definitions/instances; none states the algebraic-space theorem. The no-Noetherian hypothesis was checked against the Loogle Noetherian hits, which cannot be used here. Existing recorded searches are preserved, with five new logged searches appended.

## Not duplicates

No new nodes were created. In particular lem-a1-map-over-base-finite-presentation is reused for scheme cancellation, lem-sfb-space-etale-presentation-property-criterion for general presentation descent, lem-sfb-scheme-etale-source-target-properties for the finiteness properties' etale locality, and the existing trace-formula fibre-product and representable-etale calculus nodes for chart construction. Creating a new scheme cancellation or atlas-calculus node would duplicate these.

## Unfinished work

None at stage 1. No Lean was written, no compiler or build invoked, and no repository or launcher file was changed.

## Review by Q85

I read spaces-morphisms.tex Tag 05WT (lemma-finite-presentation-permanence), including its W, V, U atlas proof, and scheme Tag 02FV(1) in morphisms.tex. I checked the general extension criterion in spaces-morphisms.tex Tag 03MJ, the definition of local finite presentation in that file, and the chart interpretation in Tags 0410 and 040Y. I read spaces-properties.tex Tag 03EC for etale maps over an algebraic space, and the statements and relevant proofs of the existing fibre-product, representable-etale, scheme locality and general presentation nodes. No new node requires a source review.

Step 1 uses def-trf-algebraic-space for the existence of an atlas, lem-trf-space-fibre-products-etale-covers for the two intermediate algebraic spaces and the base changes of covers, and lem-trf-space-representable-etale-scheme-tests for arbitrary base change and composition of representable surjective etale maps. Each statement explicitly gives the fact used. The composite a:U -> X, not merely U -> X_V, is the source chart in the final application; b:V -> Y is similarly the composite of the atlas with the pullback of W -> Z. The commuting squares follow immediately from the fibre-product projections. This does not assume that X, Y, Z or the intermediate spaces are schemes, and does not assume arbitrary maps of spaces are representable.

Step 2 uses lem-sfb-scheme-etale-source-target-properties for both finiteness properties being etale local on source-and-target, and condition (1) of lem-sfb-space-etale-presentation-property-criterion for q:V -> W and qh:U -> W. This criterion allows every compatible etale presentation diagram, not just cartesian ones, so no unjustified assertion that U is an atlas of X x_Z W is needed. I then read the whole statement of lem-a1-map-over-base-finite-presentation: with S=W, X=U, Y=V it states exactly the required scheme cancellation under the two hypotheses just obtained. Its source-open and local-finite-type conclusions are not needed. The existing closed Lean declaration at lines 53–57 confirms the scheme cancellation statement.

Step 3 uses condition (2) of the same presentation criterion; step 1 supplies surjectivity of a and etaleness of both vertical maps, step 2 supplies local finite presentation of h, and scheme locality supplies the criterion's property hypothesis. All cited statements were opened and all citation quotes are verbatim. Every non-elementary assertion has a node; the only inline calculations are the commuting projection identities. The two trace-formula lemmas are declared as generic tool uses, not a replacement of the unit's route.

I checked B1–B10: no new unsplit statements, no missing definitions in the unchanged statement, TeX and exact source labels retained, genuine searches only, no false Mathlib leaf, provenance retained. For C1–C8, every input is listed and quoted, only statements rather than proofs are used, and no proposed dependency points back to the item. For D1–D5 the argument genuinely reduces spaces to schemes rather than moving cancellation into a renamed node. For E1–E6, the base of scheme cancellation is W, all three chart objects are schemes, the maps are in the correct order, and no flatness, Noetherian, separatedness or quasi-compactness is smuggled in. I checked empty X (empty atlas makes the conclusion vacuous), empty Z (the maps force all spaces empty), identity g, scheme-representable cases, and arbitrary non-quasi-compact atlases; all satisfy the same proof. No step exceeds 2000 characters. There was no false source assertion to correct.
