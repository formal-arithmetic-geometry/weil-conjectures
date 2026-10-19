# Worker report

Item: `lem-coef-model-cofibrant-colimit-comparison`. Group: NV. Date: 2026-10-17.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-model-cofibrant-colimit-comparison.json`: the recovered item, split into four proof steps.
- `citations.json`: four verbatim citation certificates, one for each proof step.
- `report.md`: this report.

No new child nodes and no Mathlib leaves were created. The item itself was absent from the shared snapshot at the start of the turn. I recovered the authoritative item JSON from the isolated worktree snapshot referenced by the prior worker's synchronization investigation, then preserved its statement, chapter, unit, blueprint ancestry, source, and maintainer fields while adding the stage-1 split.

## Attachments

None. Searches of the supplied slopmaster2 source and the upstream-master reference found no declaration tagged `(blueprint: lem-coef-model-cofibrant-colimit-comparison)` and no declaration stating this three-clause comparison.

## WANTED

WANTED: Mark Hovey, *Model categories*, Definition 5.1.1, Theorem 5.1.3, Corollary 5.1.6 and Lemma 5.2.6, printed pp. 120–127, for the item. The source was read online in the earlier synchronized split; it is not archived in `literature/`.

## Findings and corrections

The prior worker reported a missing source node and could not dry-run. The missing node was a synchronization/packaging fault, not a mathematical objection. Its statement is now restored exactly from the isolated snapshot. I did not weaken or alter any hypothesis: coproducts are small; all span objects are cofibrant and both attaching maps are cofibrations; ordinal diagrams are continuous at every nonzero internal limit and have cofibrant initial objects; and no properness assumption is added.

The item is a genuine generic tool rather than a restatement of the downstream restriction theorem. Its three clauses are used by the cell induction in `lem-coef-locally-cofibrant-dg-restriction`. I kept them as proof steps rather than creating children that would merely restate clauses of the item.

## Not duplicates

`lem-coef-model-cofibrant-colimit-comparison` vs `lem-coef-reedy-model-structure`: the existing node gives Reedy structures for general direct diagrams but does not state weak-equivalence preservation by these colimits, the one-cofibration pushout cube, or the coproduct conclusion.

`lem-coef-model-cofibrant-colimit-comparison` vs `lem-coef-finite-reedy-localization`: the existing node is restricted to finite direct/inverse indexing and localization of diagram categories; it does not give the ordinal and pushout comparisons here.

`lem-coef-model-cofibrant-colimit-comparison` vs `lem-coef-transfinite-left-lifting`: the existing Mathlib leaf concerns closure of a left-lifting class under transfinite composition, not weak equivalences between two cofibrant chains.

`lem-coef-model-cofibrant-colimit-comparison` vs `lem-coef-presentable-cellular-factorization`: that node constructs one cellular factorization and does not compare colimits of two diagrams.

## Mathlib search assessment

I ran the required `leanfinder`, `loogle`, `grep`, and `leansearch` searches with the item id and recorded their actual queries and verdicts in the node. The returned Mathlib declarations concern closure of cofibrations or trivial cofibrations, individual pushout inclusions, cylinders, homotopies, and transfinite lifting. None states the combined weak-equivalence comparison for coproducts, cofibrant spans, and continuous ordinal chains. Thus the item has no Mathlib match.

## Review by NV

I read the recovered item, its chapter `sec-six-functors`, unit `sk-prop-sf-biduality-general`, the current `main-20261015` blueprint ancestor proof, `lem-coef-model-infinity-derived-adjunction`, and the stage-1 and delivery-error instructions. The item’s only statement dependency is the model-category/localization convention node; the citation certificates quote its exact model-category axiom sentence for every step.

Step 1 treats a small coproduct as the colimit of a discrete direct diagram. The latching maps are initial maps of cofibrant objects, so the diagram is cofibrant; Hovey’s direct-diagram colimit theorem gives the weak-equivalence comparison and the same latching argument gives cofibrancy of the coproduct.

Step 2 treats the walking span as a finite direct diagram. I checked that its latching maps use the cofibrant initial maps and the specified cofibration leg. Hovey’s cube lemma applies to the objectwise weak-equivalence map of cofibrant span diagrams, and pushout closure of cofibrations gives cofibrancy of both ordinary pushouts.

Step 3 checks the ordinal hypotheses against the direct Reedy latching maps: initial stage, successor cofibrations, and continuity at every nonzero limit. The ordinal homotopical-colimit theorem then gives the weak equivalence on colimits and the latching induction gives cofibrancy.

Step 4 records the properness scope. The proof uses only cofibrant direct diagrams and their homotopical colimit theorem; it never pushes an arbitrary weak equivalence along an arbitrary map, so no properness hypothesis is being smuggled in.

I checked small cases: the empty coproduct is the initial object; identity maps give identity comparisons; the ordinal case covers `theta = omega` and chains with an internal limit; and a one-step ordinal reduces to the cofibrant pushout calculation. The item’s statement remains unchanged and no source error or statement dispute was found.

## Unfinished work

No split work remains. The second worker should inspect the restored node and run the delivery dry run. No Lean file, compiler, Lake, or live project was touched.

## Dry-run outcome

After the earlier launcher lock stalls, the required retry completed successfully: `deliver.py NV lem-coef-model-cofibrant-colimit-comparison --no-push` printed `OK (not pushed) deliver/NV/lem-coef-model-cofibrant-colimit-comparison at d90813a744: preflight passed`. No delivery branch was pushed and no live repository was changed.

## Second reading by NV

Read independently on 2026-10-17 with the item, all four cited node statements, and the source open. I read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the worker/stage-1 contract, the unit/chapter records, and the current main-20261015 ancestor proof. Source: Hovey, *Model categories*, https://ericmalm.net/ac/projects/symmetric-spectra/hovey--model-cats.pdf, Definitions 5.1.1–5.1.2, Theorem 5.1.3, Proposition 5.1.4, Corollaries 5.1.5–5.1.6, and Lemma 5.2.6 with its proof, printed pp. 120–127. The colimit definition was also read in Stacks `categories.tex`, Tag 002F, label `definition-colimit`, lines 1310–1337. The item is not a Stacks assertion; no tag has been invented for it.

Statement: PASS against Hovey hypothesis by hypothesis. Small coproducts use discrete direct categories; the pushout cube requires only the specified cofibration leg in each span, together with cofibrancy, and arbitrary small ordinals are direct categories by Definition 5.1.1. The continuity and initial/successor hypotheses imply precisely the required cofibrant ordinal diagrams. The no-properness scope is correct. The statement was not changed, and there is no statement dispute. The original review's claim that the walking span is a cofibrant *direct* diagram with only one leg a cofibration is false; it is repaired below using the mixed Reedy structure from Hovey's cube proof.

- Step 1: PASS against the full weak-equivalence-preservation clause of `lem-coef-model-infinity-derived-adjunction`, `def-weil-pbc-category-colimit`, and Hovey Corollary 5.1.6/cube proof; the elementary part is the cocone adjunction and corresponding lifting-square bijection, and the non-elementary preservation theorem is explicitly cited.
- Step 2 (original step 1): PASS against `lem-coef-reedy-model-structure` with degree zero, the model-adjunction clause, the colimit definition, and `lem-coef-lifting-class-closure`; the constant right adjoint preserves both required classes, and the empty coproduct is checked explicitly.
- Step 3 (original step 2): REPAIRED/PASS against Hovey Lemma 5.2.6 and the statements of the Reedy, model-adjunction, colimit, and lifting-closure nodes; degrees are now x=0, a=1, b=2, the inverse arrow is a→x, and the matching-map calculation proves the constant functor preserves fibrations and trivial fibrations. The unassumed left leg is never treated as a cofibration.
- Step 4 (part of original step 3): REPAIRED/PASS against Hovey Proposition 5.1.4/Corollary 5.1.5 and the ground WFS and colimit statements; the relative latching square, agreement on its overlap, commutation on each coprojection, transfinite lift, and restriction to predecessor segments are written out. The natural-number-only Reedy statement is explicitly not applied to an arbitrary ordinal.
- Step 5 (part of original step 3): REPAIRED/PASS against Hovey Theorem 5.1.3's factorization proof and the ground functorial WFS/colimit definitions; the map to factor is specified on both pushout legs, and zero, successor, limit, functoriality, and composition checks are included.
- Step 6 (part of original step 3): REPAIRED/PASS against Hovey Theorem 5.1.3/Remark 5.1.7, the two ground left lifting classes, and `lem-coef-lifting-class-closure`; both directions identifying relative trivial cofibrations are proved, with transfinite induction in the reverse direction and no continuity assumption on intermediate diagrams.
- Step 7 (part of original step 3): REPAIRED/PASS against Hovey Theorem 5.1.3 and the complete model-category and lifting-closure statements; objectwise (co)limits, retract preservation, mutual lifting characterizations, and both functorial WFS are verified, so the ordinal diagram category is a model category rather than an unproved invocation of a source theorem.
- Step 8 (original steps 3–4): REPAIRED/PASS against Hovey Corollary 5.1.6, the proved ordinal model structure, the ordinary weak-equivalence-preservation clause of the model-adjunction node, and the colimit definition; the initial, successor, and nonzero-limit latching maps are checked separately for both chains, and properness is absent throughout.
- New nodes: none; B1–B7 and child-node duplicate/leaf checks are vacuous. All work stays in the item's proof; no new node restates a clause or the whole item.

Small-case checks: an empty coproduct is the cofibrant initial object with identity comparison; one summand and constant chains give the original weak equivalence. In complexes of vector spaces over a field, the cofibrant span with left leg the noninjective projection k²→k and right leg the identity k²→k² shows exactly why the old direct-Reedy argument was invalid, while the mixed Reedy argument gives pushout k. Taking A initial gives the binary coproduct case, and taking i an identity gives X as the pushout. Ordinals omega and omega+omega test both the unbounded-degree issue and the internal limit at omega; continuity makes that latching map an isomorphism. Zero complexes and all-identity transformations give zero colimits and identity comparisons. Ordinals 0 and 1 are outside clause (c), but the auxiliary diagram construction still handles the empty and singleton categories and introduces no hidden nonempty predecessor assumption.

Independent searches: ran msearch.py with all four services/tools, using the alternative phrases recorded in the appended log entries: a left Quillen colimit functor on direct diagrams, `"CofibrantBrownFactorization"`, Reedy/leftQuillen/colim–weakEquivalence source patterns, and weak equivalences of continuous ordinal chains. Read Mathlib `AlgebraicTopology/Reedy/Basic.lean:14–24` (diagram model structures remain TODO) and `ModelCategory/BrownLemma.lean:43–87` (a single-map factorization with a section, not this colimit comparison). Neither semantic search nor Loogle supplies an exact declaration for the item. Searches of both named read-only source trees by the item id and model/colimit/Brown/Reedy terminology found no attachment. A whole-blueprint search for coproduct weak equivalences, colimit Quillen, ordinal model, cofibrant colimit, and cube lemma found no blueprint duplicate. The existing Reedy node has natural-number degrees, the direct-WFS extension node is finite, and the small-direct-colimit-lifting node also has natural-number degrees; none supplies the arbitrary-ordinal argument. The existing transfinite-left-lifting leaf closes a lifting class under one continuous composition and does not compare two weak-equivalence diagrams. No child or false leaf was introduced.

Changes made: replaced the false direct-span assertion by the explicit mixed Reedy proof; replaced uncited homotopical-colimit invocations by existing-node citations and the complete transfinite construction; expanded the factorization/retract/limit checks that were missing under C1–C4 and E5; regenerated all 23 citation certificates from the actual cited statements, including the model-adjunction preservation clause rather than only its axiom preamble; added four actual independent search records. The current shared snapshot now contains the authoritative unsplit item, so its `created.item` ancestry and maintainer-owned metadata were restored from that record instead of the recovered sandbox's self-parent metadata. The first worker's sections, including `## Review by NV`, are retained as requested; this section supersedes their incorrect span calculation and claim that four source references alone constitute the proof.

Delivery validation follows below. No Lean files or build tools were used, and no live project or launcher was written.

Second-reader dry run: `deliver.py NV lem-coef-model-cofibrant-colimit-comparison --no-push` printed `OK (not pushed) deliver/NV/lem-coef-model-cofibrant-colimit-comparison at b6d36e5846: preflight passed`. The required server checks passed on the repaired eight-step split, with zero new nodes and zero new Mathlib leaves. Proceeding with the required delivery command.
