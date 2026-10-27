## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-smooth-surjective-fppf-locality.json`: statement, now split into five proof steps; no Mathlib algebraic-space match.
- `citations.json`: one verbatim statement quotation for each of the 24 citations in the five steps.
- `searches.jsonl` and `search-smooth-descent.txt`: actual Q97 search records and the saved second LeanFinder response.

No new nodes and no new Mathlib leaves. The item statement, its statement dependencies, inherited citations/searches, source, created record, and blueprint ancestry are retained. No Lean was written or compiled; nothing in the shared repository or launcher was written.

## Attachments

No exact project declaration was found by searching `lean/WeilConjectures/` for the item id, its blueprint docstring tag, AlgebraicSpace, and smooth/fppf locality. The existing closed declaration `AlgebraicGeometry.Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` belongs to the already attached `lem-galois-fpqc-family-descent-of-local-property`; it is used through that existing node, not offered as an attachment for the item. I read its scheme hypotheses and proof at `lean/WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`, especially the Descent section.

## WANTED

None. All mathematical sources used are available under `literature/stacks-project/`. The obsolete inherited instruction to read `coord/dag-sync.md` refers to a file absent in this shared repository; the supplied shared-repository and current-blueprint instructions were followed.

## Corrections and route

No statement dispute or mathematical correction was needed. The unsplit item had no proof. Its source is sound, but smooth scheme descent cannot be applied directly to an algebraic-space source. The split first passes to a scheme atlas, applies scheme descent to its composite, and then uses the precise presentation criterion to return to the algebraic-space assertion. The surjectivity argument consistently allows extension of the representing field.

The current blueprint is `literature/blueprint/latest/`, snapshot `7284bb09daf97437d544c51882b325f9c52cd345` in COMMITS.txt. I read the chapter and unit records and the current chapter, unit, and direct-images proof files. This remains the supporting input in the recorded alteration/moduli/groupoid-quotient dependency chain under direct-images proof (3). No unit statement, unit step, or chapter route is replaced. The generic scheme fpqc-family theorem supplies the finite-affine assembly that Stacks 0429 packages through 041J; its hypotheses are established in step 3. The item's existing blueprint ancestor is null, as confirmed by `blueprint_refs.py ancestor`; that inherited metadata was retained rather than inventing a blueprint ancestor.

## Not duplicates

No nodes were created. Whole-DAG tag and keyword searches found the existing scheme smooth descent, scheme base-change, algebraic-space presentation, etale scheme-test, fppf covering base-change, and fppf-to-fpqc lemmas, all reused. Whole imported-blueprint searches for smooth, surjective, smooth surjective, and fpqc found no equivalent blueprint item. The nearby finite-field-extension theorem `thm-pd-fpqc-local-properties` only states descent for a scheme over a field with several simultaneous properties; it does not supply the general assertion needed here. The existing generic fibred-groupoid calculus was also inspected but was not used to assume an unproved comparison between smoothness of a space map and smoothness on all its scheme base changes.

## Mathlib searches

All new Q97 queries were run with the required msearch.py command and are recorded verbatim in the item and searches.jsonl. Both semantic services answered; Loogle answered that its index did not recognize AlgebraicGeometry.IsSmooth. The second phrasing of LeanFinder returned scheme smooth base-change/composition, scheme flat base-change, and relative-dimension results. LeanSearch likewise returned scheme smoothness definitions. The grep found scheme surjective fpqc descent and a ring-smooth import. I read the actual scheme Smooth, LocalFlatDescent, and FlatDescent files at the returned locations. These facts do not have arbitrary algebraic spaces as their objects, so the item is not a Mathlib leaf. The inherited Q23 searches are preserved as history, not claimed as Q97 executions.

## Review by Q97

I read spaces-descent.tex `lemma-descending-property-smooth` (0429) and `lemma-descending-property-surjective` (041Q), spaces-morphisms.tex `lemma-base-change-smooth` (03ZE), `lemma-base-change-surjective` (03MH), `lemma-local-source-target` (03MJ) and `remark-base-change-P`, and spaces-properties.tex `lemma-points-cartesian` (03H4), including its common-field-extension proof. I verified these tag/label correspondences in tags/tags. I also read the scheme descent proof in descent.tex `lemma-descending-property-smooth` (02VL). There are no new-node sources to certify.

Step 1 uses the actual statement of def-trf-algebraic-space for atlases, lem-trf-space-fibre-products-etale-covers for space fibre products, and lem-trf-space-representable-etale-scheme-tests for representability and composition/base change of surjective etale maps. The scheme-locality lemma explicitly says smoothness is etale local on source-and-target, which is the hypothesis required by lem-sfb-space-etale-presentation-property-criterion. That criterion states both directions between every chart diagram and one diagram with surjective source chart. Lem-pc-proper-base-change has an independent smooth clause (2), so no properness assumption is being imported. The displayed triple description checks the intermediate pullback identification rather than merely calling it a transport. All schemes and spaces stay in the standing universes.

Step 2 uses the extension-lifting formulation actually stated in def-trf-algebraic-space-jointly-surjective-family, and the sheaf fibre product statement. Forming the compatible pair after the same extension is elementary. It does not assert rational-point surjectivity over the initial field.

Step 3 uses exactly the three hypotheses of lem-galois-fpqc-family-descent-of-local-property: arbitrary scheme base change from the independent smooth clause of lem-pc-proper-base-change; single flat quasi-compact surjective descent from lem-trf-smooth-fpqc-base-descent; and target Zariski locality from condition (iii) of lem-sfb-scheme-etale-source-target-properties, applied to preimages of target opens. Lem-weil-pbc-open-immersion-etale supplies the etaleness of these open inclusions. Thus the generic theorem is not being invoked with an unchecked locality hypothesis. Its statement has no finiteness condition on the map being descended. The brief verification of target locality is a few-line specialization of existing statements, not a new lemma to create.

Step 4 uses def-trf-algebraic-space to choose U, the representable-etale scheme-test node for its base-changed atlas, and both the scheme-locality and presentation statements for the two chart arguments. Lem-trf-fppf-covering-is-fpqc states that the SAME covering family is fpqc, even when its members are not quasi-compact. Step 3 therefore applies to U -> Y. This is the scheme-atlas reduction used in the source, with the existing closed family theorem for its cover assembly.

Step 5 uses lem-trf-fppf-covering-base-change and the joint-surjectivity clause of def-pc-fppf-site to obtain a point above Spec K. Def-a1-algebraic-space-point-classes explicitly uses residue-field representatives, and def-weil-residue-field states that the residue field of a point over Spec K is an extension of K. The extension-lifting definition of space surjectivity then provides a further extension M and a point of X_i. The fibre-product equations prove the projected point maps to y restricted to M. Each citation says the fact taken from it; citations.json copies those actual statements verbatim. This step is marked elementary because, after the cited covering result, it is the explicit two successive lifts and projection.

I checked empty target and empty covering, empty members of a covering, identity maps, arbitrary (possibly nonreduced) base change, and field extensions that need not preserve rational points. No quasi-compactness, finite type, Noetherianity, representability of f by schemes, or separation was introduced. An empty source over a nonempty target is not incorrectly called surjective; it is smooth as the empty chart test requires. All steps are below 2000 characters and none conceals an uncited comparison or lemma. No SGA source is used. The two declared off-unit tools are generic representable-etale scheme tests and the point-class definition. Other scheme tools are Mathlib leaves or already Lean-closed. I checked that all dependency chains of the potential inputs avoid the item. No maintainer fields or other workers' nodes were changed.

## Unfinished work

None in the stage-1 split. Existing cited lemmas keep their own independent DAG work items. Server dry run and direct delivery are performed after this report is written.
