# Worker report: lem-trf-synchronized-resolution-zariski-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-synchronized-resolution-zariski-descent.json`: statement, split; ten proof steps using 22 existing dependencies; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/dependency pair.
- No new nodes, no new Mathlib leaves, no Lean files and no unit/chapter changes.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id, synchronized resolutions, ordinary resolution rules and labeled blowup towers. The hits concern cohomological resolutions or unrelated synchronization; none states this item. The item has no Lean attachment.

## WANTED

None. The source PDF and the relevant Stacks sources are present.

## Findings and changes

The live item was unsplit, its proof was empty, and the sandbox contained only dispatcher brief markers. There is no released repair note for this id. I retained the entire statement, its dependencies, provenance and historical blueprint chain, and added the proof. In particular the result is conditional on the assignment A; it does not construct a resolution algorithm or replace any desingularization theorem.

The proof follows the disjoint-union synchronization mechanism of ILO VIII Remark 2.3.5(ii). It exposes the actual descent of ideals as a sectionwise construction and the induction by ordinary blowups. It also writes out why a combined covering family cannot have a label that disappears on one of the original covering families. This last argument needs the affine overlap tests and nonemptiness of each global center; it does not follow just from inclusion of label lists.

I searched the whole DAG for ideal descent, blowup flat base change, unit-ideal blowups, ordinary/logarithmic tower descent, and cover independence, and ran `tools/blueprint_refs.py search` for blowup, synchronization and resolution. The existing logarithmic and fan descent statements concern different objects and are not used as ordinary-scheme descent theorems. I reused the ordinary blowup interfaces instead. The compatible-ideal construction is elementary from the sheaf condition and local definitions, so it does not become another node. Likewise padding and the label-exclusion argument remain steps of this item's proof, rather than new nodes restating its clauses.

I ran LeanFinder twice, LeanSearch, Loogle and two greps through the required msearch command; the log is `searches.jsonl` and the exact new queries appear in `mathlib_searches`. Both greps and Loogle returned no hits. Semantic searches returned general scheme cover, representability, gluing, descent and affine-transition-limit constructions, not labeled ordinary blowup tower synchronization. These do not specialize in one line to the item. The item's earlier search records are retained.

The latest blueprint ancestor has been revised to the contracting-correspondence argument. The item explicitly belongs to the retained historical alteration/resolution support branch through `lem-trf-smooth-functorial-ordinary-resolution`. I checked the latest chapter, unit and ancestor text and preserved that recorded lineage. This delivery changes no chapter or unit route. Generic facts from other units are explicitly declared in `split_report.tool_uses` for review.

## Not duplicates

No new nodes are proposed. Existing ordinary blowup base change, complement and cover-independence nodes are cited directly; no logarithmic or monoidal analogue is duplicated.

## Review by Q31

I read ILO, *Travaux de Gabber*, Expose VIII, printed pp.87--88 and 91--92 (PDF pp.93--94 and 97--98), specifically 2.1.4--2.1.9, 2.2.11, 2.3.1--2.3.5. In 2.1.4 the centers are part of a tower; 2.1.9 supplies ordinary flat pullback; 2.2.11 describes descent by descending centers; Remark 2.3.5(ii) explains synchronization by a disjoint union and reinsertion of empty blowups. These support the mechanism, but the exact conditional statement and combined-cover argument are an agent expansion. I therefore set `proof_origin.by` to `agent`, not `document`. No normalized-blowup or logarithmic theorem is substituted for the ordinary construction.

For the generic source checks I read Stacks `morphisms.tex`, Tags 01T2 (`lemma-locally-finite-type-characterize`), 01T3 (`lemma-composition-finite-type`), 01T5 (`lemma-immersion-locally-finite-type`) and 01T6 (`lemma-finite-type-noetherian`); `properties.tex`, Tags 01OV, 01OW and 01OZ (Noetherian definitions, open restriction and underlying topology); and `divisors.tex`, Tag 0805 (`lemma-flat-base-change-blowing-up`), 0806 (`lemma-universal-property-blowing-up`), 0807 (`lemma-blow-up-effective-Cartier-divisor`) and 02NS (`lemma-blowing-up-projective`). I read every cited DAG statement, including the constructed-map definition needed to interpret the short base-change theorem. Existing closed ordinary-blowup declarations are tools, not an attachment for the whole item.

Step 1 uses `lem-weil-pbc-finite-type-over-noetherian` for the Noetherian source, `lem-weil-pbc-noetherian-open-subscheme-noetherian` for quasi-compactness of arbitrary opens, `lem-weil-pbc-qc-open-immersion-finite-type` for the open map, and `lem-sfb-finite-type-composition-base-change` for its composite to Spec Q. The hypotheses are met because the original S is finite type over the Noetherian one-point scheme Spec Q. To check quasi-compactness of the open immersion, the proof tests its inverse image over every affine open, rather than confusing a quasi-compact source with a quasi-compact morphism. `lem-pqf-finite-affine-cover-qc-open` supplies a finite affine cover. These statements all say the facts used, including the nonseparated case.

Step 2 uses `def-pc-reduced-scheme` to retain reducedness on opens and `lem-pc-affine-finite-type-algebra` for finite algebra generators. The polynomial quotient and `def-weil-closed-immersion` give the embedding. `sbc-lem-affine-space-smooth` gives smoothness of the ambient affine space; `lem-weil-pbc-affine-source-morphism-separated` gives its separatedness. Thus A is only evaluated on inputs in its actual domain, including the affine W inside an overlap. Finite disjoint unions are allowed expressly by the item, so no unsupported functoriality for a general map from a disjoint union to S is assumed.

Step 3 checks open-immersion flatness using the local-ring isomorphism in `def-weil-open-immersion` and the exact stalk definition of `def-weil-flat-morphism`. It cites `def-nagata-blowup-flat-base-change-map` as well as `thm-nagata-blowup-flat-base-change`: the latter's statement is short, but the former states the actual map, extended ideal and fiber product it makes invertible. `thm-nagata-global-blowup-complement` applies to a unit ideal with empty zero scheme and makes the whole restriction an isomorphism. Hence only unit ideals are deleted. I did not delete a proper Cartier center merely because its blowup is an isomorphism.

Step 4 takes the agreement of contractions with A(W) from the item's explicit hypothesis. The labels in the fixed ordered set identify exactly where the unit stages must be reinserted. The overlap and triple-overlap identifications are made with this same padded tower. `lem-weil-pbc-affine-opens-basis` supplies all further overlap refinements. `prop-nagata-global-blowup-cover-independent` asserts uniqueness of the canonical blowup comparison on common affine refinements, which is exactly the uniqueness used here. It is not used as an arbitrary scheme-descent theorem. Intersections of affine opens are never asserted affine.

Step 5 is elementary and has an explicit compatible-section formula, not just a reference to descent. I checked that its restriction is exactly each given ideal, that its sheaf property follows from those of the structure sheaf and local ideals, and that uniqueness follows by local membership. The definitions in `pqf-def-coherent` are used for quasi-coherence, finite type and coherence separately: the kernel of every finite-free map is locally the kernel for the supplied coherent ideal, so its finite generation is local as well. This proves coherence without an unstated flat or fpqc module-descent theorem.

Step 6 uses `def-nagata-global-blowup` for the next scheme and ordinary flat base change to recover the supplied local levels. The induction hypothesis specifies the current level and lifted opens before any next center is constructed. `prop-nagata-global-blowup-cover-independent` identifies the local comparisons. `thm-nagata-global-blowup-proper` applies to the descended finite-type ideal. `def-weil-proper-morphism` includes finite type, and `lem-sfb-finite-type-composition-base-change` proves the structure morphism remains finite type. In particular the proof does not assume that the initial nonseparated S is proper or separated.

Step 7 uses the local-ring characterization in `def-weil-regular-scheme` for both centers and final scheme. The restrictions are open parts of the given regular centers/final scheme, so no smooth descent of regularity is needed. Nonempty centers are detected on the lifted covering family. For nowhere denseness the proof intersects any purported nonempty interior with a chart; this contradicts the original nowhere-dense center there. These two assertions are elementary open-cover arguments and are marked accordingly.

Step 8 is the label-exclusion argument written in full. If a combined label is missing on U, it is missing in every A(W) obtained by an open immersion into a component of U. Each of these same affine schemes W also embeds openly into a component of V. The item hypothesis then makes that center a unit on the lifted W in D. `lem-weil-pbc-affine-opens-basis` makes these W cover V, while the label was already absent over U. The global center of D would be empty, contrary to the hypothesis. The proof works with the original uncontracted index and thus does not identify two levels before checking prior deletions. No hypothetical open immersion U -> S is used when U is a disjoint union.

Step 9 uses the ideal uniqueness already proved in Step 5 and the canonical common-refinement comparison of `prop-nagata-global-blowup-cover-independent`. This yields the cover comparisons level by level. Triple comparisons are tested against the same tower from the union of three covering families, not inferred solely from isomorphism classes. Step 10 uses the item's open compatibility for A(X), with X in its domain; label sets on either side are the union of the chart-label sets by the same nonempty-center argument. Padding then identifies all chart ideals and the same ordinary comparison identifies the global blowups. The uniqueness claimed is the canonical uniqueness required by the affine-cover pullback condition.

I tested length zero, the empty scheme and empty cover, repeated or empty charts, disconnected inputs with centers supported on one component, consecutive missing labels on a chart, and proper principal centers whose morphisms are identities. A label can be absent on an individual chart; the argument only forbids its absence on an entire family covering S. For a nonseparated test, two affine lines with doubled origin have an affine-refinable overlap, and the proof uses only its opens and their lifted opens; it does not require separatedness or affine intersections. More generally the overlap itself may be nonaffine throughout. There are no new statements to test or sources to certify for new nodes.

No step exceeds 2000 characters. The long substantive arguments remain the item's own synchronization, center descent and comparison clauses. There is no hidden independent lemma moved into a new node. I corrected the draft's potential shortcuts by explicitly proving domain membership, distinguishing the base-change theorem from its map definition, writing the kernel check for coherence, and testing missing labels on both covering families. I found no statement error requiring `STATEMENT-DISPUTED` and changed no hypothesis or conclusion.

## Unfinished work

No mathematical part of the stage-1 split remains. The required dry run and direct delivery follow this report; their output determines the final disposition.
