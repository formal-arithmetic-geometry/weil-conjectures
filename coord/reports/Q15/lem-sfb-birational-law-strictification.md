# Q15 stage-1 delivery: lem-sfb-birational-law-strictification

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-birational-law-strictification.json: item, split with six proof steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-product-projection-density-shrink.json: new statement-only lemma, unsplit; Mathlib searches found no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-fibrewise-dense-open-base-change.json: new statement-only lemma, unsplit; Mathlib searches found no match.
- citations.json: verbatim statements for every cited node at every proof step.
- searches.jsonl and search-results.json: actual search log and the returned results retained for inspection.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for birational group law / strict birational / relative density terminology. No project declaration states the item or either new lemma. Existing rational-map declarations concern ordinary dense domains and do not give this relative strictness assertion.

## WANTED

WANTED: Bosch–Lutkebohmert–Raynaud, Neron Models, 2.5 preliminaries and Lemma 1, printed pp.55–56; 5.2 Definition 1 and Proposition 2, printed pp.115–117; for this item and both new nodes. No local copy was found in literature. I read the primary scan through the web reader at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf (PDF pp.61–62,121–123). No source was downloaded into the repository or patched into the launcher. The item is explicitly marked proof_origin.by=agent, as required for an unavailable local source, even though its argument follows the primary scan. No SGA source is used.

## What needed correction

The item was statement-only, with no proof, and no earlier sandbox split existed. Its mathematical statement agrees with BLR 5.2 Proposition 2 and its useful generic-fibre refinement. No statement dispute arose and no hypothesis or conclusion was changed.

The generic-fibre assertion is not an explicitly separate clause of Proposition 2. It follows from the proof's choice of charts and removal of bad projection-fibre loci: group translations are isomorphisms on the entire generic fibre, the charts can include it, and the closed bad loci then lie entirely in the special fibre. This reasoning is now explicit in step 6 and in the projection-shrinking lemma.

During self-review I corrected the fibre-product notation in the shrinking lemma: the pullback of Z at a parameter is over X using the restricted projection, not a pullback over P with a nonexistent map Spec kappa(a) to P.

The inherited blueprint reference has from.node=null. The authorized ancestor command also reports None; I retain that fact and the existing ancestry chain, and give precise BLR places for the new nodes. The latest blueprint's sk-thm-sf-ctf-stability concerns constructible six functors and has no birational-law statement. This item is a lower supporting construction already introduced in the Neron-model route, and the split does not change that route.

## Unfinished work

No part of the assigned one-level split remains. Both new lemmas are deliberately statement-only future items. There are no Mathlib leaves. Their proof routes, for the next worker: for projection shrinking use BLR 2.5 Lemma 1(a) to construct the two bad constructible loci, exclude their closures from X as in 5.2 Proposition 2, and retain the generic fibre when Z_F=P_F; for smooth fibrewise density use BLR 2.5 preliminaries and Lemma 1(b), locally if quasi-compactness is needed. The argument belongs here rather than inside their statements.

## Not duplicates

The whole DAG and the imported blueprint were searched before either node was written. Blueprint searches included birational, rational map, fibrewise density, fibrewise dense, projection density, projectionwise and schematically dense. I also searched the DAG titles and statements for the relative density concepts, the BLR places, and likely uniqueness tools. No imported blueprint node states either new result.

- lem-sfb-product-projection-density-shrink vs lem-sbc-generic-open-fibre-density: the latter only spreads ordinary density from the generic fibre of one irreducible base; it does not give simultaneous density above every surviving parameter over both fibres of a trait, nor preserve an entire generic fibre of X.
- lem-sfb-product-projection-density-shrink vs lem-sbc-generic-open-geometric-fibre-density: the latter requires geometrically irreducible generic fibres and is a generic-base shrinking theorem; our lemma allows disconnected smooth fibres and controls two projections over the original trait.
- lem-sfb-product-projection-density-shrink vs lem-sfb-birational-law-strictification: the new lemma contains no multiplication, universal translation, or strict law, and proves none of the cross-density conditions for V prime or W prime. Those arguments stay in steps 3–4 of the item.
- lem-sfb-smooth-fibrewise-dense-open-base-change vs lem-trf-schematic-density-generic-fibre-open: the latter spreads schematic density after shrinking an irreducible base; the new lemma starts with density on every fibre of a smooth morphism and asserts density and schematic density after arbitrary base change.
- lem-sfb-smooth-fibrewise-dense-open-base-change vs lemma-nagata-dense-flat-pullback: the latter assumes a schematically dominant qcqs map and flat base change; the new lemma starts from fibrewise topological density under a smooth morphism and allows an arbitrary change of its base.
- lem-sfb-smooth-fibrewise-dense-open-base-change vs lemma-nagata-reduced-dense-image-schematic: that node assumes a reduced target and a dense qcqs map. Our target after arbitrary base change can be nonreduced, and the relative smooth-fibre hypotheses supply the required schematic density.

## Review by Q15

I read the standing stage-1 brief, the whole B–E checklist in both copies of delivery-errors.md, the fixed chapter/unit contract, GOAL.md, the item's ancestor and neighbouring group-envelope/strict-realization nodes, and the latest unit blueprint. I compared the item against the primary BLR scan, 5.1 Definition 1, 5.2 Definition 1 and the complete proof of Proposition 2. For the two new nodes I read 2.5's relative-density preliminaries and Lemma 1(a),(b), and the paragraph defining the two bad loci in 5.2 Proposition 2. The two new statements are independent inputs rather than repackaged conclusions of this item.

Step 1 uses the actual smooth-base-change clause (2) of lem-pc-proper-base-change, not its properness clause; lem-trf-smooth-composition gives smoothness of the square. I opened both statements. The new smooth-density lemma supplies scheme-theoretic density on overlaps. I opened lemma-nagata-ext-scheme-theoretically-dominant-separated and checked that its statement explicitly gives equality of two relative morphisms into a separated target on a scheme-theoretically dense open. These inputs justify the common translation charts. The domain/image restrictions and finite intersections are elementary properties of isomorphisms and dense opens, written out.

Step 2 uses exactly the new projection-shrinking statement, with Z=U intersection V intersection W and the same smooth separated finite-type X. Its nonempty fibres and field/trait base meet every hypothesis. The new smooth-density lemma is applied to A inside X to pass to kappa(a). It explicitly allows arbitrary base change and disconnected fibres. Thus no geometric irreducibility or algebraically closed residue field is being smuggled into the slice computations.

Step 3 is an explicit elementary calculation with the slice isomorphisms: intersect a dense domain with A and the inverse image of A in a dense image, obtaining U prime dense for both projections, then V prime dense for the first and W prime dense for the second. Step 4 explicitly checks the two conditions BLR puts in the diagram on p.117. The level set m=a is simultaneously isomorphic to the V slice with second coordinate a and to the W slice with first coordinate a. The inverse images of the two A cuts intersect densely in this same level set. This proves W prime dense for the first projection, and the symmetric calculation proves V prime dense for the second. There is no unproved group realization or extension theorem in this argument. Those statements would depend on this item and would be circular.

Step 5 merely identifies the six established conditions with the stated definition of strictness and inherits associativity. The shrinking lemma includes that the selected A is a smooth separated finite-type open, avoiding an implicit finiteness or Noetherian argument at assembly. Step 6 writes both inverse translation formulas on the generic group fibre. It cites the schematic-density and separated-uniqueness statements already checked for gluing the charts, and the exact preservation clause of the shrinking lemma. I checked that the generic fibre is open for a trait, so adjoining it to the charts is an open enlargement; no properness or completeness is needed.

I tested the new lemmas on an empty scheme, zero-dimensional and disconnected smooth schemes over a field, a smooth trait model with multiple special components, and the case Z=P. They allow empty fibres; no argument chooses a single generic point for all components. In the extra trait case Z_F=P_F, all bad points are special and their closure remains special. I also checked that ordinary density alone, without the smooth-relative hypotheses, would not justify arbitrary schematic-density base change, so those hypotheses are explicit. No step is longer than 2000 characters; the only extracted arguments are genuinely separate law-independent scheme lemmas. Every non-elementary assertion used is a cited node, and citations.json quotes each node verbatim.

All five search calls per node were run using msearch.py, including a second natural-language phrasing. I read the returned signatures. The results are ordinary dominant morphisms and partial-map dense domains, smoothness constructors, open-map properties and Weierstrass groups; none states the relative density or birational-law conclusions. Loogle and grep returned no hits for the selected expressions. I recorded actual output rather than inferred or invented declarations. The three cross-unit inputs are generic scheme tools, declared in split_report.tool_uses with reasons; they do not replace the unit's route.
