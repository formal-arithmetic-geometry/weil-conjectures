# Stage-1 delivery: lem-sfb-pullback-ring-open-immersion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pullback-ring-open-immersion.json: statement, split into five steps; no Mathlib match for the complete item.
- citations.json: six verbatim quotations, one for every step/node citation.
- searches.jsonl: actual search-command log, retained unmodified.
- report.md: this report.

0 new nodes; 0 new Mathlib leaves. Existing Mathlib leaves supply exactness of localization, principal localization open immersions, and the injective local-source criterion.

## Attachments

None. Searched the live project under lean/WeilConjectures for the item tag, fibre/pullback-ring terminology, localization and Tags 01Z8/01Z9. The relevant project declarations in WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean are Stage.isLocalization_away (line 704) and Stage.isOpenImmersion_toSpec (line 744). Read their surrounding definitions and proofs: they depend on ExtensionData and a Stage carrying additional generation, covering, affine and qcqs data. They do not quantify over the arbitrary ring diagram of this item and do not state all its clauses. They are not an attachment for this item. No compiler or Lean file was used or written.

## WANTED

None. All source material needed is present locally.

## What changed and what was wrong

The imported node had a correct, precise statement and no proof. Its Stacks places were correct: 01Z9 is limits-lemma-diagram, and 01Z8 is more-algebra-lemma-diagram-localize, verified against tags/tags. The proof now expands the cited localization lemma using the already existing exactness-of-localization node. It also supplies the global injectivity argument needed to assemble the principal-open isomorphisms into one open immersion; merely saying that an open immersion is local on the source would omit this hypothesis.

The statement, statement dependencies, source, creation record and inherited blueprint chain are retained. The blueprint ancestor tool prints None for this item's inherited chain; no new node requires a new ancestor. The existing precise from.place is preserved. Searches of the imported blueprint for 01Z8 and 01Z9 returned no matches; a search for open immersion and a search for localization were also run to check the broader blueprint. Read the latest direct-images proof (3) and the chapter/unit records; this remains the auxiliary ring calculation below the prescribed-open approximation route, with no change to the unit or chapter.

Mathlib queries used the mandatory msearch.py only, and their actual records were added to mathlib_searches. Two Loogle patterns were rejected because the service did not recognize IsPullback (one qualified, one unqualified); these are recorded as unavailable, not negative evidence. The valid replacement query CommRingCat, IsLocalization.Away returned principal-open/localization statements. LeanFinder was queried in two phrasings. LeanSearch found the ordinary ring pullback construction and induced localization maps. Read CommRingCat.pullbackConeIsLimit (Constructions.lean:463) and isPushout_of_isLocalization (line 162): the former only constructs the unlocalized pullback, and the latter is a pushout theorem. Neither is the localization-of-a-pullback result needed here. The two grep searches found no pullback-localization theorem. No false claim of absence relies on the rejected Loogle queries.

## Not duplicates

No new nodes were created. Existing nodes with the same tags were inspected, particularly lem-sfb-ring-fibre-product-spectrum and lem-sfb-fibre-product-spectrum-topology. Both impose surjectivity on one of the original homomorphisms and cannot justify this item's arbitrary-map assertion. Reused existing nodes instead of making a more general localization-of-pullbacks node: the exact-sequence proof already fits here with explicit fraction identifications.

## Review by NX

I read the full statement and proof of Stacks 01Z9 in limits.tex and the full statement and proof of its input 01Z8 in more-algebra.tex. I also read Algebra 00CS (proposition-localization-exact) and Schemes 01I3 (lemma-standard-open-affine), including their proofs. The chapter and unit records and the current blueprint direct-image proof were read as route context. There are no new nodes needing an additional source review.

Step 1 uses only the ring diagram in the item's hypotheses. I checked P-linearity of the difference map: the two actions on R coincide precisely because each element of P is a compatible pair. Its kernel is P by definition, and the inclusion is injective. No surjectivity of either original map is being inferred.

For step 2, I opened lem-weil-pbc-localization-module-exact and checked that its statement gives exactness for any multiplicative subset and any exact pair of modules, without a surjectivity assumption. It is applied to both adjacent exact pairs, so it supplies injectivity as well as the kernel equality. I also opened def-weil-ring-localization-away; its fraction equality is exactly the criterion used for the coordinate-localization formulas and the common-denominator formula for a finite direct sum. These are elementary coordinate identifications written out in this step, not a hidden claim that arbitrary limits commute with localization. The resulting ring identification respects both coordinate projections because those are the localized maps in the exact sequence. Its length is below 2000 characters.

Step 3 cites no extra theorem: it explicitly gives and checks the inverse to projection from the localized fibre product. The hypothesis used is the natural map B_g -> R_d being an isomorphism, not some abstract isomorphism of the two rings. Consequently the output map to (Rprime)_f is the specified localized projection.

For step 4, I opened lem-weil-pbc-principal-localization-open-immersion: it states an open immersion with image D(f), hence, with def-weil-open-immersion (also read), an identification as schemes, not just a homeomorphism. I opened def-weil-affine-spectrum and checked that it states contravariant functoriality, so it takes the inverse ring maps in step 3 to inverse scheme maps. The fraction formula verifies the commuting square. The inverse-image equality is derived from contraction of prime ideals, so it does not require a separate base-change theorem or any ring-map surjectivity.

For step 5, I opened lem-weil-pbc-open-immersion-injective-local-source and read its exact hypotheses. The proof establishes the required global injectivity before applying it: two points with the same image are forced into the same U_l by the inverse-image equality, and then the chart isomorphism separates them. Each U_l is open in Qprime, and each restricted composite is an open immersion by step 4, so the local hypotheses match the cited statement. The image is exactly the union of the V_l by surjectivity of every chart isomorphism. This step does not use the false criterion that all locally open-immersive maps are automatically open immersions.

I checked the small cases: an empty family gives the empty open in both spectra and a vacuous local criterion; g=f=0 gives zero localized rings and empty charts; nilpotent elements likewise give empty charts; g=f=1 forces the expected graph-pullback identification when s is an isomorphism; zero rings are permitted by the fraction relation and all cited statements. The proof uses no domain, nonzero-ring, Noetherian or finiteness assumption beyond the item's finite list. For every step I checked that every non-elementary input is a cited statement. The only steps marked elementary are construction of the exact sequence and the explicit inverse after cancellation. No step exceeds 2000 characters, and no new node is a disguised clause of the item.

I checked delivery-errors B through E: self-contained statements and source tags, exact citations (all six full quoted statements copied verbatim into citations.json), no citation of a proof in place of a statement, no off-unit unresolved tools (the reused theorem nodes are Mathlib leaves), no cycle introduced, and no assertion of finite limits commuting with localization without the exactness argument. No SGA source was used.

## Unfinished work

None in the authorized stage-1 scope. The required server dry run and direct delivery are the final checks for this split.
