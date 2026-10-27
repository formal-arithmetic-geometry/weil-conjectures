## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fibrewise-module-flatness-criterion.json: existing statement split into five steps; no Mathlib match for the whole criterion.
- citations.json: 13 literal quotations, one for each step/node citation.
- No new nodes and no new Mathlib leaves. The statement and all statement dependencies are unchanged.

## Attachments

None. Searches for the exact blueprint tag, fibre/fiber flatness, and the local flatness criterion in lean/WeilConjectures found no declaration proving this entire module assertion. The existing FlatOfFlatClosedFiber declaration is an algebra input with the stronger essential-finite-presentation hypothesis on the middle ring. RelativeFlatOfStalks and AffineChartRelativeFlatCriterion compare affine section flatness with stalk flatness; they do not state the fibre criterion. The structure-sheaf criterion does not handle an arbitrary finite-presentation module.

## WANTED

None. All sources used are present in literature/stacks-project.

## Problems found and corrected

The item's statement matches Stacks 039C, theorem-criterion-flatness-fibre, implication (1) to (2). No statement correction or STATEMENT-DISPUTED is required. The initially empty proof needed the finite-type approximation: applying 00R7 directly to the target stalk would incorrectly assume it essentially finitely presented. Conversely the existing approximation-rigidity node assumes the source ring C itself flat over R, whereas this item assumes only M flat over R; I did not cite that specialization.

I retained the inherited blueprint ancestry, including its null from.node, because tools/blueprint_refs.py ancestor reports None for this existing chain. The current latest blueprint proof is sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). It now assembles direct image along a compactification rather than spelling out the older alteration expansion. The pre-existing chain through the relative module flat locus is recorded explicitly in split_report.blueprint; I changed no chapter or unit route. Whole-blueprint searches for flatness, fibrewise, 039C and 05UV found no blueprint statement matching the item.

The final identification T ≅ B uses faithful flatness of M, obtained from its finiteness over C and Nakayama. It does not infer faithful flatness from nonzero flatness alone and does not require M finite over T. This short argument replaces the longer stabilization of finitely generated ideals in the proof of 05UV while retaining the same approximation and 00R7 inputs.

## Not duplicates

No new nodes. In particular I reused lem-sfb-fibre-flatness-compatible-stalk-data, lem-sfb-finite-type-local-closed-fibre-approximation and lem-weil-pbc-criterion-flatness-fibre. The existing lem-sfb-fibrewise-flatness-criterion is only the structure-sheaf specialization, not a replacement for this module assertion.

## Review by Q18

I read more-morphisms.tex, Tag 039C, theorem-criterion-flatness-fibre, its statement and proof; algebra.tex, Tag 05UV, lemma-criterion-flatness-fibre-fp-over-ft, including its approximation by finitely generated ideals; and its essential-finite-presentation input Tag 00R7, lemma-criterion-flatness-fibre. The proof is confined to the forward implication and does not use the openness clause or a Noetherian hypothesis. No new node needs a separate source review.

For step 1 I read the full statements of lem-sfb-fibre-flatness-compatible-stalk-data and lem-weil-pbc-stalk-finite-presentation-of-local-presentation. The former explicitly gives the local scalar tower, essential finite presentation of C, essential finite type of B, and compatible quotient fibre rings under exactly the item's geometric hypotheses. The latter takes a supplied finite local presentation, supplied here by the hypothesis on F, and proves finite presentation of its stalk. I checked modules.tex Tag 01CP, lemma-stalk-internal-hom, whose proof explicitly obtains the finite source-stalk presentation. No flatness of C over R is inferred.

For step 2 I read lem-weil-pbc-module-stalk-pullback and lem-weil-pbc-tensor-over-quotient-ring, not just their titles. The first is the ordinary O-module pullback formula of sheaves.tex Tag 0098, lemma-stalk-pullback-modules, not the unrelated etale inverse-image stalk formula. The second gives the quotient tensor isomorphism; algebra.tex Tag 00DF, lemma-tensor-product-exact, applied to J → C → C/J gives it. The compatible-stalk-data statement also gives the quotient formula for the fibre morphism. The written map m tensor [c] ↦ [cm] verifies the resulting B/m_R B-action, and the equality (m_R C)M = m_R M is explicitly justified. Thus the given flatness is over the correct quotient target ring.

For step 3 I opened the approximation and 00R7 node statements. The approximation needs only essential finite type of R → B and gives a surjective LOCAL map T → B and the canonical closed-fibre isomorphism. Its source is the polynomial-localization construction of 05UV. The local composite T → C, the two essential finite presentations over R, finite presentation of M over C, nonzero M, R-flatness, and the exact quotient action are each checked in the step before applying 00R7. The change along the quotient-ring isomorphism merely relabels the same tensor balancing relations, as in the definition of flatness, which is also cited.

For step 4 I read lem-weil-pbc-nakayama-local-generators and lem-weil-pbc-flat-module-faithfully-flat-maximal-ideals. Their statements say respectively that a submodule equals a finite module when its residue image is everything, and that a flat module over a local ring with nonzero maximal-ideal quotient is faithfully flat. Taking the zero submodule in the first proves M ≠ m_C M; locality then gives M ≠ m_T M. This uses finite generation only over C. I checked algebra.tex Tag 00DV, lemma-NAK, and Tag 00HP, lemma-ff, including implication (4) to (1). Thus these are module results, not ring-only faithful-flatness criteria.

For step 5 I read def-weil-pbc-flat-ring-map, def-weil-pbc-faithfully-flat-ring-map and def-weil-flat-morphism. The kernel cancellation is written out from those definitions: K tensor M injects into M but maps to zero, and exactness reflection for 0 → K → 0 gives K = 0. This is a short elementary application of the definitions, not an uncited general flat-descent theorem. The last scalar transports use the actual inverse of u and the stated R-algebra compatibility. Each conclusion is exactly the original one, including q flat at y. I checked that the inclusion K → T is T-linear and its tensor map is precisely multiplication by an annihilator of M.

I checked delivery-errors B through E point by point: there are no newly introduced standalone statements, duplicate nodes, or disguised clauses of the item; every non-elementary input is a node whose statement I read. All 13 quotes in citations.json were checked as literal substrings of those statements. The proof dependencies equal the union of uses. Every step is below 900 characters, hence no step triggers the 2000-character hidden-lemma audit. Generic off-unit stalk and algebra tools are declared in split_report.tool_uses; they support this unit's existing route.

Small cases checked: over a field base, the fibre criterion reduces to the given module flatness and automatic base flatness; for identity maps and a nonzero finite free module it recovers the hypotheses; empty schemes have no chosen x; the zero module is excluded exactly where Nakayama/faithful flatness needs nonzero M. Dropping this exclusion would falsely force q flat for the zero module on any nonflat finite-presentation scheme. The maximal ideals may vanish (field local rings), in which case M/m_T M = M ≠ 0, so the same proof works. Non-Noetherian rings are allowed throughout: only the already established finite-type approximation and 00R7 handle that difficulty.

Mathlib searches were made through the prescribed msearch.py command: LeanFinder with two phrasings, LeanSearch, Loogle, and two source grep patterns. I read their hits. They return localization tests, flat base change, local-ring faithful flatness, smoothness and the equational criterion, not the requested criterion. I also read FormallyUnramified.flat_of_restrictScalars: it requires an unramified algebra, which is absent here. All Q18 queries are recorded exactly in searches.jsonl and the item; earlier search records are retained. No Lean was written or compiled and no repository or launcher file was changed.

## Unfinished work

None in this one-level split. The supporting nodes keep their own independent proof obligations.

## Validation

Server review_split passed before delivery: PASS, 0 new nodes. Required full delivery dry run follows this report.
