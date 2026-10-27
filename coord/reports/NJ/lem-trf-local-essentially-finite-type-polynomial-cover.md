## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-local-essentially-finite-type-polynomial-cover.json: statement, split; no exact Mathlib match. Six proof steps use existing nodes only.
- citations.json: ten step/node entries with verbatim excerpts of the cited statements.
- report.md: this report. searches.jsonl is maintained by the required search command.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searched lean/WeilConjectures for the blueprint tag and for EssFiniteType, essentially of finite type, and essentially finite type. No project declaration states this item. The occurrences in FieldHypersurfaceIntegralPresentation and LimitTowerEssentiallyFinitePresentation are different statements, not attachments.

WANTED: none.

The initial item was statement-only. Its statement is correct and unchanged; the proof was missing. No statement dispute, dependency correction, unit-route change or source error was found. No work remains unfinished.

## Sources and route

Read Stacks more-morphisms.tex, Tag 0GSG, lemma-mod-injective-valuation-ring, especially the first reduction paragraph beginning “By assumption we can write B as a quotient”. That paragraph supplies the construction, but suppresses the elementary prime, fraction-surjectivity and locality checks. Read algebra.tex Tags 00QM (definition-essentially-finite-p-t), 00F3 (definition-finite-type), 00CP (proposition-universal-property-localization), 07BI (definition-local-ring and the following localization paragraphs), and 00E9 (lemma-characterize-local-ring). Verified these tag/label pairs in tags/tags.

Read the chapter and unit records sec-trace-formula and sk-i-curve-zero, then the latest blueprint sk-i-curve-zero/_section.md and lem-trf-local-term-locality.proof.md under literature/blueprint/latest. The item is a commutative algebra tool below the inherited semistable-alteration/nearby-cycle branch, through the flatness input to 0GSJ/0GSI and the finite-module lemma 0GSG. It does not replace a step of the unit. Only the proof of this item changes. All six cited nodes are existing Mathlib leaves; no off-unit non-leaf tool approval is needed.

## Searches and reuse

Searched the whole DAG statements for localized polynomial surjections, universal properties, local-ring units and polynomial finite presentations, and inspected the statements of the six dependencies below. The ring-localization universal property and local-ring unit criterion are already nodes, so neither is recreated. Also read the existing localization-of-localization and localization-at-prime-of-quotient nodes; the direct fraction construction avoids invoking those stronger facts.

Ran tools/blueprint_refs.py ancestor for this item, and blueprint searches for localization, local ring and essentially finite type polynomial. The last has no matches; the broader searches supply no blueprint node stating the local polynomial cover. The inherited blueprint.from.place is already specific and same_as remains []. The whole-DAG search for essentially finite type polynomial surjections also found only this item and unrelated Popescu coefficient constructions.

Ran the mandatory msearch.py tools for the item: LeanFinder twice with different phrasings, Loogle, LeanSearch and grep, all successful, all recorded in searches.jsonl and appended exactly to mathlib_searches. Read returned hits. Algebra.essFiniteType_iff_exists_subalgebra and EssFiniteType.cond describe finite subalgebra localizations; EssFiniteType.of_surjective and the quotient instance preserve essential finite type. Neither constructs the local polynomial cover. IsLocalization.mapₐ_surjective_of_surjective (Localization/Algebra.lean:122-124) presupposes compatible localizations and does not supply the prime or identify its localized target with B. Formally-unramified local-ring results require extra hypotheses absent here. None is an exact match or one-line specialization of the item. Read EssentialFiniteness.lean:40-78, 161-166 and 223-249, and the localization-surjection signature. The original item's searches are preserved as history.

## Not duplicates

No new nodes are created, so there are no new/existing same-tag pairs.

## Review by NJ

I checked the construction against the actual first reduction paragraph of Stacks 0GSG, rather than using its main valuation-ring theorem. In particular the cover does not require the base A to be a valuation ring, a domain or Noetherian: only the local essentially finite type hypotheses are used. I read each cited node's statement in full and wrote citations.json from those statements, not their proofs or titles.

Step 1 uses def-weil-pbc-essentially-finite-type-algebra for C, W and the A-algebra isomorphism, and def-weil-pbc-finite-type-algebra for the finite polynomial surjection. Both statements explicitly give exactly that data. This is unpacking two definitions, not an extra existence theorem. The composite on constants is the prescribed A-algebra structure.

Step 2 uses lem-weil-pbc-local-ring-unit-criterion, whose statement explicitly equates the complement of the maximal ideal with units. Its local-ring hypothesis holds for B. The prime inverse image is proved directly by multiplication and properness; the elementary fact that a quotient by a maximal ideal is a field suffices. It is important to pull back the maximal ideal of B under P to B, rather than choose an arbitrary prime of P.

Step 3 uses lem-weil-pbc-ring-localization-universal-property for the extension and its fraction formula, with U = P minus q. Step 2 has verified its unit-image hypothesis. def-weil-pbc-localization-at-prime supplies exactly this fraction ring. Checking constants proves the required A-algebra compatibility. This is the one step labelled non-elementary: it applies the cited universal property.

Step 4 again uses the fraction data in def-weil-pbc-essentially-finite-type-algebra and the local-ring unit criterion. Surjectivity of the map to C is part of the chosen presentation from step 1; lifts f and s therefore exist. A denominator w in W becomes a unit, even when C has zero divisors. Its polynomial lift consequently lies outside q. The exhibited fraction f/s maps to the arbitrary b. No unproved localization-surjectivity theorem is hidden here.

Step 5 uses the explicit local-ring/maximal-ideal assertion in def-weil-pbc-localization-at-prime. The ideal generated by q maps into m_B because each generator does. Its containment in the proper inverse-image ideal and its maximality give equality, without an additional ideal-correspondence theorem. Pulling this equality back to A uses precisely the locality hypothesis on phi and the composite equality from step 3. Both required inverse-image equalities are thus established, not merely claimed from the word “quotient”.

Step 6 uses the presentation data of def-weil-pbc-finitely-presented-algebra with no relations, and the localization supplied by def-weil-pbc-localization-at-prime. The identity polynomial presentation has zero kernel and empty relation list. This proves the essential-finite-presentation clause exactly in the sense already spelled out in the item's statement. It does not assert B itself is essentially finitely presented, which could fail if the quotient ideal is not finitely generated.

I checked B a field, the identity local map, a non-Noetherian base, quotients with infinitely generated kernel and n = 0. None requires a finite kernel or an injective C to B. For example B = A/I with I inside the maximal ideal admits the n = 0 cover A localized at m_A, mapping onto B; its cover is essentially finitely presented independently of I. Zero rings are excluded by having a maximal ideal. Empty generator and relation lists are permitted. Each new proof step is below 600 characters, so no step exceeds the 2000-character hidden-lemma review threshold.

Against delivery-errors B–E: there are no new unsplit nodes or undefined added notions; TeX has single logical backslashes; source tags and labels are checked; no leaf is claimed without a matching declaration; all non-elementary inputs are named existing nodes; all ten quotations are literal substrings; there is no new node restating a clause, no proof moved elsewhere, no circular construction, and all local/unit hypotheses are checked at the point of application. The only substantive repair was to supply the previously absent proof and its explicit fraction and ideal arguments.
