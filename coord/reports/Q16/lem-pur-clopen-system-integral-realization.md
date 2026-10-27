# Worker report — Q16

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-clopen-system-integral-realization.json`: the item, statement unchanged, eight proof steps, status split; Mathlib verdict no match. No new nodes and no Mathlib leaves.
- `citations.json`: a verbatim statement for every node cited by each proof step. Full statements retain the hypotheses as well as the used clauses.
- `searches.jsonl`: actual Q16 search log, retaining every completed query. `prepare.py` is the sandbox-only preparation script.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id, clopen systems, integral realization, exceptional operations and open/closed restrictions. There is no declaration giving this entire item without sorry. The existing ordinary clopen-idempotent and pushforward declarations do not construct this exceptional coefficient-system comparison. No Lean was written and no compiler, Lake or build tool was run.

## WANTED

None.

## Findings and corrections

The sandbox initially had dispatcher markers only. I copied the live unsplit item, preserving all fields, statement, inherited search records, citations and source references. There was no repair note for this item and no previous split/report requiring an initial dry run. The source package is Q121's retained old steps 8–9, which I read in `coord/reports/Q121/lem-pur-finite-clopen-exceptional-restriction.md`. No mathematical statement correction is necessary. The proof fills two details that were compressed there: transport of the specified insertion and exceptional counits, and commutation with the TOTAL derived limit rather than an unspecified triangulated cone. The integral pullback identification uses the existing canonical open-completed-restriction theorem; the bare completeness definition alone explicitly does not select a natural reconstruction map.

## Sources and route

I read GOAL.md, the three levels of SETUP.md, stage-1 and worker rules, delivery-errors B–E in both copies, `dag/chapters/sec-smooth-purity.json`, and `dag/units/sk-def-purity-conv.json`. This unit has no proof steps and refers to the six-operations conventions. The current ancestor source is `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md`: its final invertibility sentence is the place served by the finite-clopen component expansion. This item is not the unit key statement, and no unit record changes.

The proof is honestly agent-written: the blueprint sentence does not itself prove the system compatibility. I read Stacks `proetale.tex`, Tag 09AF (`lemma-jshriek-comparison`, around line 5076), whose proof identifies the open extensions by their right adjoints; `sites.tex`, Tag 04TS (`lemma-mapping-property-glue`, around line 5909), giving sheaf gluing; `sites-cohomology.tex`, Tag 0941 (`lemma-derived-limit-is-ok`, around line 5067), whose proof calculates the total limit using a K-injective tower; and `derived.tex`, Tag 08BJ (`lemma-adjoint-preserve-K-injectives`, around line 9857), including its exact-left-adjoint argument. I also read Bhatt–Scholze, printed pp.24–25, Definition 3.5.2 and Lemma 3.5.7: actual completeness uses the natural map and sequence-site systems, agreeing with the canonical comparison needed here. No SGA source is used.

## Searches and reuse

I searched the whole DAG by clopen, coefficient-system, site comparison, completed restriction, strict tower, reconstruction, the relevant tags and declaration names, opening every cited statement. `tools/blueprint_refs.py ancestor` identifies `def-pur-section-invariant`; whole-blueprint searches for clopen, coefficient system and comparison pullback found no duplicate of the entire item. Existing notions, comparison lemmas and strict-system reconstruction statements were reused; no new node was necessary.

The five actual Q16 searches are in the item with exactly their logged tool/query text: LeanFinder for the whole system/exceptional comparison, Loogle for sheaf-module restriction, Mathlib grep in `CategoryTheory/Sites`, LeanSearch for the total-limit/clopen comparison, and a second LeanFinder phrasing for complete sheaf complexes and reduction towers. The first four results were read directly. The final search completed during the provider interruption: its completed log lists the actual hits, which I read before recording it, and no search or delivery mutation was repeated. The hits are ordinary presheaf restriction, scheme restriction, etale algebra presentations, profinite limit projection identities and restrictions/truncations of homological complexes. None gives this actual exceptional-system comparison or its integral realization. The inherited Q121 searches remain untouched.

## Not duplicates

No new node is created. In particular the finite-clopen decomposition already supplies the exact product and derived-limit statements; the existing open-completed-restriction identification already supplies the canonical integral pullback comparison. These were cited rather than reintroduced as sublemmas.

## Review by Q16

I checked the proof with the sources and every cited node's statement open. This is my direct-delivery self-review, not an independent second-reader claim.

Step 1 takes the inverse-image square exactly from `lem-weil-pbc-comparison-pullback`, exact levelwise system inverse images from `lem-pur-coefficient-system-derived-comparison`, and descent of transformations and inverses from `lem-weil-pbc-localization-universal-property`. The transition square is checked before localization, by applying the same underlying pullback comparison to a semilinear arrow and its scalar endomorphisms. It does not infer a system arrow from derived level maps.

Step 2 uses the actual system rho and its finite counit evaluations stated by `lem-pur-clopen-counit-adjoint-comparison`. The system-derived-comparison node explicitly supplies evaluation of the derived direct image and the units/counits. Thus both sides have the correct derived strict-system source and target, and sigma and its inverse are whiskered actual arrows.

Step 3 checks the normalization of the open comparison using `lem-sf-open-comparison-unit-normalization`, which actually states its unit equation. The common-compact-support node identifies zero insertion with open extension, with identity normalization; the strict-system-support node states the evaluated insertion maps and strict compositor; and the clopen-derived-decomposition gives the fully faithful product equivalence used to check component maps. `lem-amb-compact-support-site-comparison-open` explicitly states that its J is the composite of the canonical open and proper comparisons. Both chosen compactifications have exactly the same p, so naturality of its proper factor applied to the open compositor gives the required equality. This step is not using the target-open exchange clause as a source-open theorem. It uses only the stated construction of J and naturality, with the sectionwise identity/zero computation written out.

Step 4 uses the bounded-below etale-origin Hom bijection of `thm-sf-ambient-adjoint-class`, not an unrestricted pro-etale adjunction. Its dimension and Noetherian hypotheses are supplied verbatim by `lem-pur-clopen-common-compact-support`. The exceptional definition says its finite adjunction is the transported one. The clopen-counit-adjoint-comparison statement gives uniqueness under exactly the displayed counit equation, so transporting that equation identifies the evaluated map. No finite Tor hypothesis or separation of Y over k was added. The definition provides constructible typing and etale origin for the stated inputs.

Step 5 uses the definition's actual reduction/system/forgetful composite, the coefficient projection-preserving clause of `lem-pur-clopen-ringed-module-gluing`, exact descent, and the reduction compatibility of the finite-clopen decomposition. Both scalar-forgetting orders have the same completed-ring action through the same finite projections, the same transitions, and the same action on maps.

Step 6 takes the exact product equivalence on module categories and its component zero insertion from the finite-clopen decomposition. Applying these functors levelwise gives the exact left adjoint on tower categories. The general right-adjoint-preserves-K-injective theorem explicitly assumes an exact left adjoint, which is now available. The ringed-strict-tower-homotopy-limit statement explicitly computes the TOTAL derived limit by a K-injective tower resolution. Therefore restricting that resolution computes the target total limit as well. Ordinary limits are componentwise compatible families. The resulting comparison is natural for tower maps and preserves projections, with no exactness-of-products assumption imported into the total-limit argument.

Step 7 takes the exact defining functor formula from `def-weil-exceptional-inverse-image` and the canonical natural kappa from `lem-pur-open-completed-restriction-identification`. The latter states compatibility with strict transitions, augmentations and finite projections and applies to every integral constructible K. Here K is the integral exceptional output, whose constructible typing is part of the already specified operation; no separate adjunction or effectivity lemma is silently assumed. The pullback definition fixes precisely the completed finite-reduction limit that kappa identifies. This removes the ambiguity of trying to select a natural morphism merely from the Roos-triangle definition of completeness.

Step 8 is elementary: functors preserve the two inverse equations and the naturality square. The two cited clopen nodes explicitly give the zero-category empty-factor and empty-product conventions. For one component equal to X the comparisons are the identity normalizations; for an empty component all maps are the unique zero map; for the empty cover there is no component comparison. All n are positive, all rings are finite quotient coefficient rings, and no smoothness, section or invertibility hypothesis is introduced.

For B, no statement-only new node or new definition is needed. TeX and blueprint ancestry are retained, and exact searches are recorded honestly. For C, citations.json covers every proof citation with a verbatim complete statement; uses-union equals proof_deps. I traversed both statement and proof dependencies of every prospective citation and found no path back to the item. Generic tools outside this unit are explicitly justified in split_report.tool_uses; they implement the given route, rather than replace it. For D, the proof actually constructs and checks the maps and inverse equations instead of moving the conclusion to a new node. Every proof step is below 2000 characters; no hidden long-step lemma is left. For E, I checked the small cases above, the finite-dimensional compactification requirement, exactness/K-injectivity, and the distinction between varying coefficient systems and fixed completed-coefficient towers. The statement and route were not weakened.

## Unfinished work

None for this one-level stage-1 split. Existing unsplit dependencies retain their own work. Validation and direct push are performed by the required delivery command; no repository or launcher file is edited.
