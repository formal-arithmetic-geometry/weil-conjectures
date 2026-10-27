# Q24 — lem-pd-internal-direct-image-lax-realization

## Files written

- dag/nodes/sec-poincare-duality/lem-pd-internal-direct-image-lax-realization.json — statement, split; Mathlib has the separate section operations but not the full internal/section comparison.
- citations.json — 16 step/node citations, each checked against the current cited statement.

No new nodes and no Mathlib leaves. The statement, statement dependencies, creation provenance and blueprint ancestry are unchanged. The sandbox was empty apart from dispatcher markers. No repair note exists for this item.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for sectionModule/pushforward/adjunction and lax pushforward notions. The generic abelian pushforward generator equation exists in WeilConjectures/CategoryTheory/Sites/PushforwardMonoidal.lean, but does not state the internal balanced-module comparison or the specified adjunction comparison. FiniteCoefficient/UpperLowerStar/SectionsMonoidal.lean specializes to its coefficient category, not arbitrary condensed coefficient rings. PullbackTensorUnitSection.lean concerns structure-sheaf modules on opens, not this pro-etale internal-module equivalence. These are not attachments of this item.

## WANTED

None.

## Findings and route

The imported item has no proof. Its parent had already extracted the internal direct-image realization from the ordinary oplax-normalization argument. I retained that route and supplied the argument at this level. The chapter and unit records were read; this item is a lower-level comparison serving the inherited Verdier-exchange route, not the unit's key node, so neither record was edited.

Read sites-modules.tex, definition-pushforward (03D6), lemma-adjoint-pullback-pushforward-modules (03D7), and section-tensor-product (03EK), including the two successive Hom bijections in the adjunction proof and the displayed bilinear universal property of sheaf tensors. Also read current-blueprint def-sfb-module-upper-lower-adjunction.md and lem-sfb-pushforward-comp-monoidal.proof.md. The latter's loose section language must mean the composite with the presheaf-to-sheaf tensor map, rather than preservation of sheaf tensors by evaluation. The proof spells out that distinction. The resulting internal/section identification is an agent argument, so proof_origin.by is agent.

Searches of the whole DAG found lem-sfb-section-ring-lax-pushforward-coherence, lem-sfb-sheaf-pushforward-generator-comparison, lem-pc-sites-sheaf-tensor-bilinear-universal and lem-weil-pbc-ringed-topoi-module-adjunction. Their statements supply exactly the reusable ingredients, making further nodes unnecessary. Blueprint searches used direct image, lax, adjunction, section, tensor comparison and bilinear; the existing blueprint definitions give the structures, not another statement of this full comparison. Ancestor reports None, as expected for the seeded target ancestry. same_as is therefore empty.

Fresh Mathlib searches are recorded verbatim from searches.jsonl in addition to the original item's searches. LeanFinder was queried with two distinct phrasings, together with Loogle, LeanSearch and source grep. All services answered. Read Mathlib's Sheaf/PushforwardContinuous.lean:39–54 and Sheaf/PullbackContinuous.lean:48–110 to check the promising section-pushforward and adjunction hits. They do not compare internal module objects under sectionModuleEquivalence; neither do the scalar-extension and module-sheafification hits. No exact or one-line Mathlib specialization states the item.

## Review by Q24

I checked the five steps against the statements of all their cited nodes, and read the source passages above rather than treating their references as proof steps. There are no new nodes requiring a separate source check.

Step 1 uses section-ring-lax-pushforward-coherence specifically for its identity-underlying-sheaf comparison and the action r n = psi(r)n. Finite-lower-star supplies continuous base change and sheaf preservation. Coefficient-morphisms asserts that the adjunct coefficient map is a ring-object morphism. The operations-data definition fixes this same section comparison. The functor direction is Y_proet to X_proet, and the resulting direct image is from X-sheaves to Y-sheaves. Site objects in universe u+1 and arrows in u both fit the coefficient universe u+1; no smallness beyond the stated skeleton convention is introduced.

Step 2 uses the explicit mate normalization in operations-data; it does not infer adjunction compatibility merely from functor isomorphisms. The internal-adjunction statement gives the two successive Hom bijections, and the ringed-topoi-module-adjunction statement gives the corresponding canonical section adjunction. I wrote both scalar-extension formulas, checking their balancing and inverse equations, so unit compatibility has a concrete formula. Bilinear-universal is applied over the inverse-image coefficient ring, with the target restricted along alpha; S-linearity follows from multiplication in the first factor. Identity maps under the Hom bijections give the stated unit and counit. This also explains why the chosen section adjunction is the one being compared.

Step 3 uses the full generator equation in sheaf-pushforward-generator-comparison. Its statement explicitly identifies both tensor and unit maps after precomposing with the actual sheafification units. It applies to tensor abelian groups, a closed symmetric monoidal Grothendieck abelian coefficient category. No claim about evaluation being strong monoidal occurs here.

Step 4 uses the coequalizer displayed in relative-tensor and the actual scalar-restricted action displayed in module-lower-star. The balancing equation is written for arbitrary local r,a,b. Bilinear-universal gives the unique sheaf map from this restriction-compatible balanced pairing, and internal-section-tensor-comparison gives identity on pure tensors for the fixed strong constraints. Thus equality of maps follows from a cited universal property, not from a claim that every global tensor section is a sum of pure tensors. The non-elementary abelian generator identification is explicitly cited in step 3, not hidden in this calculation.

Step 5 uses module-lower-star and coefficient-morphisms for the very same c, and internal-section-tensor-comparison for the regular-unit identification. The abelian unit-generator equation of step 3 sends the local integer generator to the local unit, so the induced scalar-restriction map is r to c(r), including r=0. This is the specified map, not a choice of lax unit inferred from a potentially unrelated tensorator.

For B–E I checked self-contained existing hypotheses, precise Stacks labels, truthful search logs, the union of uses against proof_deps, the statement quotes, and potential circular dependencies. No clause is moved to a replacement node. No statement correction or STATEMENT-DISPUTED issue was needed. The five steps have lengths 587, 1147, 662, 1103 and 631 characters, each below 2000; there is no long step hiding an unrecorded lemma. All invoked cross-unit statements are generic module/sheaf tools, declared in split_report.tool_uses. They do not replace a step of the unit's geometric route.

Small-case checks: for the identity morphism the coefficient map is the identity and the pairing sends a tensor to itself; scalar extension along the identity has the displayed insertion and multiplication inverse. Zero modules give the zero pairing. For the zero ring the regular unit is zero and the formulas still hold, with 1=0. Empty site objects cause no problem since all equations are sheaf/presheaf map equations. No flatness, points, finite-presentation or tensor-preservation-by-evaluation hypothesis is used.

## Unfinished work

None for this stage-1 split. The cited non-Mathlib nodes remain their own existing items; this delivery does not claim Lean proofs for them.
