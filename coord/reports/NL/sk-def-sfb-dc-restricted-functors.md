# Worker report: sk-def-sfb-dc-restricted-functors

## Files written

- dag/nodes/sec-six-functors-basics/sk-def-sfb-dc-restricted-functors.json: existing definition, split; preserve its statement and all five preservation inputs and cite existing generic Mathlib leaves for its categorical arguments. Proof text totals 2851 characters, down from 3187, because the adjunction and natural-isomorphism lifting arguments are now explicit cited statements.
- dag/units/sk-def-sfb-dc-restricted-functors.json: only realized and realized_by filled; both blueprint proof paragraphs are realized by the item.
- citations.json: a verbatim statement quote for every node cited by each of the four steps.
- searches.jsonl: actual searches run through the required msearch.py command; their results were read and the corresponding records appended to the item.

Zero newly created nodes, zero newly created Mathlib leaves. Four existing Mathlib leaves now carry generic arguments: lem-sp-fully-faithful-adjunction-restriction, lem-sfb-fully-faithful-postcomposition, lem-cbc-fully-faithful-isomorphism-lift and lem-sfb-fully-faithful-cancel-iso-components. The postcomposition and cancellation nodes were created on 2026-10-21 by the parallel re-split work, so they are reused rather than duplicated. The delivery gate explicitly counts cited nodes landed since the re-split note's baseline in its new-node condition.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint docstring tag (no hits) and for boundedConstructibleUpperStar, boundedConstructibleLowerStar, boundedConstructibleTensor and boundedConstructibleHom. The project has the restricted operations in WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean, but boundedConstructible_rightDerivedLowerStar_obj (lines 251–256) and isMonoidalClosed_boundedConstructible (lines 485–488) contain sorry. Thus their assembly is not a finished proof of every clause, and ATTACH would be incorrect.

## WANTED

None.

## Repair note and argument accounting

This repairs coord/repair-notes/sk-def-sfb-dc-restricted-functors.json, released 2026-10-22 under the human's 2026-10-21 re-split decision. Its instruction reopens the item despite its retained older approval metadata. The statement remains byte-for-byte the live statement. The purpose is to name the separate arguments rather than conceal them in shortened prose.

The old first step (five preservation assertions, all coefficient hypotheses) is unchanged. The old second step (objects, maps, products/opposites, functor laws, compatibility and uniqueness of the restrictions) is unchanged. In the old third step, the naturality and inverse Hom-bijection argument is now the full statement of lem-sp-fully-faithful-adjunction-restriction, with the same ambient adjunctions and inclusion comparisons. No preservation is inferred from that purely categorical lemma. In the old fourth step, postcomposition full faithfulness is the statement of lem-sfb-fully-faithful-postcomposition; existence and uniqueness of an isomorphism preimage is lem-cbc-fully-faithful-isomorphism-lift applied in functor categories; forward and inverse components are the statement of lem-sfb-fully-faithful-cancel-iso-components. These existing results retain exactly the old inverse and naturality equations. No argument has been replaced with a new node restating one of the geometric functor clauses.

## Not duplicates

No new nodes. DAG searches by restrictFullyFaithful, preimageIso, fully faithful postcomposition and natural-isomorphism cancellation found the four existing general results, whose statements were opened. Whole-blueprint searches used blueprint_refs.py search for restrictFullyFaithful (zero), preimageIso (zero), full subcategories, fully faithful inclusion and restriction, together with ancestor for the item. No second aggregate or generic-restriction node was created. The leaf for adjunction restriction is more general than the required full-subcategory case; it is cited as a Mathlib tool from another unit.

## Review by NL

I read GOAL.md, the worker/stage-1 rules, SETUP.md's three levels, delivery-errors B–E, the current item, its chapter/unit, the released repair note, and the current blueprint _section.md and sk-def-sfb-dc-restricted-functors.proof.md. The source's first paragraph names the five preservation lemmas and five operations; the second gives factorization through full subcategories, restriction of Hom-bijections, and natural-isomorphism preimages. Those remain the four proof steps. The chapter route and unit statement are unchanged. I read the generic adjunction implementation at pinned Mathlib/CategoryTheory/Adjunction/Restrict.lean:26–88, postcomposition at CategoryTheory/Whiskering.lean:108–125 and isomorphism lifting at CategoryTheory/Functor/FullyFaithful.lean:201–222. The existing cancellation leaf records the component declarations at lines 372, 378 and 384. These are categorical Mathlib sources, not new geometric finiteness inputs or a forbidden SGA route.

For step 1 I opened all five cited statements. Pullback and extension by zero allow every commutative condensed ring. Pushforward, tensor and Hom each contain the three coefficient cases asserted by the item. Pushforward also allows finite discrete ell-primary rings, which gives extra scope and is not needed here. The scheme hypotheses remain separated and finite type over a field k of characteristic p, with distinct primes p and ell. None of the last three preservation assertions is applied to arbitrary coefficients.

For step 2 I opened sk-def-sfb-bounded-constructible and all five cited operation definitions. The former explicitly defines a full subcategory with ambient morphisms, identities and composition, without a derived-completeness requirement. The latter specify restrictions of the same ambient operations. Thus (K,h) maps to (F(K),hF), arrows map by F, and identities/composition remain those of F. Products and opposite products handle the two-variable operations. No general-purpose lemma is hidden here: the complete elementary construction is retained verbatim, including uniqueness when the inclusions commute strictly.

For step 3 I opened all three cited adjunction definitions and lem-sp-fully-faithful-adjunction-restriction. The definitions give exactly the ambient Hom-bijections to which the generic theorem applies. Its fully faithful i,j are the full-subcategory inclusions, and its comparison isomorphisms are step 2's compatibility maps; no essential-surjectivity or smallness assumption is used. For strict inclusions these comparisons have identity components, so the displayed composite Hom-bijection is the original ambient one on the same maps. The open adjunction definition expressly contains D(j^*) isomorphic to Lj^*, avoiding an unsupported identification. Push-pull uses coefficients for which pushforward preserves, open shriek uses all Lambda, and tensor–Hom fixes a bounded constructible K and assumes both preservation assertions.

For step 4 I opened def-sfb-dc-upper-star-comp and all three generic lifting leaves. The definition names the ambient composition isomorphism. The postcomposition leaf makes the inclusion of functor categories fully faithful, so the isomorphism-lift theorem applies to these functors as objects, with no change of universes beyond those already allowed by that leaf. The cancellation leaf fixes both forward and inverse components. Uniqueness follows from injectivity on natural transformations, not from object-level faithfulness alone. Hence the entire original component/inverse/naturality/uniqueness argument remains represented in cited statements, for arbitrary Lambda and composable morphisms of the setting.

I checked each citation against the node's statement, not its proof, and copied those statements verbatim into citations.json. No new non-elementary geometric assertion is left uncited. The generic leaves are tools; they replace none of the five preservation lemmas or any unit route. No statement was changed, so there is no statement dispute to report. The generic theorems permit empty categories and zero objects, and no step assumes a nonempty scheme, stratum or object. Each step is below 2000 characters; total proof text is 2851. No new source tag, definition, unsplit node, unsupported Mathlib absence claim, or duplicate was introduced. No Lean, compiler, Lake, repository write or launcher modification occurred.

## Validation

The first dry run on the unchanged reading copy failed preflight; the separate server review_split passed but noted the missing unit realization. The repaired item fills that realization and records the released re-split arguments as explicit existing-node citations. The final dry run and push results will be recorded below.
