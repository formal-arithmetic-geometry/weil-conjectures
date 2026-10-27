# Stage-1 delivery: lem-sfb-topos-cohomology-pullback-delta

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-topos-cohomology-pullback-delta.json: statement, now split into seven proof steps. The statement and its statement dependencies are retained. No exact Mathlib match.
- citations.json: eighteen verbatim statement quotations, one for every cited node in every proof step.
- report.md: this report. searches.jsonl contains the search command's actual search records. write_split.py is sandbox-only authoring material.

No new nodes; no Mathlib leaves. No Lean written or compiler invoked. The shared repository and launcher were read only.

## Attachments

None. A search of lean/WeilConjectures for the item blueprint tag returned no declaration. Concept searches found AlgebraicGeometry.Etale.cohomologyMap_δSucc in SixFunctors/Etale/UpperLowerStar/CohomologyMapDelta.lean:45, which proves the boundary equation for scheme morphisms on small etale sites. It does not cover arbitrary geometric morphisms, arbitrary presenting sites, or the specified resolution comparison, and is not an attachment. Generic horseshoe declarations were inspected as corroboration of the existing DAG tools, not substituted for the item.

## WANTED

None. All source material used is available locally.

## What needed work

The imported item was statement-only. Its sources describe universal derived global cohomology and cohomology functoriality but do not themselves provide a split for this precise geometric-morphism resolution construction. I marked the synthesized proof as agent-written. No statement error was found and no hypothesis was added.

The existing lem-weil-pbc-site-cohomology-pullback is restricted to morphisms of presenting sites and evaluation at a site object. Its statement explicitly leaves the distinguished-triangle boundary comparison unaddressed. Thus merely citing it would miss both the generality of this item and its specified derived boundaries. Likewise lem-weil-pbc-horseshoe-delta-functor explicitly disclaims that boundary identification. Step 5 supplies the assembly from existing triangle and homology-comparison tools; it does not assume the missing identification.

The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor prints None. I preserved the inherited place and via chain, whose place identifies det-thm-sf-ctf-stability-direct-images proof (3), and filled split_report.blueprint with the relation of this homological prerequisite to that place. The current latest file is sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md (frontmatter of det-thm-sf-ctf-stability-direct-images). The latest unit and direct-image proof were read as well as the DAG unit and chapter. This is below the unit route, not a replacement for its direct-image proof. The item is not the key unit node; no realization fields were changed.

## Searches and reuse

The sandbox initially had no node, report or search log, so the live item was copied. The imported Mathlib searches were retained. New logged searches used leanfinder (two different phrasings), loogle, leansearch and grep. Results are recorded verbatim as tool/query pairs in the item, with the names returned and an assessed verdict. Loogle found NatTrans.rightDerived and its computation on a chosen resolution, which compare functors on one source category. LeanFinder's second phrasing found Ext.mapExactFunctor and snake-boundary formulas. I read Mathlib/CategoryTheory/Abelian/RightDerived.lean, CategoryTheory/Sites/SheafCohomology/Basic.lean and Algebra/Homology/DerivedCategory/Ext/Map.lean. None is a one-line specialization to the complete item: the resolution construction across L, its choice comparison and identification with derived global boundaries require the argument delivered here. A restrictive grep of Ext/Map.lean returned no hits and is honestly recorded as such, not treated as absence of its Ext constructions.

Whole-DAG title/concept searches located the existing lift, homotopy, horseshoe and triangle comparison nodes. Whole imported-blueprint searches for delta, global cohomology, resolution pullback and geometric morphism were read. The global-cohomology comparison result concerns the etale/proetale comparison for schemes, not this item. No candidate needed a new node. Thus no duplicate pairs arise.

## Not duplicates

No new nodes.

## Review by Q77

I read Stacks sites-cohomology.tex Tag 01FT, section-cohomology-sheaves, including its global-section definition when the site has no final object; Tag 08J6, remark-before-Leray; cohomology.tex Tag 01F8, lemma-functoriality; derived.tex Tags 013P (lemma-morphisms-lift), 013S (lemma-morphisms-equal-up-to-homotopy), 013T (lemma-injective-resolution-ses), 013K (lemma-injective-resolutions-exist), 015B (lemma-higher-derived-functors) and its preceding right-derived properties; and homology.tex Tag 0117 (lemma-long-exact-sequence-cochain). I checked tag labels against tags/tags. I also read the current latest blueprint direct-image proof and the long-exact-of-triangle statement and proof. No prohibited SGA route is used.

For step 1, def-trf-geometric-morphism actually supplies the adjunction and finite-limit preservation, including preservation of the terminal sheaf. The bijection on global sections is therefore adjunction at that terminal sheaf, not evaluation at an assumed final site object. The additive and kernel statements are written out directly. Exactness of the abelian inverse image is part of the item's explicit setup; the proof does not assume preservation of injectives by L.

For step 2 I opened lem-weil-pbc-site-sheaves-enough-injectives, lem-weil-pbc-left-exact-injective-resolution-degree-zero and lem-weil-pbc-lift-along-injective-quasi-iso. They respectively supply the required abelian/enough-injective categories, nonnegative injective resolutions and the strict comparison into a bounded-below injective target. The source augmentation becomes monomorphic and a quasi-isomorphism under the assumed exact L. This checks both hypotheses of the lift, even though LI is not injective. I corrected a source-place tag from the section tag 013G to the actual existence lemma 013K.

For step 3 I opened lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, lem-weil-pbc-homotopic-maps-equal-cohomology, lem-weil-pbc-injective-resolution-lift-exists and lem-weil-pbc-derived-functor-map-via-lift. The first allows the non-injective source LI; only the target J' must be bounded below injective. The two maps v beta and beta' Lu have equal augmented restrictions, which is exactly its hypothesis. The additive T preserves the resulting homotopy and its cohomology maps agree by the second statement. The last two statements give actual augmented coefficient lifts and identify their homology maps with the canonical derived-functor maps. Taking h to be the identity compares arbitrary source and target resolutions at once, without choosing noncanonical identifications.

For step 4 the degree-zero part of lem-weil-pbc-left-exact-injective-resolution-degree-zero identifies the augmentations with the degree-zero isomorphisms. Strict augmentation compatibility then identifies the map with the adjunction map from step 1; this proves its formula on every section, rather than merely asserting a transported normalization.

For step 5 I read all six cited statements: lem-weil-pbc-injective-resolution-ses gives compatible nonnegative horseshoes; lem-weil-pbc-ses-injective-kernel-splits gives all three splitting equations; def-weil-abstract-derived-category supplies the localization homology convention; lem-sc-p1-horseshoe-derived-triangle-comparison supplies a triangle morphism with the precise endpoint identifications j theta; lem-sp-long-exact-of-triangle gives boundary naturality for that triangle morphism; and lem-sc-p1-nat-complex-derived-boundary gives the snake/derived boundary equation for extension by zero. No cited statement merely defines the missing comparison. The image exactness required by the triangle-comparison statement follows by applying each additive functor to the displayed splitting identities, so global sections need not preserve arbitrary epimorphisms. Extension by zero has the same exact row in nonnegative degree and the zero row otherwise. The endpoint equations yield exactly j delta = partial j, and the shift/sign conventions are those of the cited derived-boundary node, not an independently guessed sign. All categories are taken in the common sheaf universe, enlarging the derived-morphism universe as in the size convention, so the derived-category tools add no smallness restriction to the sites.

For step 6 I opened lem-weil-pbc-horseshoe-morphism-lift-exact-source and lem-weil-pbc-complex-ses-long-exact-naturality. The former expressly allows source columns that are merely exact augmented resolutions and gives a middle complex map with both row squares strictly commuting. The image LI has exactly those hypotheses, while the target is an actual injective horseshoe. After applying T and composing with the natural section map, both global complex rows are short exact by the splitting calculation. The second statement then gives the displayed endpoint boundary equation. Steps 3 and 5 identify its endpoint maps and boundaries respectively with the exact maps in the item; neither identification is taken from an uncited proof of a node.

For step 7 I read clause (1) of lem-weil-pbc-horseshoe-delta-functor. It states the arbitrary-extension-morphism naturality equation used here for a left exact additive functor on an abelian category with enough injectives. Those hypotheses hold for global sections by steps 1 and 2. Its disclaimer about derived boundaries is addressed by step 5 before it is used. This proves the last clause on either site.

I checked the small cases: degree zero uses augmentations and admits no boundaries from negative degrees; zero sheaves and zero extensions give zero maps; the identity geometric morphism permits beta to be the identity on a common resolution and gives the identity cohomology map. The proof never uses enough points, an object representing terminal sections, or L preserving injectives. Every cited node statement was read, and citations.json selects verbatim portions of those statements. No new statements need edge-case review. No step exceeds 2000 characters. The nontrivial comparison in step 5 is an assembly of explicitly cited comparisons, not a hidden new lemma. Tools from other units are declared in split_report.tool_uses as general homological algebra tools; they do not replace the unit's geometric route.

## Checks and unfinished work

Server srvcheck review_split passed with zero new nodes. It notes that the parent unit has no realization recorded yet; this item is not its key node. Nothing mathematical remains unfinished for this split. Full delivery dry run and push are recorded below after their completion.

Full dry run: the first invocation requested a longer quotation for homotopy invariance; I replaced it with the whole cited statement. The next invocation exited successfully: `OK (not pushed) deliver/Q77/lem-sfb-topos-cohomology-pullback-delta at 453803fc030: preflight passed`. This includes the server DAG and split checks. No mathematics or statement changed after the passing check.
