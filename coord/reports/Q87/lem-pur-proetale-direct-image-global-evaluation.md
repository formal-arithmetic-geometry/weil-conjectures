# Stage-1 delivery: lem-pur-proetale-direct-image-global-evaluation

Group Q87, 2026-10-21. Only stage 1; no Lean written or compiled.

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-proetale-direct-image-global-evaluation.json: statement, split into eight proof steps; no Mathlib match for the complete normalized comparison.
- citations.json: exact statement quotations for every step/node citation.
- searches.jsonl: results recorded by the required search command.

No new nodes, no Mathlib leaves, no unit or chapter changes. write_split.py is sandbox-only preparation material.

## Attachments

None. Searched WeilConjectures for the blueprint tag and for pro-etale/global/derived-section notions. AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso (SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/GlobalSections.lean:61) is underived; the composition and identity lemmas in Restriction.lean are likewise underived. AlgebraicGeometry.ProEtale.derivedGlobalSectionsUnitIso (SixFunctors/ProEtale/Adic/DerivedGlobalSectionsTransport.lean:121) concerns the adic unit under scheme isomorphisms. Neither covers arbitrary morphisms, ordinary finite coefficient modules, and every normalization clause of this item.

## Literature wanted

None.

## Findings and corrections

The item had a complete statement but no proof. Its bounded-below category reference was def-weil-pbc-derived-categories, whose statement defines only the etale categories. Replaced this reference and its statement dependency with def-weil-pbc-bounded-derived-subcategories; the pro-etale module definition already supplies the ambient category. This is a citation repair with no mathematical change, added hypothesis or removed conclusion.

The finite published coefficient sheaf needs its constant-preserving identification with the ordinary constant sheaf. Step 1 cites prop-weil-pbc-proetale-constant-ring-map explicitly. No integral completion, constructibility, finite cohomological dimension, properness or quasi-compactness assumption is used. The proof does not assume arbitrary inverse image preserves K-injectives.

The generic tools from other units are declared individually in split_report.tool_uses. They implement the global-sections paragraph of sk-prop-a1 after localization and Rp_*, through the retained ancestor prop-pur-affine-line-orientation-uniqueness and the extracting parent lem-pur-retracted-support-localization-comparison. They do not replace the orientation or purity route. The chapter and unit remain untouched. There is no unit realization edit because this item is not its key statement.

## Unfinished work

None for this one-level split. Supporting statements are existing DAG obligations, whose status is retained.

## Not duplicates

No new nodes. Searched the whole DAG and blueprint with global sections, Leray, K-injective, global evaluation and final object. The etale Leray nodes do not by themselves assert the ordinary pro-etale module comparison with its specified unit, shift and composition normalizations. Reused existing general facts, in particular the ringed-topos composition theorem, instead of creating a new Leray node or one node per clause.

## Review by Q87

I read the item, the chapter and unit records, the current main-20261015 sk-prop-a1 statement and proof, and the current ancestor proof prop-pur-affine-line-orientation-uniqueness. I read Stacks sites-cohomology.tex Tag 0D6H (lemma-Leray-unbounded) and Tag 0D6E (lemma-derived-pushforward-composition), including their proofs: they give the right route through final-object sections and composition but do not alone spell out every normalization required here. I read derived.tex Tags 08BJ (lemma-adjoint-preserve-K-injectives), 070I (lemma-K-injective), 070Y (lemma-K-injective-defined), 070K (lemma-enough-K-injectives-implies), and the derived adjunction representative characterization. I also read proetale.tex Tag 09BN (lemma-open-immersion). The explicit normalization and third-arrow arguments are agent elaborations, and proof_origin says so. There are no new nodes needing separate literature checks.

For Step 1 I checked the full statements of def-weil-pbc-proetale-site, def-weil-pbc-proetale-modules, prop-weil-pbc-proetale-constant-ring-map, def-weil-pbc-bounded-derived-subcategories and lem-sc-bounded-below-injective-resolution. The site is small in the chosen larger universe; the coefficient ring is commutative and finite. The good truncation is written explicitly, so a cohomologically bounded-below object really has the bounded-below input required by the resolution theorem. The constant-ring identification preserves precisely the structural map needed here.

For Step 2 the statement of def-weil-pbc-proetale-operations gives the exact left adjoint and actual module adjunction, not merely names for operations. These are exactly the hypotheses of lem-weil-pbc-right-adjoint-preserves-kinjective. The finite clause of def-weil-derived-direct-image uses this ordinary total right derived functor. This proves that the middle K-injective model is admissible; it is not inferred from a definition of K-injectivity alone.

For Step 3 pur7710-def-derived-sections expressly defines coefficient-linear derived sections by K-injective computation, and def-weil-proetale-module-direct-image gives both the object and map evaluation formulas. I checked the ring action as well as the differential. The canonical terminal-object isomorphism is understood when writing the identity of section complexes. lem-sf-kinjective-derived-map-computation gives the normalized model identifications.

For Step 4 lem-weil-pbc-kinjective-hom-derived states the Hom bijection for an arbitrary source, and lem-sf-kinjective-derived-map-computation states the formula for arbitrary derived morphisms, changes of resolution and their cocycles. Thus the calculation covers roofs and not just chosen chain maps. Both supporting statements were opened and read, and the chosen source and target complexes meet their K-injective hypotheses.

For Step 5 lem-pc-right-derived-functor-triangulated supplies the derived shift comparisons and triangulated property. I checked its source instances at WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean:94-99. The defining null-homotopy test of def-pur-kinjective-complex verifies shifted K-injectivity directly; the identical (-1)^n differentials show the shift square, and the already-cited model-transition formula identifies it with the specified comparisons. No assertion that plain cohomology is enough to control a derived arrow is used.

For Step 6 I read the statements of both lem-weil-derived-direct-image-composition and lem-weil-pbc-ringed-topoi-derived-pushforward-composition. The latter expressly supplies the g_*v representative, unlike a bare existence claim. Since f_*J is K-injective the identity is an allowed resolution, so all maps reduce to the displayed final-object identifications. The finite canonical comparison of the former is the ordinary ringed-topos comparison; its finite proof paragraph confirms this convention. The equality itself is proved in the item. For a triple fibre product the two terminal identifications are the same canonical map. The identity case is likewise computed, rather than imported from an unrelated etale assertion.

For Step 7 I checked prop-pur-kinjective-resolutions-exist on the small ringed site of U, the actual adjunction in def-weil-pbc-proetale-operations, and the representative characterization in lem-pc-pre-derived-adjoint-functors-general. The displayed composite is the unit because its adjunct is the resolution v and hence the identity in the derived category. lem-pur-proetale-open-unit-evaluation gives the actual unit at every site object, including the final object, and is valid for any open immersion. It states exactly the evaluation isomorphism and restriction formula used. Resolving j^*J separately avoids an unstated K-injective preservation assumption about j^*. The resulting two-map section complex is the definition of derived restriction.

For Step 8 the generic triangulated theorem applies to direct image and sections. Naturality is applied to the existing third morphism d, with the fourth comparison identified by Step 5. The last square is written explicitly; this verifies the existing arrow and its sign, rather than choosing a new connecting map for an isomorphic triangle. No new support-localization theorem is used or claimed.

I checked B--E point by point: no statement-only new nodes or duplicate clauses, no hidden non-elementary fact left as an elementary assertion, no source or definition cited for a theorem it does not state, no source proof used in place of its statement. Every cited node has an exact statement quote in citations.json. All steps are below 2000 characters. The dependency search finds no path back to the item. I preserved imported metadata and the original recorded Mathlib searches, and appended the searches actually run for this delivery. The six logged searches include a second semantic phrasing and a targeted second grep; I read the abstract comparison, derived-unit and underived section candidates in Mathlib. They do not give a one-line specialization of the whole item.

Small cases checked: zero complex gives identity on zero; the empty scheme gives zero section complexes; identity maps give the stated identity; U=T gives identity restriction, U=empty gives the unique zero restriction; disjoint unions retain all components of global sections; shifting by 1 negates both differentials and introduces no extra boundary sign. Arbitrary non-quasi-compact opens are allowed because none of the cited unit or resolution statements impose quasi-compactness.

Server-only preliminary checks: review_split PASS, 0 new nodes; check_dag OK with no introduced finding. The full required dry run and push follow this report.
