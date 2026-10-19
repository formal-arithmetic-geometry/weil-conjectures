# Worker report: lem-kun-higher-exchange-coefficient-cube

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-higher-exchange-coefficient-cube.json`: statement, split; not a Mathlib leaf. Statement and statement dependencies retained; four proof steps and their exact dependency union supplied.
- `citations.json`: a verbatim statement quotation for each of the nine step/node citations.
- `searches.jsonl`: actual msearch records. No new node files and no Mathlib leaves.

## Attachments

None. Searches of WeilConjectures for the blueprint tag and cube/exchange/coefficient vocabulary found no declaration stating this item in its full generality. Pasting.lean supplies ordinary pasting ingredients, DerivedComparison.lean compares the two derived exchanges, and FailureOverField/Transition.lean gives a special transition geometry; none is an attachment of the eight-scheme arbitrary coefficient identity. The upstream master checkout is reference material only.

## WANTED

None.

## Findings and changes

The item had a complete, correctly typed statement but no proof. Its source is an agent extraction of the canonical-map compatibility needed in Stacks 0EYM and 0EZT, rather than a verbatim separately numbered assertion. I kept the statement exactly. In particular, comparison faces only commute, and neither their exchanges nor the coefficient morphism is inverted. I did not apply a cartesian-only pasting theorem to a noncartesian comparison face.

The existing `lem-kun-derived-exchange-cube` already provides the stronger bounded-below derived cube, without cartesian faces. The degreewise result still needs naturality at the coefficient morphism and identification of all factors on cohomology; those arguments remain in this item's steps. No clause has been moved to a new node. The imported item has no lean_audit record, so the source inspection and Mathlib searches were performed directly.

I read the current main-20261015 blueprint node `lem-kun-0ezt.md`, the chapter and unit records, and the existing DAG parent. The current blueprint node contains the limit assertion without a proof; the older DAG ancestry locates this compatibility in the final canonical-map comparison. The unit is not this item's key statement and no unit record was modified. Generic localization and exact-functor cohomology tools from other units are declared in split_report.tool_uses; they do not replace the unit's limit route.

## Mathlib and duplicate searches

The whole-DAG title/statement search for mate, exchange, cube, pasting and composition found `lem-kun-derived-exchange-cube`, `lemma-weil-pbc-derived-exchange-coherence`, `lem-weil-pbc-exchange-identity-pasting`, and `lem-weil-pbc-abelian-exchange-cube-comparisons`. I opened their statements: only the first supplies precisely the unrestricted derived cube needed here; the other cube statement includes stalks and a different local geometry. The blueprint_refs ancestor is lem-kun-0ezt; searches for cube and higher direct image found no blueprint node equivalent to the present coefficient cube. Therefore same_as is empty. No new nodes need duplicate comparisons.

All five additional searches were actually run through msearch.py and their results read. LeanFinder with two phrasings returned module-sheaf pullback coherence and free-module comparisons; these do not state a derived etale cube. LeanSearch returned CatCommSq ordinary naturality, etale stability under base change and TwoSquare.lanBaseChange. The latter is a left Kan-extension comparison, not this etale right-derived map. Loogle returned NatTrans.naturality, which is exactly the elementary naturality ingredient of step 2, but does not supply the geometric cube. I read NatTrans.lean's naturality field and CatCommSq.lean's iso_hom_naturality and inspected the KanExtension declaration. The recorded CategoryTheory grep had zero hits. Inherited searches from Q79 were preserved, and the actual new query texts and results were appended to the item.

## Unfinished work

None for this one-level split. The already existing derived cube is now marked split in the current repository; this delivery cites its statement and does not modify its split. No Lean files or compiler/build tools were used.

## Review by Q73

I read Stacks etale-cohomology.tex, Tag 0EYM (lemma-relative-colimit-general), especially its first two proof paragraphs defining transition maps by exchange followed by the coefficient morphism, and Tag 0EZT (lemma-base-change-Rf-star-colim), especially the two colimit identifications in its proof. I also read sites-cohomology.tex, Tags 07A7 (remark-base-change) and 0E47 (remark-compose-base-change-horizontal). These support the mate and transition route; the explicit degreewise compatibility is agent-written and is marked as such, with no claim that those paragraphs themselves contain a complete cube proof. No SGA source is used.

For step 1 I opened the statement of lem-kun-derived-exchange-cube and matched all eight schemes and all four comparison equalities with the item. It states exactly the derived equality, including the target composition comparison and without cartesianness or invertibility assumptions. The statement of def-weil-pbc-derived-inverse-image supplies termwise inverse image and preservation of D-plus, so the degree-zero coefficient map is an admissible derived morphism. This is an invocation of an existing more general result, not a new restatement.

For step 2 I opened def-kun-commutative-derived-exchange: it explicitly calls the mate a natural transformation on the bounded below abelian-sheaf derived category. The displayed naturality equation at phi-hat is its defining naturality property. Precomposition and substitution are elementary category algebra. No result is inferred merely from a definition of flatness or a name suggesting naturality.

For step 3 I opened lem-weil-pbc-exact-functor-complex-cohomology, def-weil-pbc-derived-inverse-image, lem-weil-pbc-localization-universal-property, and lem-weil-pbc-derived-inverse-image-composition. The exact-functor lemma is only stated on complexes, so I did not silently claim it is already natural for arbitrary derived morphisms. Its natural isomorphism descends by localization part (2), since cohomology inverts quasi-isomorphisms and the inverse images are exact. Part (3) checks equality after localization. The composition node explicitly identifies the derived comparisons with the termwise sheaf comparisons; the cohomology lemma explicitly gives compatibility with cycle inclusions and cohomology projections. Thus the quotient argument identifies the cohomology of chi-D with the specified sheaf chi, rather than introducing a new comparison.

For step 4 I opened def-weil-pbc-direct-image and lem-kun-bc-map-on-cohomology. The former defines higher images as degree-q cohomology of derived direct image; the latter equates cohomology of derived exchange with the usual injective-resolution base-change map for cartesian squares and abelian coefficients. Both b-squares satisfy that cartesian hypothesis. The P and Q faces need no such hypothesis because their degree-q maps are defined in the item using the commutative mate. Every factor in the final equality is individually identified, including the coefficient map, chi, and the pulled-back original beta.

I checked the degree q=0 case, where the argument is the ordinary naturality/cube identity; phi=identity, where it is the cohomology of the derived cube; phi=zero or F1=zero, where both composites vanish; and empty schemes, where the same categorical identities remain well typed. For higher q no injectivity or acyclicity is assumed on the coefficients. Cartesian comparison faces, qcqs morphisms, affineness, and torsion are never required. The original statement needed no correction. The only substantive gap corrected was the missing argument that the cohomology comparisons are natural on the derived category and compatible with chi. All steps are below 2000 characters and none hides a separate non-elementary lemma: the non-elementary cube and localization assertions are existing cited nodes. The nine citations have exact quotations from the opened statements. This review is my own check under the direct-delivery brief, not an independent second reading.

## Resumed delivery check, 2026-10-17

I compared the retained sandbox item with the current shared item: the statement, statement dependencies, source, ancestry and unit binding agree exactly. I reopened all eight proof-dependency statements and checked all nine citation quotes against their current text; every quote remains verbatim. I reread Stacks 0EYM and 0EZT and Remarks 07A7 and 0E47, and the current main-20261015 ancestor text. The derived cube is now split upstream, so I corrected the stale status sentence above. The retained mathematical argument and recorded searches require no change. A fresh search of the project Lean source still finds no exact blueprint-tag attachment; its coefficient and transition results cover other or more restricted geometries. The four proof-step lengths are 768, 592, 1108 and 849 characters, respectively. No new nodes, Lean edits or builds were introduced.
