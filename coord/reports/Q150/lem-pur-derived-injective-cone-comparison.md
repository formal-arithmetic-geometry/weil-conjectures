# Stage-1 delivery: lem-pur-derived-injective-cone-comparison

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-derived-injective-cone-comparison.json: statement node, now split into six steps; no exact Mathlib match for the whole assertion.
- citations.json: twelve verbatim statement quotes for all step citations.
- searches.jsonl: actual msearch.py output records. The inherited Mathlib searches in the item are retained, with six additional searches from this session.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for the whole item. The project declaration CategoryTheory.rightDerived_injectiveComplex_boundary in lean/WeilConjectures/CategoryTheory/Abelian/RightDerivedInjectiveBoundary.lean covers the boundary clause, and already belongs to lem-sc-p1-right-derived-injective-boundary. It does not state the cone isomorphism, cone quotient comparison, or naturality of the entire comparison, so it is reused as a dependency rather than offered as an attachment of this item.

## WANTED

None.

## Corrections and omissions in the starting node

The statement is unchanged. Its source's Tag 014Z is the section containing the construction; Tag 0152, lemma-derived-canonical-delta-functor, gives the canonical boundary and its naturality. I retain the original source metadata and give the more precise places on the proof steps. There was no proof in the starting item. I did not strengthen additivity to left exactness: lem-weil-pbc-derived-direct-image-triangulated assumes left exactness, so its statement is not an applicable generic citation here. The existing inverse-unit boundary theorem expressly assumes only additivity and the two exact rows, and is the correct tool.

The sandbox had no earlier item or report. There is no released repair note for this item. I searched the live project's WeilConjectures source for the exact blueprint tag and for cone/quotient and derived-unit comparisons. The K-injective comparison and its naturality in RightDerivedFunctor/KInjective.lean and RightDerivedFunctor/ShortExact.lean do not prove this full bounded-below injective-row assertion. No finished whole-item attachment was found.

## Not duplicates

No new nodes. Whole-DAG searches by statement concepts and Stacks tags, and blueprint_refs.py searches for cone, injective, right derived, short exact sequence of complexes, injective cone, and cone quotient found reusable nodes. In particular lem-pc-cone-short-exact-quasi-iso is reused for both quotient maps; lem-sc-p1-right-derived-injective-boundary is reused for the last-arrow square. Creating a fresh node for either fact would duplicate an existing statement. The remaining cone comparison, finite-biproduct injectivity, and strict row-map formulas are short explicit calculations in the item rather than new nodes.

## Review by Q150

I read the chapter sec-smooth-purity and the sk-prop-a1 unit, the nearest blueprint ancestor and its main-20261015 proof (Steps 1 and 3), and the item's existing ancestry through support-global-boundary. The item is a generic homological-algebra tool below the localization/global-supported-class argument, so this split does not change the geometric proof route. The unit and chapter files are untouched. The two off-unit statement tools are declared in split_report.tool_uses; the other off-unit tools are Mathlib leaves or definitions.

For the source I read derived.tex definition-cone (the displayed differential, inclusion and projection), section-canonical-delta-functor (Tag 014Z), lemma-derived-canonical-delta-functor (Tag 0152, including its naturality proof), and lemma-injective-acyclic (Tag 05TH). I also read lemma-right-derived-properties to check that additivity, rather than left exactness, is the relevant derived-category hypothesis. The explicit assembly is marked agent-written: the Stacks text supplies the constructions and signs, while the existing DAG boundary statement supplies the normalized inverse-unit comparison.

Step 1 cites the statement of def-sp-injective-resolutions, specifically its extension property for an injective object. I checked the extension into a biproduct component by component, so finite biproduct injectivity is actually proved here. If the three complexes vanish below N, the cone vanishes below N-1. No bounded-above assumption and no injectivity of T(E), T(F), T(G) is used.

Step 2 cites def-sp-left-exact-additive only for its finite-biproduct meaning of additivity, and def-weil-abstract-derived-category for the signed cone and shift convention. I read both statements. The matrix calculation gives a complex isomorphism, not merely degreewise isomorphisms. The equations for the inclusion, negative projection and quotient are written explicitly. Additivity preserves negatives; the termwise shift comparison therefore has no extra sign. Element notation abbreviates biproduct maps and does not assume the categories are module categories.

Step 3 cites lem-pc-cone-short-exact-quasi-iso, whose entire statement is the canonical quotient quasi-isomorphism for any abelian category. I read its Mathlib match CochainComplex.mappingCone.quasiIso_descShortComplex and the descShortComplex definition. Applying it in B is legitimate exactly because the image row is assumed short exact. The two definition-node statements supply localization, the signed cone distinguished triangle, and the full triangulated bounded-below subcategory. Transport along Qq is written as composition with its inverse, giving the exact negative-projection formula. I did not cite lem-weil-pbc-complex-ses-triangle for a formula absent from that node's statement.

Step 4 uses the full statement of lem-weil-pbc-right-derived-plus-injective: the unit is natural on the homotopy category and invertible on every bounded-below complex of injectives. Step 1 verifies this for P as well as for the three row complexes. Naturality at u and v gives the two ordinary triangle squares, and naturality at q plus the explicit equation q_Tχ=Tq gives the cone-quotient comparison. This does not require T to preserve arbitrary quasi-isomorphisms.

Step 5 cites lem-sc-p1-right-derived-injective-boundary. I opened the node and its live upstream Lean declaration and read the displayed equation, whose shift comparison and inverse units are exactly the ones used here. Its statement allows arbitrary additive T; assumes enough injectives only in A; takes a bounded-below short complex with injective terms at all three vertices; and requires the original and image rows short exact. Each of these hypotheses is present in the item. The canonical SES boundary uses the localization's factorization and shift maps; after these standard identifications the cone quotient construction in Step 3 is the same canonical boundary. The equation is reproduced in conventional right-to-left composition notation in the proof. Thus no unsupported 'compatibility with the boundary' is hidden. The endpoint inverses and the three commuting squares give an isomorphism of triangles; distinguishedness follows from the already distinguished target triangle.

Step 6 is the strict cone calculation from the Tag 0152 naturality proof: diagonal maps commute with the differential using the first row square, commute with q using the second row square, and commute with the negative projection directly. After localization, cancellation of the two invertible quotient maps gives the displayed boundary naturality equation. Naturality of α from the cited right-derived node and naturality of biproduct projections finish naturality of the comparison. No unchosen homotopy or functorial-cone assertion for arbitrary derived morphisms is assumed.

I checked the zero row and T=0: all comparisons are the zero-object isomorphisms and the formulas hold. For T=identity, χ and the units give the original cone-quotient triangle. For E=0 or G=0 the quotient formula gives the corresponding degenerate triangle. I also checked a nontrivial two-term complex: the -d on the shifted summand is necessary and the last projection retains the minus sign. The proof works at any common integer lower bound, including negative ones. No smallness-dependent colimit or new existence statement is introduced.

I checked delivery-errors B–E: there are no new statement-only nodes needing separate sources/searches or same-tag comparisons; the existing item's statement is retained; every cited statement has been opened and quoted in citations.json; no step draws on a cited proof instead of its statement. I checked the dependency closure of the boundary node and found no path back to this item. Every step is shorter than 2000 characters (the longest is 671), and the only substantive generic boundary theorem is cited rather than re-created. The actual Mathlib searches returned generic unit/shift infrastructure, mapping-cone functoriality and SES triangles, which do not collectively make the entire assertion a one-line Mathlib specialization.

## Unfinished work

None in the stage-1 split. No Lean was written and no compiler or build was run. Final delivery still undergoes the maintainer's independent mathematical review.
