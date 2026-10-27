# Worker report: lem-pur-kummer-line-inclusion-over

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-kummer-line-inclusion-over.json: existing statement item, now split into two elementary steps. Statement and stmt_deps unchanged. Added precise proof citations, an agent proof_origin, current Mathlib searches and split_report.
- citations.json: verbatim statement excerpts for all five step/node citation pairs.
- report.md: this report.
- searches.jsonl: the search command's own log, retained unmodified.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures and lean/Sheaf by the blueprint tag, normalizedKummerInclusion_over, KummerLine, and punctured-line/Laurent concepts. The exact declaration AlgebraicGeometry.Etale.normalizedKummerInclusion_over in lean/Sheaf/AlgebraicGeometry/KummerLineInclusionOver.lean:18 states the item but contains sorry at line 21. The upstream WeilConjectures declarations found by the conceptual searches concern Kummer cohomology or other presentations of the relative punctured line; none states this exact field-model equation with a finished proof.

## WANTED

None.

## Problems corrected

The imported proof's conclusion is correct, but it had empty uses despite using the coordinate models and contravariant Spec functoriality. It did not provide the coefficient calculation or cite statements supporting it. Added those details and exact citations. There is no statement dispute and no change to its quantification over all fields. The existing reviewed record is a stage-2 statement review, not a finished stage-1 proof, and the existing Lean proof is sorry. Maintainer-owned fields were preserved.

The current blueprint file under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/prop-pur-gm-relative-kummer.proof.md, Step 2 final paragraph, uses π = pj and restriction along j. The helper verifies that relation for the explicitly chosen field models used earlier in the step. The unit and chapter records were read; this argument stays below the unit's route and uses no purity theorem, SGA source, cohomology computation or altered coefficient category. The unit record's older text is not used as a substitute for the latest blueprint. This helper is not the key node of the unit, so no realization fields are changed.

## Unfinished work

None for this stage-1 item. No Lean was written, compiled or built. The live library and launcher were only read; all writes were within this item's sandbox or were the authorized search/delivery commands.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. Whole-DAG searches for Polynomial.toLaurent, its constant compatibility, Spec.map_comp, and the inclusion equation found the existing geometry and affine-spectrum definition nodes used here. Whole-blueprint searches using blueprint_refs.py for Laurent, Spec and punctured-line inclusion found no blueprint statement duplicating this equation (the Laurent matches concern the group definition and a reciprocity identity). The ancestor command confirms prop-pur-gm-relative-kummer. Kept the existing precise from.place and via list; same_as is empty.

## Mathlib assessment

Ran the required searches through msearch.py and read their hits; the query texts and command results are recorded in searches.jsonl and in the item. A first Loogle query used the nonexistent name LaurentPolynomial.ofPolynomial, which the service reported; the second query used Polynomial.toLaurent and returned the relevant constants lemmas. Both semantic phrasings were run. LeanSearch and LeanFinder were available. Direct source reading confirmed Polynomial.toLaurent_C at Mathlib/Algebra/Polynomial/Laurent.lean:189 and Polynomial.toLaurent_comp_C at line 194, and AlgebraicGeometry.Spec.map_comp at Mathlib/AlgebraicGeometry/Scheme.lean:488. These are the two ingredients of the calculation, not an existing declaration stating the complete scheme equation after a single specialization. The coefficient equality is an explicit elementary step, and Spec functoriality is already part of the statement of the Mathlib-leaf definition def-weil-affine-spectrum; no new lemma is necessary. In particular, a lemma restating either clause of this tiny calculation would be unnecessary fragmentation. The original searches were retained; the added records describe only searches actually run during this work.

## Review by NI

I read the latest blueprint's unit statement and full proof of prop-pur-gm-relative-kummer, the DAG chapter and unit records, and the actual definitions in lean/Sheaf/AlgebraicGeometry/KummerLineGeometry.lean. For the item I compared the formula with its stage-2 Lean declaration: inclusion is Spec.map of Polynomial.toLaurent, structureMap false is Spec.map of Polynomial.C, and structureMap true is Spec.map of LaurentPolynomial.C. Thus the written statement and Lean statement agree, including the order of the composite. There are no new nodes requiring additional source reviews. The proof is marked agent-written because it expands the coordinate calculation underlying the blueprint rather than claiming the blueprint supplies those details.

For step 1 I opened and read the statements of def-pur-kummer-line-geometry, def-weil-polynomial-ring, and def-weil-laurent-polynomial-ring. The first supplies exactly the two models, the standard structure maps and the polynomial-to-Laurent inclusion. The polynomial statement describes finitely supported nonnegative coefficient sequences, and the Laurent statement says coefficients are unique and that the polynomial subring consists of Laurent polynomials with zero negative coefficients. These statements justify the displayed computation: the constant polynomial has only its exponent-zero coefficient; retaining those coefficients in the Laurent ring gives the same constant. Equality is checked for every element of k, then ring-homomorphism extensionality gives the equality of maps. No assertion about localization exactness, open immersions, or Kummer classes enters this step. The corresponding Mathlib constant lemmas were read as a check on the actual coordinate implementation, not introduced as an uncited black box.

For step 2 I opened and read def-weil-affine-spectrum. Its statement explicitly says that ring homomorphisms induce scheme morphisms contravariantly and functorially. This is the exact property the proof applies, not a stronger fact inferred from its proof. I also checked Spec.map_comp in the local Mathlib source. Applying it to c_P followed by u gives Spec(u) followed by Spec(c_P), which has source C_true and target Spec k. Substituting step 1 yields Spec(c_L). The geometry-node citation supplies the identification of each of these three scheme maps with the item's named maps. citations.json quotes the actual sentences from all cited statements, rather than adapting a quotation to the desired argument.

I checked the requirements B through E against the final JSON: there is no new statement-only node to populate or search, no duplicated or hidden lemma, no clause moved out of the item, no off-unit theorem or cycle introduced, and no unsupported non-elementary step. Both steps are short calculations from the cited statements (558 and 388 characters), so neither falls under the long-step review threshold. The existing stmt_deps already contains the only node whose named construction the statement uses; proof_deps is exactly the union of the uses. The source pointers and all imported/maintainer fields remain intact.

I tested the argument at a = 0 and a = 1, over F_2 and F_3 as well as characteristic zero: the zero exponent is unchanged, every other coefficient is zero, and the composition order is the same. The proof uses only a commutative ring structure, so the stated field hypothesis suffices in every characteristic; it needs neither algebraic closure nor an invertible integer nor any coefficient-ring assumptions. I corrected the original empty proof citations and made the two elementary inferences explicit. Required server checks are run with deliver.py --no-push before the final push.
