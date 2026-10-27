# Worker report

Item: lem-sf-rational-localization-triangle-orthogonality. Group: Q57. Stage 1 only; 2026-10-22.

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-rational-localization-triangle-orthogonality.json: statement, split into eight proof steps; no complete Mathlib match.
- citations.json: 22 exact statement quotations, one for each step/node citation.
- report.md: this report and signed review.

New nodes: 0. New Mathlib leaves: 0. No Lean files, repository files, launcher files, unit records or chapter records were changed. The sandbox initially had only dispatcher marker files, with no earlier split/report to reuse. Original item fields, statement, blueprint attribution, O1 searches and creation metadata are retained.

## Attachments

None. I searched the project under lean/WeilConjectures both for the exact blueprint tag and for rational open/closed triangles and extension by zero. RationalizationRecollement.lean supplies generic scalar-localization adjunction machinery; LocalizationRational.lean gives the other supported triangle i_*i^! -> id -> Rj_*j^*, with Hom(i_*Q[m],Rj_*G)=0. Those are not every clause of this item, whose triangle begins j_!j^* and whose vanishing has arbitrary open objects on the left. Neither is an attachment for this item. CompactSupportIntegral.lean rationalizes compact support but does not state the whole item.

## WANTED

None. All documents needed here are already local.

## Corrections and scope

The statement is retained verbatim. There is no statement dispute or change to the unit route. The unsplit seed had no argument. I supplied the integral prerequisite identifications, then the rational argument. In particular I did not cite the parent prop-sf-open-closed-triangle-all-stages, which already depends on this item, and did not cite its same-K Hom clause for cross-object Hom vanishing. I also did not use prop-weil-open-closed-recollement-adjunctions as an integral theorem: its statement is only for finite constant coefficients.

The current main-20261015 rational-stage paragraph of prop-sf-open-closed-triangle-all-stages.proof.md is the item's source. The source's brief reference to exact R-linear functors and localized maps is expanded below; it is not used as a black-box proof. All non-elementary inputs are existing nodes. Generic off-unit inputs have explanations in split_report.tool_uses; the route remains the unit's actual open/closed operations and adjunction maps. No SGA source is used.

## Searches and duplicate audit

Read the whole chapter/unit records and SETUP's three levels. Searched the entire imported blueprint with blueprint_refs.py for rationalization, adjunction scalar, and orthogonality, and computed the nearest ancestor (prop-sf-open-closed-triangle-all-stages). Searched the DAG by statements/key words and inspected the existing comparison, exactness, adjunction and scalar-localization nodes. There is no other blueprint node stating the complete item in another form: same_as is []. No new node was necessary, so there are no new/existing-node duplicate pairs or new source-tag collisions.

Ran and read msearch.py LeanFinder, Loogle, grep and LeanSearch for this item, with a second LeanFinder phrasing. The search log is searches.jsonl and the exact queries/results are appended to mathlib_searches. All services returned hits. Read Mathlib/CategoryTheory/Localization/Adjunction.lean, especially localization and localization_unit_app/localization_counit_app (lines 89, 118, 125). These are genuine generic adjunction tools, but do not identify the particular completed integral sheaf operations or prove their cross-object vanishing. The existing generic node lem-pur-semilinear-scalar-localization already supplies extension of transformations and equations; the elementary unit/counit calculation in step 6 therefore needs no new node. The second phrasing returned generic Ext exact-functor results, not the item.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own statuses; no claim is made to have proved their Lean declarations. The server review_split check passed. The required delivery dry run passed with preflight accepted; the final delivery push follows the checked package.

## Not duplicates

No new nodes; no pairs to distinguish.

## Review by Q57

I checked the split against sections B–E of delivery-errors.md, reading their full text (including the merged new-target copy). I read the main-20261015 parent proof, with particular attention to the rational-stage paragraph and the integral-stage operation comparisons. I also read the chapter and sk-prop-sf-open-closed-triangle unit records: this split preserves their triangle and their actual counit/unit route. The natural-language proof is marked agent-written because the blueprint itself is agent-written and the explicit rational-adjunction calculation is my expansion.

Step 1 uses the statement of lem-sf-open-roos-unit-adjunction for Noetherian/qcqs and quasi-compact-open hypotheses, finiteness/perfectness of the DVR quotients, and the actual coefficient identifications. Its finite-type hypotheses hold for the given X and U; identities supply the same conclusions on Z when needed. The statement of lem-weil-pbc-profinite-coefficient-inverse-image gives the canonical ring-sheaf isomorphism for i and j, including preservation of constant sections and quotient projections. I checked that these are completed coefficient sheaves, not constant R-sheaves. I read Stacks proetale.tex Tags 099M/099N (lemma-naive-completion / lemma-pushforward-Noetherian-case) and used the node's explicit refinement rather than silently extending a constant-coefficient Stacks assertion.

Step 2 uses the definition def-sf-proetale-ring-sheaf-operations for the actual functors and adjunctions, lem-weil-pbc-proetale-ringed-open-closed for exact j_!, exact i_* and j^*i_*=0 with arbitrary ring sheaves, and lem-weil-pbc-proetale-immersion-limit-preservation for exact module inverse images. The latter permits a coefficient ring-sheaf isomorphism, exactly what step 1 supplies. lem-sf-exact-functor-derived-triangulated gives the derived exactness and shifts; lem-weil-pbc-exact-functor-derived-functor identifies the derived functors with those termwise models. R-linearity here is the direct module-map calculation preserving the same constant scalar r. I read Stacks proetale.tex Tag 09BM, lemma-closed-immersion-complement-retrocompact-exact, sites-modules.tex Tags 03DI/03DJ, lemma-extension-by-zero / lemma-extension-by-zero-exact, and derived.tex Tag 015F, lemma-right-derived-exact-functor. The needed retrocompactness follows from step 1.

Step 3 reads and uses the full statements of seven existing nodes. lem-sf-immersion-completed-pullback-comparison supplies both the specified ordinary/completed isomorphism and integral constructibility. lem-sf-integral-open-reduction-comparison supplies completeness, a strict reduction-system isomorphism, the specified actual completion unit, and the adjunction-map identification for j_!, not merely the right vertices. def-weil-integral-rational-qbar-compact-support is used only for its strict-limit definition. lem-sf-open-finite-constructibility-interval gives finite constructibility with the same interval for every quotient. prop-weil-pbc-direct-image-limits supplies the canonical strict-tower comparison for the actual i_* of def-weil-derived-direct-image and the finite-reduction isomorphisms; its adic hypotheses were checked in step 1. lem-sf-finite-immersion-constructibility-interval supplies the same bounded interval for closed direct image. These facts and the definition of the intrinsic integral category give preservation of the full subcategories; no unproved uniformity assumption is added. I read Stacks sites-cohomology.tex Tag 0A07, lemma-Rf-commutes-with-Rlim, and proetale.tex Tag 099N, and distinguish their statements from the explicit completed-coefficient refinements in the cited node. The open strict-system refinement is used as exactly stated in its node, whose source is Tag 0GL1, lemma-j-shriek-and-tensor, not as a claim that the Stacks tag alone constructs the system comparisons.

Step 4 uses def-sf-proetale-ring-sheaf-operations for the actual abelian adjunctions and lem-sc-derived-adjunction-from-underived for their derived adjunctions. I read Stacks derived.tex Tag 09T5, lemma-derived-adjoint-functors. The functors are exact and have the termwise derived models from step 2, so this is a legitimate application to the supplied comparisons. Step 3 identifies the normalized complete-category operations, and fullness permits restricting the Hom bijections and units/counits, without any essential-image assumption. The cited ringed-open/closed node states j^{-1}i_*=0; applying the exact operations termwise proves the required derived zero on every closed complex.

Step 5 uses lem-pur-semilinear-scalar-localization with the identity R->R and t inverted on both sides. Its statement explicitly gives unique extension on objects/morphisms, natural transformations, shift comparisons and exactness. The hypotheses, including integral exactness and linearity, were established in steps 2–3. def-weil-rationalization-karoubi says raw localization has the same objects and the tensor Hom formula; it introduces no summand objects. I compared this with the main-20261015 rational-stage paragraph and the actual defining formulas for pullback, direct image and compact support. The generic extension identifies the actual operations by their formulas, not by choosing arbitrary vertex isomorphisms.

Step 6 takes only the transformation/equation clause of that same generic node. I wrote out the two Hom maps and the naturality argument on arbitrary finite sums of pure tensors. The triangle identities prove they are inverse. Thus a morphism f/t^n, or a sum of such expressions with no integral representative, is included. Components of the open counit and closed unit are literally the localized specified components. This is a few-line application of the cited transformation theorem and the definition of an adjunction, not a new lemma restating one clause of the item.

Step 7 uses precisely the conclusion of lem-weil-linear-scalar-localization-triangulated that Q is exact. I read derived.tex Tag 05R6, proposition-construct-localization, including its image-triangle definition, and the definition of exact functor there. The last arrow uses the canonical shift comparison. The given completion is arbitrary, so no cone uniqueness assertion or replacement completion is smuggled into the argument. Steps 5–6 identify the first maps with the normalized rational counit/unit.

Step 8 uses the already-established integral adjunction and disjoint-support zero for independent objects N and M, then the exact Hom tensor formula from def-weil-rationalization-karoubi. The displayed Hom adjunction and 0 tensor E calculation prove the assertion without a new node. I checked zero N or M, empty U or Z, nonreduced closed Z, every integer shift including negative ones, t-torsion objects that become zero after localization, and rational arrows with denominators: all remain covered. In particular no same-K hypothesis and no torsion-freeness or flatness assumption on the integral Hom module is used.

For C4, citations.json quotes the exact statements, one per cited node per step; each was opened and read. For C1, the only computations not cited are module scalar compatibility, restriction of a Hom adjunction to full preserved subcategories, the unit/counit formulas on tensor sums, the Hom-to-zero calculation, and 0 tensor E, all written in the proof. No additional comparison is proved inline. All eight steps are below 2000 characters. A source-only dependency traversal found no cycle from any cited input to the item. There are no new statements needing a separate small-case test, no new Mathlib leaves missing declaration lines, no orphan nodes, no relabeled clauses, and no unsupported source route changes.
