# Worker report: lem-sfb-normal-curve-punctured-generic-model

Group Q25; stage 1; 2026-10-24. Direct delivery, with the maintainer as independent reader.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normal-curve-punctured-generic-model.json: statement, split into seven proof steps; statement unchanged; inherited source, provenance and Mathlib searches retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-generic-morphism-open-extension.json: statement, Mathlib leaf. AlgebraicGeometry.spread_out_of_isGermInjective' at Mathlib/AlgebraicGeometry/SpreadingOut.lean:374-378 specializes at the generic point of an integral scheme; the required germ-injectivity instance is at lines 160-167. All clauses, including the exact generic restriction and the equality over the base, are in this single theorem.
- citations.json: 17 entries, one for each step/node citation. The quote in each entry is the complete verbatim statement; this is intentional so a reader can assess each interface in context.

One new node; one Mathlib leaf; no new unsplit nodes. The helper write_split.py is sandbox-only generation code, not part of the delivery.

## Attachments

None for the item: searches in lean/WeilConjectures by its blueprint tag and by normalization, punctured curve and generic-map concepts found no exact declaration covering all its hypotheses and conclusions. The proved AlgebraicGeometry.IsConnectedCurve.normalizationIn in AlgebraicGeometry/Curve/Affine.lean:70 assumes an algebraically closed field and a smooth input curve, and does not give a prescribed punctured morphism. It cannot attach this item. The existing node lem-sbc-normalization-generic-field already records its own proved project declaration and is cited, not recreated.

## WANTED

None. The item and the new leaf have their sources locally in Stacks.

## Corrections and scope

No statement dispute or change was necessary. The source proof is Stacks Tag 0GWV, limits-lemma-essentially-finite-type-criterion-universally-closed, final paragraph, read in literature/stacks-project/limits.tex:4330-4370. The spreading input is Tag 0BX8(3), morphisms-lemma-rational-map-finite-presentation, read in literature/stacks-project/morphisms.tex:12609-12660. I also read Tag 035L, morphisms-lemma-normal-normalization, and the neighboring finite-normalization lemma in morphisms.tex:14170-14260 to check the normality and finiteness route. Existing nodes supply these inputs; I did not create another normalization theorem.

The shrinking is made more explicit than in 0GWV: first prove that the affine normalization has dimension one, decompose the proper closed missing set into finitely many closed points, then choose a product of elements separating every unwanted point from c. Its principal open is affine and of finite type, so there is no tacit quasi-compactness assertion about an arbitrary open.

The chapter and unit records, their three-level route, and the current blueprint unit and direct-image proof were read. The current source is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3). This item is a generic properness-test input deep in its inherited route, not a replacement for that clause. tools/blueprint_refs.py ancestor returns None for this already broken provenance chain; I preserve the inherited null from.node and via list and extend the place precisely for the new input. No ancestor id was invented. The generic inputs from other units are declared with reasons in split_report.tool_uses.

## Searches and reuse

I searched the full DAG for the normalization-in-extension, dimension, lying-over, maximality, Noetherian components and rational-map statements, and specifically for Tag 0BX8. I ran tools/blueprint_refs.py search for rational/map, normalization/extension, 0BX8, and generic/morphism. None states the new generic spreading input. The two existing 0BX8 references are the item and its parent; neither is a duplicate of the general spreading theorem.

The item arrived without a sandbox node, report or search log. Its existing Q09 Mathlib records have been retained. Fresh Q25 queries for the whole item again found only generic spreading and relative normalization, not the full prescribed-point punctured construction. For the new leaf, the two semantic phrasings and LeanSearch returned RationalMap.ofFunctionField, its exact restriction identity and PartialMap.ofFromSpecStalk. I read those candidates in Birational/RationalMap.lean:215-239 and 516-548. Grep and Loogle then found the more direct spread_out_of_isGermInjective' theorem, whose full type and source I read. Its three output clauses match the new node without any separation hypothesis. The additional instance read supplies germ injectivity for every point of an integral scheme. The queries, hits and digests are in searches.jsonl exactly as produced by the required msearch.py command; the new leaf records the corresponding tool/query text and results. No unrun query is recorded.

## Not duplicates

lem-sfb-generic-morphism-open-extension vs lem-sfb-normal-curve-punctured-generic-model: both cite 0BX8, but the new node extends a generic morphism on any integral source to an open, while the item constructs a normal finite-type curve with a closed point over y, prescribed finite generic extension, and a map on the entire punctured curve.

lem-sfb-generic-morphism-open-extension vs lem-sfb-normal-curve-universal-closedness-test: both cite 0BX8, but the new node is generic-map spreading on an arbitrary integral source; the existing node is a universal-closedness criterion using punctured normal curve tests and their lifts. It depends on this item, and is never cited back by this split.

## Review by Q25

I checked delivery-errors B through E with the sources and every cited statement open. The new node is statement-only, self-contained, and has explicit definition dependencies; it carries no hidden proof or merely restated construction of the item. Its source is 0BX8(3) with the actual .tex label. Its Mathlib match names the source file and lines and the integral-source instance, and every recorded search was actually run through msearch.py. I checked that its conclusion is existence of an open representative of the *given* generic morphism, rather than just some rational map with an isomorphic field. All seven item steps are shorter than 2000 characters.

Step 1 uses lem-sc-integral-function-field-affine-fraction for the identification of K with Frac(A), def-fin-normalization-extension for the concrete B inside L, lem-weil-pbc-normalization-normal-stalks for integrally closed local domains, lem-fin-normalization-extension-finite for the finite normalization, and def-weil-finite-integral-morphism for the finite module description. The normality node applies to Spec(L), which is integral with its unique local ring a field. Its morphism to affine T is affine, hence quasi-compact and quasi-separated. I checked that the concrete integral-closure construction is the relative normalization used in its statement. Finiteness needs only finite L/K and finite-type integral T over a field, exactly the available hypotheses, not separability.

Step 2 uses lem-weil-pbc-finite-type-domain-dimension-local-ring at the maximal ideal corresponding to the *closed* point y, lem-weil-pbc-integral-injective-dimension-equal for A contained integrally in B, and lem-wf-affine-noetherian-components after explicitly showing that B is finitely generated over k. Both rings are domains; the inclusion is injective because they are subrings of the specified fields. No transcendence-degree or dimension formula not stated by a citation is used.

Step 3 uses lem-weil-pbc-integral-injective-lying-over to choose the prime over y; lem-weil-pbc-integral-prime-over-maximal-maximal makes it maximal. The same local-dimension node now applies to the finite-type k-domain B and gives local dimension one at c. Finally lem-sbc-normalization-generic-field states the compatible Spec isomorphism and exact equality with the canonical map, so it provides the required identification with *this* L over T and therefore over K, not an arbitrary abstract field isomorphism.

Step 4 uses both directions of lem-weil-pbc-lft-affine-pairs. Its statement really covers every affine source/target pair. The finite set of k-algebra generators is also a generating set over the target affine ring because the ring maps preserve k. This short algebra calculation proves f locally of finite type; I have not silently assumed that a morphism between schemes locally of finite type is separated or quasi-compact.

Step 5 uses only the new generic-extension leaf, with base Y, source N and target W. Step 4 supplies its locally finite type hypothesis, Step 1 its integrality hypothesis, and Step 3 the exact identification of the given generic map. The assumed equality fu = ip on Spec(L) is precisely the base compatibility needed. The leaf gives equality over Y already on its open representative. Thus there is no invalid appeal to global uniqueness of maps into a nonseparated target. Its k-linearity follows by composing that equality with the structure map of Y.

Step 6 uses lem-sc-noetherian-closed-subset-finite-components for the proper closed E in Noetherian N and lem-sc-scheme-sober for each component's generic point. Neither node is used to assert a finite set of points directly: the text proves each component is a closed point by the one-dimensional prime-chain argument. The elements separating distinct maximal ideals, their finite product and the resulting principal open are written out; these are elementary consequences of maximality and primeness. The case Sigma empty is covered by product 1. Removal of c from the representative does not lose the generic point because c has local dimension one.

Step 7 uses def-weil-open-immersion only for the actual identification with an open subscheme, hence its unchanged local rings. The presentation B_s = B[t]/(st-1) explicitly verifies finite type, and the restrictions of p_N and b give all equalities and preserve the generic field and exact u. Every clause of the item, including normality, p(c)=y, local dimension one, K-compatibility, and exact generic restriction, is checked here or in the cited earlier steps.

I tested the construction on A=k[t], y=(t), L=K (including empty Sigma); on inseparable L=k(t^(1/p)) in characteristic p; and on a singular integral affine curve where its normalization can have several points over y. Lying-over selects just one of those points, and the separating product removes any others in the missing set. None of these cases needs smoothness or a perfect field. The zero-dimensional input cannot occur, because the hypothesis on the local dimension at y excludes it. The spreading leaf also handles zero-dimensional integral X: its generic point is then already an open point and the stated extension has no extra condition. Nonseparated targets are allowed because the spreading equality is over Y, not deduced from agreement at all of N. I verified every citations.json quote directly against the corresponding statement, checked the dependency directions to avoid citing the parent criterion back, and left no unresolved mathematical obligation beyond existing DAG nodes.

## Unfinished work

None in this stage-1 split. No Lean file was written and no compiler, Lake or build command was run. The first server dry run required an explicit mathlib_match.line field even though the verified line already appeared in how; I added line 374. The required final server dry run and push follow this self-review.
