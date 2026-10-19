# Stage-1 report: lem-sf-closed-support-tor-bound

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sf-closed-support-tor-bound.json`: statement, now split into five steps; statement unchanged; no Mathlib match for the whole item.
- `citations.json`: seven citations, each accompanied by the full verbatim statement of the node actually used.
- `searches.jsonl`: six fresh searches made with msearch.py and read, supplementing the item's inherited searches.
- `report.md`: this report and the direct-delivery review below.

No new nodes, no new Mathlib leaves, and no unit or other existing node was edited. All authored files are in this item's sandbox. No Lean edits, compiler, Lake, global build, or git command was run.

## Attachments

No attachment for the item. Searches for its id and blueprint docstring tag in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found none. Concept searches led to `WeilConjectures/SixFunctors/Etale/Derived/Stability/ClosedImmersion.lean`, which I read. `AlgebraicGeometry.Etale.homologyConcentratedIn_obj₁` (line 89) proves a cohomology bound, not the Tor conclusion. `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_lowerStar` (line 115) assumes constructibility and an explicit projection-formula hypothesis hPF. Neither is a declaration of this item under its stated hypotheses. The exact tensor instances at Derived/Triangulated.lean lines 92 and 103 already belong to lem-kun-derived-tensor-triangulated; no attachment delta is requested.

## WANTED

None. The blueprint and all Stacks source used are available locally.

## Findings and changes

The inherited item had no proof. Its explicit assumptions already suffice; no statement dispute or correction is needed. The Tor argument needs a tensor triangle, the cohomology long exact sequence, exact inverse-image cohomology, and the monoidal comparison. Each is now a cited existing statement. In particular it is unnecessary to assume the projection formula that appears in the nearby Lean constructibility theorem.

The unchanged support triangle is an assumption: we do not reprove existence or use a constructibility theorem to obtain it. I removed prop-weil-pbc-inverse-image-modules-exact from statement dependencies because exactness of i^* is already an explicit assumption, and added def-weil-pbc-inverse-image for the actual notion. The support triangle citation is retained as the precise unbounded constant-coefficient interface for the triangle and Rj_* in the statement. All other original fields are preserved; the blueprint place now identifies both the closed-immersion paragraph in the current source and the parent split's step 3.

The source's unit writes the calculation on the pro-etale site, while the current parent split explicitly performs this subargument on the ordinary small etale site before site transport. This item follows that ordinary-etale calculation. There is no passage between coefficient categories in this proof and no change to the unit route.

## Not duplicates

No new nodes were created. Whole-DAG statement/title searches and blueprint searches for `closed support`, `Tor amplitude upper`, `Tor amplitude triangle`, `long exact cohomology`, and `inverse image tensor` were read. The close candidate prop-exc-closed-tor assumes residue-DVR coefficients, bounded constructibility, a uniform bound on all R^q j_*, and preservation of constructibility; this item instead assumes a Tor bound on the particular object Q and the support triangle, and applies to any finite commutative A. It is not an equivalent statement. Existing general tensor, cohomology, and exact-functor nodes were reused instead of creating their closed-immersion special cases.

## Searches

The six fresh commands are recorded verbatim in searches.jsonl and in the item's mathlib_searches, with their real results. LeanFinder was run on the closed-immersion bound, then on a second phrasing using the fibre of a morphism and exact restriction. Both returned derived t-structure bounds, not a Tor statement. LeanSearch returned triangle-object and triangulated-subcategory declarations, none of which quantifies over tensor tests or compares the closed inverse image. Loogle on `"torAmplitude"` returned no hits. Source grep for the Tor-bound names, first across Mathlib and then across Algebra/Homology with a broader Tor-amplitude expression, returned no hits. All six services/commands completed successfully. The inherited searches are retained, not represented as fresh calls.

## Review by NS

I read the chapter record sec-six-functors-basics, unit record sk-prop-sf-rf-shriek-preservation, its current main-20261015 _section.md and proof.md, and the current parent node's closed-case steps. The precise source sentence is the explicit interval [a,b+cd_l(j)+1] in the closed-immersion paragraph. The argument below supplies its tensor-test and endpoint details while keeping the item's already separated hypotheses on Q. There are no new nodes whose sources need separate review.

For step 1, I opened lem-sf-exact-functor-derived-triangulated and read its full statement. It supplies the termwise induced functor for an exact additive functor between abelian categories and its action on single-degree complexes. I read Stacks derived.tex Tag 015F, lemma-right-derived-exact-functor. Both i_* and i^* are exact by this item's assumptions. Applying the given natural sheaf counit to every term of a representative complex commutes with differentials and is an isomorphism term by term, hence gives the displayed derived isomorphism. This is a two-line specialization, not a hidden new lemma. In particular i_*N is an actual degree-zero sheaf test, not an uncontrolled derived direct image. The proof uses the counit i^*i_* to identify E, not the unrelated counit i_*i^times.

For step 2, I opened lem-kun-derived-tensor-triangulated and def-kun-tor-amplitude, reading the actual statements. The former explicitly says that tensoring on either side by any fixed derived object is a triangulated functor, with no flatness or boundedness condition on that object. The latter quantifies over every module sheaf on the same small etale site. Thus M=i_*N is permitted. I read Stacks sites-cohomology.tex Tags 06YM (lemma-derived-tor-exact) and 06YU (definition-derived-tor), including the paragraph descending the K-flat tensor functor to D(O). Exactness here is the triangulated exactness of derived tensor, not ordinary tensor exactness with a nonflat sheaf.

For step 3, I opened lem-sf-derived-homology-long-exact and checked its statement for an arbitrary abelian category, every distinguished triangle and every integer degree. It gives exactly the adjacent segment used, with Q in degree r-1 and F and K in degree r. I read derived.tex Tag 0147 (definition-homological and equation-long-exact-cohomology-sequence), Tag 05RS (lemma-cohomology-homological), and the subsequent acyclic-localization/derived-category paragraphs. Tag 05RS itself is formulated on K(A); the following localization gives the D(A) cohomology used in the existing node. The inequalities are written out: r<a forces r-1<a; r>b+e+1 forces r-1>b+e and r>b using e>=0. Exactness between zero outer terms gives the desired zero middle term. No shift convention is silently reversed.

For step 4, I opened lem-weil-pbc-exact-functor-bounded-below and read its full statement rather than relying on its title. Its first conclusion is H^r(FK) isomorphic to F(H^rK) for EVERY derived object K and every r, without a bounded-below assumption. That is exactly what is applied to i^*. I also read its Stacks source Tag 015F and homology.tex Tag 010N (lemma-exact-functor). Exactness ensures preservation of zero. Thus this step does not assume flatness of N, boundedness of a tensor representative, constructibility, a finite cohomological dimension, or a projection formula. This non-Mathlib generic tool is declared in split_report.tool_uses because no statement in the item unit supplies its general cohomology interface.

For step 5, I opened lem-kun-inverse-image-monoidal and reread its full statement, including the canonical comparison's direction. I read Stacks sites-cohomology.tex Tag 07A4 (lemma-pullback-tensor-product). The existing node already specializes the ringed-topos result to ordinary constant coefficients on small etale sites, so no extra coefficient identification is assumed here. The ring A is commutative as required and i is a scheme morphism. Inverting that isomorphism gives i^*(F tensor M) isomorphic to i^*F tensor i^*M; step 1 then gives E tensor N. Cohomology preserves these isomorphisms. Since N was arbitrary, the final use of def-kun-tor-amplitude is precisely its universally quantified definition. This step has no separate assertion that i_* preserves tensor products.

I checked delivery-errors B1-B10: no new statement-only node or Mathlib leaf was manufactured, all original hypotheses and conclusions remain, the notions are named by existing definition nodes, TeX is escaped once, source labels/tags are explicit, ancestry is retained, and the nearby existing Lean statements were not mistaken for an exact attachment. For C1-C8, every substantive tool in the five steps is one of the seven citation occurrences in citations.json, copied from the opened statements; no proof-internal construction is borrowed. The off-unit general exact-functor cohomology statement is declared as a tool, while the other proof tools are Mathlib leaves or already Lean-closed. No node downstream of this item is cited. For D1-D5 the steps contain the tensor-test argument and the endpoint inequalities themselves, and do not transfer the conclusion to a new lemma.

For E1-E7 I checked arbitrary integers a<=b, e>=0, ordinary constant-A coefficients, and the natural counit assumption at the precise steps described above. Small cases: e=0 still yields [a,b+1]; r=a-1 and r=b+e+2 both vanish, while r=a and r=b+e+1 are correctly retained. If Q=0 the LES even gives the narrower bound [a,b], so the stated one remains valid. If Z is empty all test sheaves are zero; if i is the identity, the same argument still works. A=0, N=0, and K=Q=0 give zero complexes and cause no exception. No invertibility of the order of A, characteristic restriction, finite-type hypothesis, quasi-compactness or Noetherian hypothesis is used. I found no counterexample and no false source inference. All five steps are below 600 characters, so there is no non-elementary step above the 2000-character review threshold.

The main corrections during this self-review were to cite the existing general cohomology comparison explicitly rather than leave t-exactness implicit, and to distinguish the exact item's hypotheses from the stronger nearby Lean theorem. No second agent was started; this review is my signature under the direct-delivery brief.

## Unfinished work

None for this one-level split. The item reuses existing lower nodes and does not claim their unsplit branches are newly finished.
