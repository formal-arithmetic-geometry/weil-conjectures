# Stage-1 delivery: lem-weil-pbc-finite-postnikov-isomorphism

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-postnikov-isomorphism.json`: statement, split into five proof steps. Mathlib verdict: no exact match for the arbitrary triangulated-target theorem. Existing searches retained; five further genuine searches recorded in the node and `searches.jsonl`.
- `citations.json`: one verbatim statement quotation for each node used in each proof step.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. No unit record is changed: this item realizes one part of the key node's existing proof, and is not the key node itself.

## Attachments

None for this item. I searched `lean/WeilConjectures/` for its exact id, Postnikov, and truncation/isomorphism terminology, and read `CategoryTheory/DerivedCategory/PlusDevissage.lean` and the triangulated functor/generator infrastructure. `DerivedCategory.Plus.isIso_app_of_isGE_of_isLE` (`PlusDevissage.lean:81`) proves a related finite-range result only for functors with target `Plus D` for an abelian category D. The present item allows an arbitrary triangulated target, so that declaration does not give the whole item. It must not be attached by silently specializing the item's target category.

Existing attached results reused without editing their records: `DerivedCategory.truncation_triangle` belongs to `lem-weil-pbc-truncation-triangle`; the three `CategoryTheory.NatTrans.isIso_app_obj*` declarations in `WeilConjectures/Mathlib/CategoryTheory/Triangulated/Functor.lean` belong to `lem-sf-triangle-two-out-of-three` and are recorded Lean-closed. The latter's statement includes exactly the required shift compatibility.

## WANTED

None. All sources used are present locally.

## Audit of the imported item and blueprint

The item's statement is retained verbatim; no dispute or hypothesis repair was needed. Its former empty proof left the actual finite induction to be supplied. The natural transformation is required to commute with the specified shift comparisons: this is used in step 3 and is exactly the compatibility hypothesis of the two-out-of-three node in step 4. Merely having a natural transformation between exact functors would not supply this hypothesis.

I read the chapter and unit records and the current main-20261015 `sk-thm-properbasechange.proof.md`, specifically the bounded-below-complexes paragraph. This split implements its finite Postnikov filtration and makes no replacement of the unit's route. The historical unit record still describes the older three-step torsion argument; the current blueprint's added bounded-below passage is the precise place inherited in the item's `blueprint.from`. No change to either record is required here.

The abstract target category has no assumed cohomology functors, so the argument uses two-out-of-three for distinguished triangles in that target, rather than trying to detect its isomorphisms on cohomology. Cohomology detection is used only in the source derived category, for the zero base case. No t-exactness or cohomological-dimension condition on the two functors is used or added.

## Not duplicates

No new nodes were created. Before deciding this, I searched the whole DAG by `08J5`, `Postnikov`, successive truncations, two-out-of-three, and the relevant Lean declaration names, and ran `tools/blueprint_refs.py ancestor` and `search` with `Postnikov`, `truncation triangle`, `two-out-of-three`, `finite range`, and `natural transformation`. The existing `lem-weil-pbc-truncation-triangle`, `lem-weil-pbc-truncation-cohomology`, `lem-weil-pbc-derived-plus-iso-on-cohomology`, and `lem-sf-triangle-two-out-of-three` give the needed results. No imported blueprint node found states the same arbitrary-target finite Postnikov conclusion. The related `sbc-lem-finite-range-comparison` concerns a specified etale exchange and spectral-sequence comparison, not this arbitrary transformation.

The zero-object calculation, the shift conjugation calculation, and integer induction remain explicit steps; creating nodes for these consequences of the cited statements and definitions would add elementary duplicates. Conversely, the genuine truncation-triangle and two-out-of-three theorems remain citations, rather than being relabelled as elementary steps.

## Mathlib search results

The five new queries are recorded exactly as run through the required `msearch.py`, including their actual result summaries in `searches.jsonl`. Both LeanFinder phrasings returned individual truncation or single-degree representation results, fraction lemmas, and homological-functor infrastructure. LeanSearch returned `Triangle.functorHomMk`, `Triangle.functorIsoMk`, `TStructure.truncLTι`, cochain truncation naturality, and `NatTrans.app_homology`. Their returned signatures do not state induction over the cohomological range. The Loogle conjunction returned zero hits, and the grep in `Algebra/Homology/DerivedCategory` returned zero hits. All services were available in these searches. The inherited nine searches and their results are preserved. No failed search was reported as evidence of absence.

## Review by N8

For the item I read Stacks `derived.tex`, Tag 08J5, label `remark-truncation-distinguished-triangle`, in particular its displayed successive-upper-truncation triangle. I also read `homology.tex`, Tag 0118, label `section-truncations`, including the explicit good truncation and its cohomology formula; `derived.tex`, Tag 05RU, label `definition-unbounded-derived-category`, for the full triangulated D+ category; and Tag 014A, label `lemma-third-isomorphism-triangle`, for two-out-of-three in an arbitrary pre-triangulated target. The last proof uses representable functors, so does not require the target to be a derived category. I read the definitions of triangles and exact functors in the same source (labels `definition-triangle` and `definition-exact-functor-triangulated-categories`) to check the order of the shift-comparison maps. There are no new nodes needing separate sources.

I opened and read the statement of every cited node. Step 1 uses the two explicit cohomology clauses of `lem-weil-pbc-truncation-cohomology`, and the inherited full triangulated structure and shift closure stated in `def-weil-pbc-bounded-derived-subcategories`. Their hypotheses are exactly an abelian category, canonical truncations, and the given cohomological lower bound; no strictly bounded complex representative is assumed. The single-degree objects also belong to D+ even when their degree is negative.

Step 2 uses `lem-weil-pbc-derived-plus-iso-on-cohomology` only for the map from the acyclic truncation to zero in D+. Its statement is for any abelian category, not only sheaves. All source and target cohomology objects of this map are zero, so its cohomology maps are isomorphisms. `def-weil-triangulated-category` explicitly defines an exact triangulated functor to be additive. Applying additivity to the zero identity proves the two image objects are zero objects; the reverse zero map is written as a two-sided inverse of the actual component. This avoids assuming that a functor preserves a chosen zero object literally.

Step 3 uses the shift autoequivalence from `def-weil-triangulated-category` and the item's equation itself. The displayed conjugation proves the positive shift case, and applying the same equivalence at M[-1] proves the negative case. The naturality conjugation under an isomorphism handles the canonical associations of iterated shifts. Thus the degree-zero hypothesis gives the component on H^q(E)[-q], with the correct negative sign and with no claim that natural transformations are determined by their values on generators.

Step 4 uses the actual statement of `lem-weil-pbc-truncation-triangle`: it gives the successive triangle, including its H^q[-q] third term and bounded-below assertion. I read its project declaration and docstring in `CategoryTheory/TruncationTriangle.lean`; the item needs only the existence and boundedness clauses, not its extra uniqueness assertion. The statement of `lem-sf-triangle-two-out-of-three` takes arbitrary triangulated categories, exact functors, and precisely the same shift equation as this item. Substituting D+(A) for its source and the item's T for its target meets all hypotheses. The induction supplies the first component and step 3 supplies the third, so its conclusion is exactly invertibility of the middle component. This is a generic formal tool, not an alternative proper-base-change route; its off-unit use is declared in `split_report.tool_uses`.

Step 5 is finite induction on the nonnegative integer b-a+1, with the base q=a-1 and successor q-1 to q explicitly set up. I checked the empty interval b=a-1, the one-degree interval b=a, the zero complex, a single nonzero cohomology object in either a positive or a negative degree, and objects unbounded above. Empty intervals use no cohomology-component hypotheses; in a one-degree interval the triangle has a zero first vertex; unbounded upper cohomology never enters any triangle used. For a non-split extension with several degrees, the triangles, rather than a direct-sum decomposition into cohomology, supply the induction. No step requires the Postnikov triangles to split.

All five proof steps have fewer than 2000 characters. I checked for hidden comparisons: cohomology preservation and the successive triangle are cited as statements, and shift propagation and the zero inverse are written out. `proof_deps` is exactly the union of the steps' `uses`. `citations.json` copies the relevant statement text verbatim, with complete hypotheses for the two-out-of-three citation. There is no dependency on this item below any cited node, no new statement to test or duplicate, no SGA source, no Lean write, and no compiler or Lake invocation.

## Unfinished work

None in the requested one-level split. The maintainer's independent mathematical review follows delivery.
