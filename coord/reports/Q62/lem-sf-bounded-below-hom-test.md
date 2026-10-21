# Stage 1: lem-sf-bounded-below-hom-test

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sf-bounded-below-hom-test.json`: item, statement, now split; seven proof steps; no whole-item Mathlib match.
- `citations.json`: nine verbatim statement quotations for every step/node citation.
- `report.md`: this report.
- `searches.jsonl`: generated search-command log, retained unchanged.

There are **0 new nodes and 0 new Mathlib leaves**. The item statement and its statement dependencies are unchanged. Existing search records, creation data and blueprint provenance are retained; six actual Q62 searches are appended.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact blueprint id, bounded-below Hom detection/generation, brutal/stupid truncations and telescope terminology, and examined the derived-category and six-functor search results. No project declaration states this whole item. The existing module-category generation and bounded-below comparison declarations have different hypotheses/conclusions. The item is not an attachment to a Mathlib declaration.

## WANTED

None. The sources needed for this split are present locally.

## Defects and corrections

The seeded item had no proof. Its source refers to the final composition/open-locality paragraph of the upper-shriek preservation blueprint: this test was isolated by the parent's Q13 split, rather than explicitly proved in that paragraph. I supplied the missing generic detection argument without changing the parent unit route or the item statement.

The key distinction is the direction of truncation. Good lower truncations naturally receive a map from the original complex; they do not provide the increasing bounded-below subcomplexes required here. I used the stupid lower subcomplexes of an actual representative instead. I also avoided identifying a degreewise colimit with a colimit in the derived category or presuming that Hom out of an arbitrary object commutes with filtered colimits.

Mathlib searches: LeanFinder with two phrasings, Loogle, LeanSearch, and grep with two patterns (the second restricted to `Algebra/Homology/DerivedCategory`). The services returned results. The hits give localization/cohomology criteria or bounded representatives, not this detection theorem. I read `DerivedCategory.isIso_iff` in `HomologySequence.lean:88` and `isIso_Q_map_iff_quasiIso` in `Basic.lean:298`: neither turns the stated Hom tests into its hypotheses in one line. The corresponding declarations are not a match. Existing exactness is already the Mathlib leaf `lem-weil-pbc-hom-out-of-triangle-exact`; its two declarations were read at `Pretriangulated.lean:248,254`.

## Not duplicates

No new nodes. DAG statement searches found the exact tools already present and reused them. Blueprint searches for `truncation`, `bounded-below`, `hom-out-of-triangle`, and `detect isomorphisms` found no blueprint node stating the whole item in another form. `lem-weil-pbc-basis-derived-detection` concerns derived sections on affine pro-etale basis objects and bounded-below targets, so does not state this item. The sibling `lem-sf-localizing-hom-test` concerns a general localizing subcategory; it is neither copied nor used as a replacement for the argument here.

## Review by Q62

I read the chapter record, the four-step unit record and the current main-20261015 blueprint proof for `sk-prop-sf-rf-shriek-preservation`, along with the item, the stage-1 contract and both copies of delivery-errors B–E. This split provides the generic representing-object test needed by the final composition/open-locality comparison. It does not change any coefficient category or use SGA. The proof is marked agent-written because it combines existing Stacks arguments, rather than pretending that the blueprint contains this proof.

For step 1 I read Stacks `homology.tex`, Tag 0118, cochain stupid truncations, and the statements of `def-kun-truncations`, `def-weil-abstract-derived-category` and `def-weil-pbc-category-colimit`. They give exactly the lower subcomplex, localization and colimit notions used. The inclusions commute with the differentials including the boundary degree. Each truncation has a possibly different lower bound, which the item's quantifier permits. Eventual constancy in each degree supplies the colimit universal property explicitly; no global eventual stabilization is asserted.

For step 2 I read Stacks `derived.tex`, Tag 0949 (`lemma-colim-hocolim`) and Tag 090Z (`definition-derived-colimit`), and the whole statement of `lem-kun-complex-colimit-hocolim`. That statement explicitly includes sheaves of modules over an arbitrary sheaf of commutative rings on a site, arbitrary unbounded complexes, the actual derived coprojections, and transport of the distinguished triangle to the degreewise colimit. Thus it supplies every part of the telescope used here. The hypotheses agree with the item. I declared it in `split_report.tool_uses`: it is a generic construction absent from the upper-shriek unit, not a substitute geometric route.

For step 3 I read Tag 0146 (`lemma-composition-zero`) and the full triangulated-category definition node. The proof writes out its TR3 argument and uses TR2 for the remaining composites. It records the minus sign in the rotation, which matters in step 6. This is a few-line consequence of the axioms, so no new node is appropriate.

For step 4 the colimit universal property and the shift automorphism give exactly the product descriptions of Hom out of the coproduct and its shift. The inverse to each product map is coordinatewise. Both shifted and unshifted truncations are allowed tests. No countability-to-compactness inference or Hom/filtered-colimit interchange occurs.

For steps 5 and 6 I read Stacks Tag 0149 (`lemma-representable-homological`), both clauses of `lem-weil-pbc-hom-out-of-triangle-exact`, and its Mathlib declarations. Step 5 uses clause (i) to lift the map out of the second coproduct and clause (ii) to factor its residual. Step 6 uses clause (ii) first on the original triangle and then on its rotation. The rotated third arrow is exactly the recorded `v=-u[1]`. Each required zero composite, each injectivity use and each lift is written. This is the direct application of the cited exactness statements, not a hidden five-lemma or generation lemma. Step 7 constructs the inverse using the established bijections at X=G and X=B and associativity.

I tested zero complexes/the zero ring, a single sheaf in any integer degree, and complexes with nonzero terms in arbitrarily negative degrees. In every degree the lower-truncation sequence still stabilizes; it need not stabilize simultaneously in all degrees. Countable sums and all Hom sets are taken in the fixed ambient universe. Neither B nor G acquires a boundedness assumption. All seven steps are below 2000 characters; no long step conceals an auxiliary comparison. Every citation quote was checked as an exact substring of the corresponding live statement, and proof_deps is exactly the union of uses. Unsplit new-node, duplication and new-statement edge-case issues do not arise because none are created.

## Unfinished work

No mathematical part of this one-level split is left unfinished. No Lean was written and no compiler, Lake or build tool was run. Required delivery validation is performed with the server dry run, followed by direct delivery.
