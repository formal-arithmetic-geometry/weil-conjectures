# Worker report: lem-sfb-bounded-bifunctor-devissage

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-bifunctor-devissage.json: statement, now split; no exact Mathlib match found.
- citations.json: verbatim statement excerpts for every dependency cited by each of the five steps.
- report.md and searches.jsonl: this report and the searches actually performed. write_split.py is sandbox scratch work.

No new nodes; no new Mathlib leaves. The statement is unchanged. Added direct statement dependencies for the derived-category and exact/triangulated-category notions already used in it. Kept all inherited node fields and search records; corrected the inherited verdict's irrelevant “ringed-site/scalar-model” wording.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, the item id, bifunctor/bounded combinations, and bounded induction/devissage terminology. Read the closest general result, DerivedCategory.exists_not_isZero_homology_obj_singleFunctor in WeilConjectures/Algebra/Homology/DerivedCategory/HomologyDevissage.lean:44. It concerns nonvanishing cohomology of an exact functor into another derived category; it does not state membership in an arbitrary triangulated subcategory for a bifunctor. The bounded flat-tensor results require flatness and do not state this item. No exact attachment was found.

## Literature wanted

None.

## Findings and changes

The imported statement is correct, but its empty proof did not supply either induction or handle the fact that the classes need not contain zero. I wrote the inductions inside the item, without creating a one-variable restatement as a new node.

I read the chapter sec-six-functors-basics and unit sk-lem-integral-models, the current ancestor det-lem-integral-models-operations, and its blueprint proof at literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-integral-models/sk-lem-integral-models-operations.proof.md. The current ancestor's reviewed DAG step 5 requests precisely the bounded passage from its sheaf calculation. This split supplies the formal finite-cohomology passage; it does not reintroduce completeness hypotheses from the older blueprint prose or alter the unit.

The source actually used for the triangles is literature/stacks-project/derived.tex, Tag 08J5, remark-truncation-distinguished-triangle, especially its second displayed triangle. Read also Tag 014V, definition-exact-functor-triangulated-categories, Tag 05QM, definition-triangulated-subcategory, the following lemma-triangulated-subcategory (05QX), and the localization definition 05RU. Verified their tag/label correspondence in stacks-project/tags/tags. The source gives the triangles; the two explicit finite inductions are my argument, so proof_origin.by is agent.

Searches used the prescribed msearch.py command exclusively for Mathlib discovery, with two semantic phrasings, LeanSearch, Loogle, and two grep patterns. Read the Loogle hit Mathlib/CategoryTheory/Triangulated/TStructure/TruncLTGE.lean:652-654: it asserts that the bounded subcategory itself is triangulated, not the required two-variable generation principle. The other hits concern exact functors, the standard t-structure or homological functors. They do not give an exact match or a one-line specialization for this item. The inherited searches remain recorded and the new log queries have been appended exactly.

## Not duplicates

No new node was created. Whole-DAG keyword/tag searches and blueprint_refs searches for truncation, bounded objects, bifunctor, and finite cohomological induction found the existing general truncation nodes. Reused lem-weil-pbc-truncation-triangle and lem-weil-pbc-truncation-descends instead of creating copies. The blueprint search found no alternate statement of the entire bifunctor item, so same_as is empty.

## Review by NF

I checked the split against delivery-errors B through E with the source and each cited node's statement open. There are no new statement-only obligations or new definitions, and all TeX is stored once through JSON escaping. Every proof step is below 2000 characters. The two inductions remain in this item's proof; no clause is moved into a renamed child.

Step 1 uses def-weil-triangulated-category's statement that an exact functor is additive and commutes with shifts. This makes its zero-object calculation a direct identity calculation, rather than an unproved preservation theorem. def-weil-triangulated-subcategory explicitly gives zero, arbitrary integer shifts, and extension closure; the item's strict-fullness assumption supplies invariance under isomorphism. I checked that only extension closure, and not closure under retracts or arbitrary sums, is needed.

Step 2 uses the exact cohomology formula in the statement of lem-weil-pbc-truncation-descends. At the lower endpoint all cohomology is zero; at the upper endpoint the inclusion induces identities in retained degrees and maps zero to zero elsewhere. def-weil-abstract-derived-category defines quasi-isomorphisms by those cohomology maps and the derived category as their localization. Thus the endpoint identifications follow directly from the cited statements, with no additional non-elementary detection theorem.

Step 3 uses the displayed distinguished triangle in lem-weil-pbc-truncation-triangle, read in full. Its hypothesis is an arbitrary abelian category with derived category; it applies to both input categories here, without injectives, Grothendieck hypotheses, bounded-below assumptions, or smallness of an index category. The statement also gives the triangle on derived objects. We need only existence, not the additional uniqueness/functoriality clauses of that node. def-weil-triangulated-category gives the image triangle under each partial exact functor. The shift in degree q is [-q], as in 08J5 with a=q-1.

Step 4 uses that same triangle, partial exactness, and the extension/shift clauses of def-weil-triangulated-subcategory. I checked the induction indices: j=0 is cutoff c-1; the successor with q=c+j has cutoffs q-1 and q; j=d-c+1 ends at d. For nonzero H^q(M), the stated hypothesis applies to the actual object H^q(M), with no isomorphism-closure requirement on the class. For zero H^q(M), step 1 applies instead, so zero need not be in the class.

Step 5 repeats the argument in the first variable after step 4 has proved the required assertion for every F in A_0 and this fixed M. Again j=0 is cutoff a-1 and the last cutoff is b. I checked that no compatibility between the two shift structures of B is used: each image triangle or shift comparison involves only one variable. This proves precisely the statement, without requiring a uniform support interval for all objects.

Edge cases checked: zero or acyclic inputs; either class empty; cohomology concentrated in one arbitrary positive or negative degree; gaps inside the chosen intervals; the zero target subcategory; and classes that omit zero. In a one-degree pair the result reduces to the hypothesis followed by the total shift [-p-q]. Empty classes permit only acyclic complexes in the corresponding variable, which step 1 handles. All these cases agree with the proof.

The two general truncation nodes are declared as tool uses in split_report, since they supply category-theoretic infrastructure rather than replacing the integral-model unit's tensor calculation. citations.json copies actual parts of their statements and of the definition statements, checked as literal substrings. I corrected the initial source-tag annotation for exact functors to 014V and the derived-category label to definition-unbounded-derived-category before delivery. No mathematical statement dispute was found. No Lean file was written, and no compiler or build tool was run.

## Unfinished work

None within this one-level stage-1 split. The reused nodes retain their own independent proof obligations.
