# Q152: lem-weil-pbc-etale-lisse-filtration-devissage

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-lisse-filtration-devissage.json — statement, split into four steps; no exact Mathlib match for the whole item.
- citations.json — seven verbatim statement quotations, one for every step/node citation.
- report.md and searches.jsonl — report and actual search-command log.

No new nodes; no new Mathlib leaves. No unit file is changed: this item is not the unit's key statement.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures source for the exact id, weak-Serre terminology, and finite-filtration terminology. HomologyProperty.lean provides the weak-Serre derived-subcategory result, already represented by lem-sbc-cohomology-in-weak-serre-subcategory; it does not state the entire finite-filtration transfer through an arbitrary triangulated functor. The finite composition filtration mentioned in DeligneLaumon/AffineLine/Upper.lean is not this abstract assertion.

## WANTED

None. All mathematical sources used here are present in literature/stacks-project/.

## Findings and changes

The imported statement is valid as written. Its proof was empty. I retained its statement, statement dependencies, source, blueprint ancestry, inherited searches and creator information. I supplied the induction, its zero base case and the exact sequence/triangle for each quotient. The two genuine homological inputs already have nodes, so making new nodes for them would duplicate existing work.

Read the chapter and sk-thm-properbasechange unit record, the ancestor's current blueprint_update, and the current blueprint's direct-image-finiteness statement. This is a generic tool below the classical constructibility input: it supplies the finite-filtration reduction in Tag 0GKY, not an alternative route for proper base change. The generic weak-Serre cohomology lemma is from another unit; its precise black-box use is declared in split_report.tool_uses. The short-exact-sequence triangle node is already a Mathlib leaf. No SGA source is used.

Searches of the whole DAG for 06UQ, 0152, weak Serre, filtration and derived triangles found the existing nodes reused here. Blueprint searches for Serre, weak Serre, filtration, finite-filtration and cohomology found no blueprint node stating this exact transfer. In particular lem-sp-finite-filtration-induction proves an isomorphism criterion for a morphism between two filtered objects; it does not transfer a weak-Serre cohomology condition through a triangulated functor. The specialized constructible/locally constant sheaf Serre nodes do not assert this abstract result for arbitrary abelian categories.

I ran the required Mathlib search command for the item with LeanSearch, Loogle, LeanFinder twice with distinct formulations, and grep both globally and in Algebra/Homology/DerivedCategory. The results were read: t-structure support results, triangulated-functor/subcategory APIs, an unrelated homological-kernel closure result, and unrelated ring/probability filtrations do not state the complete item or a one-line specialization of it. The generic APIs are used through existing DAG nodes. All six new records correspond exactly to searches.jsonl. Earlier search records inherited from Q60 are retained with their original provenance/results; they are not claimed as Q152 searches.

## Not duplicates

No new nodes are proposed. The item is not a duplicate of lem-sp-finite-filtration-induction: that statement compares two filtered objects and concludes an isomorphism from graded isomorphisms; this item concerns one filtration, a triangulated functor and a weak-Serre cohomology property. The existing generic Tag 06UQ and Tag 0152 nodes are cited rather than recreated.

## Review by Q152

I read more-etale.tex Tag 0GKY, label lemma-loc-constant-shriek-rel-dim-1, including the final finite-filtration reduction, and derived.tex Tag 06UQ, label lemma-cohomology-in-serre-subcategory, with its proof and bounded variants. I also read Tag 0152, label lemma-derived-canonical-delta-functor, and the full-triangulated-subcategory definition/criterion (Tag 05QM, label definition-triangulated-subcategory and label lemma-triangulated-subcategory). Homology Tag 0754, label lemma-characterize-weak-serre-subcategory, confirms that precisely the closure assumptions in this item characterize the needed weak Serre class. No source error or STATEMENT-DISPUTED correction is needed, and there are no new statements to check against additional sources.

Step 1 uses the statement of lem-sbc-cohomology-in-weak-serre-subcategory, not a fact buried in its proof. I checked that it explicitly allows arbitrary abelian ambient categories and states the D+ intersection clause. Substituting ambient B and subcategory S matches each hypothesis: strict fullness, zero, kernels and cokernels of maps between S objects, and extensions. No stronger Serre hypothesis (all arbitrary subobjects or quotients) is assumed. Its conclusion supplies W as a strictly full triangulated subcategory. I opened def-weil-triangulated-subcategory and checked that its statement explicitly supplies zero and middle-vertex closure with the first and third vertices in the subcategory.

Step 2 states P(i) before using induction. The zero case uses only additivity of the given functor: its image of the zero object's identity is both an identity and a zero map. An object with identity zero is a zero object since every map to or from it is zero. Computing cohomology on the zero complex is exactly the cohomology construction in the cited def-weil-abstract-derived-category. Strict fullness of S allows the resulting isomorphic zero cohomology objects. This argument is elementary and introduces no extra lemma or assumption about preservation of arbitrary limits by Phi.

Step 3 uses lem-sf-derived-ses-triangle at exactly its stated generality: any short exact sequence in an abelian category, objects placed in degree zero. I checked its Mathlib source SingleTriangle.lean, in particular singleTriangle_distinguished at line 77. The sequence is short exact because F_(i-1) is a subobject of F_i and Q_i is its quotient. All three single complexes are bounded below. The cited def-weil-pbc-bounded-derived-subcategories explicitly provides the inherited triangulated structure, so the triangle lies in the domain D+(A) of Phi. The cited def-weil-triangulated-category explicitly defines an exact functor by preservation of distinguished triangles with the shift identification. Thus the image triangle and the last arrow's target are justified without assuming Phi comes from an exact functor of hearts or from a right derived functor.

Step 4 performs the induction: the induction hypothesis supplies the first image vertex, the item's hypothesis supplies the third, and middle-vertex closure established in step 1 supplies the second. The definition node cited here states precisely that closure. There is no new extension theorem hidden in this step. Setting i=r proves all degrees simultaneously, so no uniform lower bound across different Phi(F_i[0]) is needed.

I tested r=0 (F=0, conclusion is the base case), r=1, repeated consecutive subobjects/zero quotients, the zero functor, S={0}, and S=B. The argument uses no strictness of inclusions and no finite-length assumption on F. I also checked the nontrivial weak-Serre distinction: the proof never asserts an arbitrary subobject of an S object lies in S; all closure is taken from the actual Tag 06UQ statement with its exact hypotheses. The initial unsplit state required no correction of a previous attempted proof; I corrected the missing proof by writing the finite induction explicitly rather than delegating the whole item to a new clause-restating node.

Against delivery-errors B–E: all objects remain introduced in the unchanged statement, source tags and labels are checked in their tex files, each non-elementary step uses an actual stated theorem, every cited statement was opened and copied verbatim to citations.json, and no dependency was inferred from another node's proof. The union of step uses is proof_deps. No new nodes means no elementary-node, duplicate-node or clause-restatement problem. All four step texts are below 2000 characters; their lengths are 635, 458, 652 and 603 characters. No Lean was written and no compiler, Lake or build was run. Only the sandbox was written.

## Unfinished work

None of the mathematical split remains unfinished. Delivery validation and push are performed with the mandated delivery tool; its final result is reported in the one-line dispatch answer.
