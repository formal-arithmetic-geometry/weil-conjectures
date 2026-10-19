# Q155: lem-coef-pattern-marked-mapping-components

## Files written

- dag/nodes/sec-six-functors/lem-coef-pattern-marked-mapping-components.json: statement, split into five steps; no Mathlib match.
- citations.json: one verbatim statement quotation for every step/node citation.
- searches.jsonl: six actual msearch.py records, preserved as produced.
- report.md: this report.

No new nodes and no Mathlib leaves were created. No unit record was changed: this item is auxiliary infrastructure, not the unit's key statement.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 checkout for the exact blueprint id, marked simplicial sets, markedSimplicial, MarkedSimplicial and categoricalPattern. No project declaration states this item. Upstream master sorry declarations are not used as evidence of completion.

## Wanted literature

WANTED: Jacob Lurie, Higher Algebra (2017), Proposition B.1.14, printed pp.1481-1482, and Lemma B.2.4(a), printed pp.1483-1484, for lem-coef-pattern-marked-mapping-components. The document is not archived in literature/. I read these passages online at https://people.math.harvard.edu/~lurie/papers/HA.pdf without downloading or writing literature. The agent-written expansion is marked proof_origin.by = agent.

## Findings and corrections

The local shared checkout did not contain the assigned item at launch. A read-only SSH read found it at /home/ubuntu/weil-newtargets/dag/nodes/sec-six-functors/lem-coef-pattern-marked-mapping-components.json on the server. I copied that exact record into the empty sandbox and retained its statement, source, blueprint ancestry, creation metadata and inherited Mathlib searches. The server also confirmed the three proof dependencies' statements agree with the local copies used for citations.

There is no statement dispute. No hypothesis, conclusion, definition or coefficient category was changed. This item's statement is the relative marked mapping-space assertion, not a claim that arbitrary full subcomplexes of Kan complexes are unions of components. The important additional input is that this particular inclusion is a Kan fibration. No assertion about weak equivalences, local/global cocartesian comparisons or section cores is needed.

The imported node had no proof. The split now carries the elementary argument itself, using the final paragraph of the existing lem-coef-pattern-anodyne-lifting-products for its only non-elementary input. That result applies to arbitrary marked cofibrations and therefore to the identity of underlying simplicial sets that enlarges the domain marking. It is not a restatement of this item, and the proof does not use the edge-detection parent that created this item.

## Searches and duplicates

I ran blueprint_refs.py search for "marked mapping" and "union of connected components"; each returned zero blueprint nodes. Whole-DAG searches for "full simplicial subset", "union of connected components" and injective/monomorphism Kan-fibration phrases found related infrastructure. The parent's Step 3 contains the argument this item was extracted to support, so citing that parent would be circular. The existing lem-coef-kan-component-restriction-fibration concerns restricting a given Kan fibration to already specified component subsets; it does not identify the present marked subset. No new lemma is necessary: the generic injective-Kan-fibration consequence is written out by horn lifting in Steps 3-4, rather than made another node.

I ran msearch.py for two LeanFinder phrasings, two Loogle queries, one grep and one LeanSearch. The first Loogle query, SSet.KanComplex, Mono, reported unknown identifier Mono; its record explicitly says invalid query, and I repeated with SSet.KanComplex. All six real records are appended to the item without modifying the inherited searches. Read hits include SSet.modelCategoryQuillen.I/J and its fibration predicate, SSet.KanComplex.hornFilling, skeletal/range lemmas, full truncation/nerve functors and ordinary subobject monomorphisms. I read KanComplex.lean:36-52, CategoryWithFibrations.lean:35-103 and PiZero.lean:12-24,39-74 in pinned Mathlib. These provide unmarked horn/component notions, not marked relative mapping spaces. PiZero's TODO still lists component subcomplexes. The grep's four hits are comments about simp markings in unrelated algebra files, not mathematical markings of simplicial sets. No exact or one-line-specialization match was found.

## Review by Q155

I read the complete B-E sections of delivery-errors.md against the item and its dependencies. For B, the statement introduces the small pattern, W, its marking M, the fibered target and both mapping complexes. Its existing statement dependencies define precisely these notions. There are no new unsplit nodes to carry hidden proofs, incomplete hypotheses, duplicate sources or invented Mathlib declarations. The JSON uses single mathematical backslashes as parsed strings, and blueprint.from.place already identifies the exact auxiliary place; same_as was checked and remains empty.

For C, I opened every cited node and read its statement, including the final paragraph rather than merely the proof of lem-coef-pattern-anodyne-lifting-products. Step 1 uses only the definition of marked maps and coordinatewise product marking from lem-coef-marked-point-cartesian-model: restriction forgets a condition on the same underlying map, so is injective in every degree; at degree zero the product marking is M. Step 2 uses exactly the arbitrary-degreewise-injection restriction-fibration clause and mapping-Kan clause of lem-coef-pattern-anodyne-lifting-products. Its hypotheses are satisfied because W^flat -> W is a marked map over the same base and an identity on underlying simplices, and Z is assumed fibered. It requires neither an anodyne hypothesis nor a fibered domain. Steps 3 and 4 use exactly the all-horns, including both dimension-one horns, characterization from lem-coef-kan-quillen-right-proper. Step 5 uses only closure of marking-preserving maps under composition from lem-coef-marked-point-cartesian-model. citations.json gives an actual verbatim part of each statement for each occurrence. proof_deps is precisely the union of these citations. All are in the same unit; no off-unit tool or route exception is claimed.

For D, Step 2 is the sole non-elementary application, and Steps 1,3,4,5 carry the argument instead of relabeling clauses as new nodes. In Step 3 I explicitly lift from either endpoint of a one-simplex, giving invariance along finite zigzags. In Step 4 the induction has a degree-zero base, the degree-one case from Step 3, and the n >= 2 step: faces lift by induction, injectivity makes their overlaps agree, and the horn lift has exactly the prescribed bottom simplex. Thus the full-subset assertion does not hide an external general theorem. This is a routine horn argument from the stated lifting characterization, correctly marked elementary; it is not an uncited cocartesian-invariance lemma. The longest step is 977 characters, so there is no non-elementary step over 2000 characters hiding a subsidiary comparison.

For E, I checked both endpoints in dimension one (not just a left-fibration convention), arbitrary n and degenerate simplices, the fixed base C, and coordinatewise product markings. I tested W empty: both complexes are the one-point complex. With no selected vertices the source mapping complex is empty and every horn lifting problem into it is vacuous. An entirely unselected target component contributes no simplex, and in a selected component all vertices are selected by finite edge zigzags. A simplex has finitely many vertices and restrictions commute with postcomposition degreewise, so no finiteness assumption on W is introduced. Empty Z or an empty K is permitted; no vertices are conjured by the horn proof. The proof uses no choice of cocartesian lift, no equivalence reflection by a target map, and no unrestricted surjectivity. Natural postcomposition need only send selected components to selected components, which follows directly from preserving markings; it need not reflect them.

The source I read for the item is Higher Algebra B.2.4(a) and the supporting B.1.14, as above. Its full-subset description agrees with the unchanged statement; the union-of-components refinement follows from the explicit injective Kan-fibration argument. The supporting theorem is already in this unit's marked-anodyne route. I also read the item's chapter and unit records and the blueprint ancestor's statement/proof: this is auxiliary mapping-complex infrastructure below the finite-coefficient adjunction paragraph. No unit proof route or chapter reference was replaced, and no SGA source is cited by the split. No new node needs a separate source check. No Lean file, live project, launcher or compiler was written or run.

## Unfinished work

None in the split.

## Delivery verification

On resuming the interrupted turn, I found no active delivery for this item and retained the existing split, citations and six logged searches. The required deliver.py --no-push completed with exit 0: OK (not pushed) at 766a759026, preflight passed. I reread all cited statements and verified their verbatim citations against the current shared DAG, and reread Higher Algebra B.1.14 and B.2.4(a) online. The current repository still has the same unsplit item statement; no replacement split or completed Lean attachment supersedes this work. No mathematical change was needed. A final dry run checks this report update before direct delivery, as the dispatched brief requires.
