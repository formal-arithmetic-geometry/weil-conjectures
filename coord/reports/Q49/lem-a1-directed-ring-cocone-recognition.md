# Stage-1 report: lem-a1-directed-ring-cocone-recognition

1. Files written: dag/nodes/sec-purity-real-sheaves/lem-a1-directed-ring-cocone-recognition.json (statement, now split; no exact Mathlib match for the whole statement), citations.json, and this report. There are no new nodes or new Mathlib leaves. searches.jsonl records the required searches as actually run.
2. Attachments: none. Searched lean/WeilConjectures by the exact blueprint id, recognition/colimit words, and directed/cocone words. The directed tensor-cocone and two-colimit files concern different statements; there is no exact project declaration to attach.
3. WANTED: none.
4. The imported statement is correct and remains unchanged. The source's eventual-equality description is not by itself a proof that the supplied ring and additive cocones are colimits; the explicit common-stage calculations now supply that proof. The naturality clause now has an actual equation on every coprojection. No statement dispute or unit-route error was found.
5. Nothing mathematical remains unfinished for this one-level split. No Lean was written, compiled, or built. Only this sandbox was written.

## Sources and searches

Read the chapter sec-purity-real-sheaves and unit sk-p-real-rankin, the three-level route rule in SETUP.md, GOAL.md, the worker/stage-1 documents, and delivery-errors.md B through E. The item's inherited blueprint ancestry identifies it as the algebraic recognition tool in the fpqc descent input to lem-a1-affine-hc0. Read the parent lem-a1-sections-intersection-structure-colimit, including its use of both the recognition and naturality clauses.

For the actual argument read literature/stacks-project/categories.tex, Tag 04AX (section-directed-colimits, especially the equivalence relation immediately preceding lemma-directed-commutes) and Tag 002F (definition-colimit). Read literature/stacks-project/more-groupoids.tex, equation-sections-of-intersection and its preceding/following paragraphs, to check the use for structure-sheaf sections. The proof_origin is agent: the elementary algebraic and naturality checks are written out here, rather than attributed to a named source theorem.

Ran blueprint_refs.py ancestor and searches for directed ring, colimit cocone, and eventual equality, and DAG searches for 04AX, recognition, same-stage and eventual equality. Read the existing lem-pc-filtered-colimit-commrings-elementwise and lem-weil-pbc-filtered-colimit-algebras-elementwise statements. They assume an already-colimiting cocone and establish its elementwise properties; this item proves the reverse implication and functoriality, so these are not replacements for the item. No helper node is created.

Required msearch calls cover LeanFinder (two phrasings), LeanSearch, Loogle (ring-colimit and set-recognition patterns), and grep (ring filtered colimits and Types colimits). Read the returned hits and Mathlib/CategoryTheory/Limits/Types/Filtered.lean:60-105 and Mathlib/Algebra/Category/Ring/FilteredColimits.lean:340-385. Types.FilteredColimit.isColimitOf' covers the sets clause. The ring construction theorems concern a particular constructed cocone. The whole item is not a one-line specialization of these declarations: additive/ring preservation and the comparison-map equation still need the explicit arguments given here. It would be wrong to create a new node for the already available set-recognition clause or for these few-line algebraic checks. Earlier searches inherited from the live node are retained, with the new actual searches appended and their results recorded.

## Review by Q49

I checked the split against B-E with the node, the colimit definition and the source text open. No new statement-only nodes are needed, so the source and duplicate obligations for new nodes are vacuous. The statement introduces every ring, diagram and map; the only specialized notion, categorical colimit, cites def-weil-pbc-category-colimit. The maps are unital ring maps. The index poset is explicitly small and nonempty, and directedness supplies each common upper bound used below.

Step 1 uses only the item's compatibility and same-stage equality hypotheses. Moving both representatives to k is legitimate because their images under q_k are their original equal images; the assumption then applies to two elements of A_k. The transition law turns the resulting equality at l into equality of the original transported representatives. No injectivity or hidden finite-presentation claim is used.

Step 2 constructs the unique function directly. Step 1 and cocone compatibility prove independence of every choice of stage and representative. Existence of representatives is exactly the first hypothesis, and uniqueness follows by evaluating at one representative of each r. This supplies the set universal property without citing the proof of an existing node or making an unstated quotient-identification claim.

Step 3 uses the same function, now with additive t_i. Both operands are transported to a common stage, where t_k preserves addition. The identities for zero and negatives are explicitly displayed. Nonemptiness is used for choosing an index for zero. This proves that the constructed function has the required additive structure; it does not assume that a forgetful functor preserves colimits.

Step 4 likewise checks products and the unit at a stage, then invokes def-weil-pbc-category-colimit. I opened that node: its statement says that a compatible cocone is a colimit precisely when every compatible cocone admits exactly one factoring morphism, and it states uniqueness up to unique isomorphism. These are exactly the facts used here and in Step 5; they are copied verbatim into citations.json. The additive portion is Step 3, so no additional ring-colimit theorem is being used implicitly.

Step 5 takes chosen colimits as in the cited definition, forms maps in both directions by its universal property, and checks their composites on all coprojections. This proves the canonical identifications are isomorphisms, rather than merely naming a transport. For the naturality square, evaluation on c_i' gives u q_i' = q_i u_i by the stated hypothesis, while the induced colimit map satisfies v c_i' = c_i u_i by definition. Uniqueness then gives u alpha' = alpha v, in each of sets, abelian groups and rings. The cited definition explicitly includes the induced canonical map, so the citation supports everything taken from it.

All five steps are elementary calculations from hypotheses, preceding steps and the colimit definition, not invocations of an unrecorded theorem. Each is under 2000 characters; the longest is under 800. No whole proof is moved to a new node and no clause is relabelled as a helper. proof_deps is exactly the union of uses. The existing blueprint.from.place already names the exact extraction and remains unchanged; same_as is the empty result of the blueprint search.

I tested a singleton index (the hypotheses make q bijective and the factor map is its forced inverse followed by the target map), all zero rings, and a noninjective transition Z to Z/2 at a terminal stage. In the last case equality in R is witnessed at that terminal stage, exactly as used by Step 1. For R the zero ring and a putative cocone to a nonzero ring, equality of the images of 0 and 1 forces them to agree at some stage and hence in the target; thus the proof does not incorrectly manufacture a unital map from the zero ring to a nonzero ring. Constant identity systems and arbitrary noninjective maps satisfy the displayed calculations. Removing nonemptiness would invalidate the unit argument, but that hypothesis is present and retained. No extra hypotheses, source errors, or weakened conclusions were introduced.

## Not duplicates

No new nodes.
