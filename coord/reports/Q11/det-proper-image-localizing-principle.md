# Stage-1 worker report: det-proper-image-localizing-principle

## Files written

- `dag/nodes/sec-six-functors-basics/det-proper-image-localizing-principle.json`: existing item, five-step split; Mathlib search found no complete match.
- `citations.json`: seven entries, one verbatim quotation for each step/node citation.
- `report.md`: this report. `finalize.py` is a sandbox-only preparation script; `searches.jsonl` was written by the required search wrapper.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this detail lemma does not state the unit's two geometric assertions.

## Attachments

None. Searched the exact item id and blueprint tag, proper-image/localizing terminology, and the upstream declaration-name inventory. The project has a theorem about finite triangulated envelopes and natural transformations (`WeilConjectures/Mathlib/CategoryTheory/Triangulated/Generators.lean`), not this arbitrary-coproduct localizing-closure principle. Nothing justifies ATTACH.

## WANTED

None. The generic argument is proved directly from the definitions. Its source is the current blueprint's two proof paragraphs, so `proof_origin.by` remains `agent`.

## What was wrong and what changed

The imported proof gave the right route, but its second paragraph had `elementary: null` and no citations. More significantly, its citation to `sk-def-localizing-closure` alone did not justify a theorem for arbitrary triangulated categories: that definition now specializes to pro-etale condensed-module derived categories. I kept the theorem's hypotheses and conclusions and added its intended generic intersection definition inline. Step 1 verifies that this intersection is localizing and minimal, instead of treating the specialized definition node as a general theorem. Existing Mathlib leaves define exact functors and full triangulated subcategories. They now supply the two generic interfaces actually used. The pro-etale closure node is used only for the final specialization, alongside the already existing existence statement for its ambient small sums. This is an explicit expansion of the same notion, not a weakening or a statement dispute.

The five steps realize the original two proof paragraphs: intersection unpacking and the subcategory S argument, followed by restriction exactness and restriction coproducts. The final step checks the example stated in the item. The proof origin now names the actual `.proof.md` file, not a nonexistent `## Proof` in the statement file. `blueprint.from` stays null because the item is imported; `same_as=[]` records the whole-blueprint search. Import flags and maintainer fields are retained.

## Not duplicates

No new nodes or duplicate pairs. Whole-DAG and blueprint searches for localizing closures, localizing subcategories and functors preserving sums found the existing specialized existence and definition nodes, the related natural-transformation determination principle, and the proper/open applications. None states this same generic preservation theorem except the item itself. I reused the definitions and existence statement rather than creating general-category-theory nodes for elementary closure arguments.

## Mathlib searches and source reading

All recorded queries were actually run with `msearch.py`; the exact query strings, output digests and top hits are in `searches.jsonl`. Two natural-language phrasings were used with both LeanFinder and LeanSearch. Loogle initially rejected two identifiers; its successful `CategoryTheory.ObjectProperty.IsTriangulated` query returned triangulated-subcategory infrastructure. The initial two grep calls mistakenly included `Mathlib/` in the subdirectory argument, duplicating the wrapper's prefix: those zero hits are explicitly recorded as invalid evidence. Corrected grep calls used `CategoryTheory/Triangulated` and `CategoryTheory` and were read.

I inspected Mathlib `Triangulated/Subcategory.lean` (including the inverse-image triangulated instance around line 580), `Triangulated/Generators.lean` (finite-operation triangulated envelope and its minimality), and `Triangulated/LocalizingSubcategory.lean` (Verdier left/right localizing subcategories). They supply infrastructure, not the whole coproduct-generated-hull theorem. There is no exact or one-line-specialization Mathlib match. This split writes out the elementary remaining universal-property arguments, so no new Mathlib leaf is needed.

## Review by Q11

I read the current main-20261015 statement and both proof paragraphs, the proper-image unit record and its chapter record, GOAL.md and coord/dag-sync.md, and delivery-errors B--E in full. I also read every cited node's complete statement: the triangulated-category/exact-functor definition, full triangulated-subcategory definition, specialized localizing-closure definition, and existing closure-existence theorem. I consulted `literature/stacks-project/derived.tex` at `definition-exact-functor-triangulated-categories` (Tag 014V), `definition-triangulated-subcategory` (05QM) and `lemma-triangulated-subcategory` (05QX), checking tag mappings locally. No SGA source is used and there are no new-node sources to audit.

Step 1 uses the full-subcategory criterion: zero, integer shifts and triangle closure are preserved pointwise under the intersection, as are repleteness and all small sums. The ambient category is a candidate, so no existence of a small category indexing all candidates is assumed. Minimality follows by containment of object predicates, not a colimit. Step 2 uses exactly the given additive exact F, its shift isomorphism and its action on distinguished triangles, together with that same subcategory criterion. Both K and M already belong to the source closure; this is checked separately before checking their images. Closure under sums uses precisely the hypothesis that F preserves all small sums. No full faithfulness, equivalence, compactness, or retract theorem is used. The generator hypothesis is invoked exactly once to place G in S.

Step 3 uses the inherited shifts and ambient distinguished triangles guaranteed by the full-subcategory statement; the ambient exactness definition then proves exactness of the restriction, including its shift comparison. Step 4 spells out the Hom-set coproduct universal property using fullness, both in the source and target closures. It cites no extra theorem because the argument is the coproduct definition itself. It preserves the actual coproduct cocones, not merely an abstract object isomorphism. Step 5 uses the specialized definition for the precise condensed-module coefficient category and the existing existence theorem's clause (1) for arbitrary ambient sums. This is a foundational tool use, declared in `split_report.tool_uses`, not a replacement of the unit's proper-image route. The citation file quotes the corresponding exact clauses, and each quotation was checked as a literal substring of the cited statement.

I tested empty G and G', the zero category and zero functor, identity functors, and empty coproducts. The proof always includes zero before invoking the triangulated-subcategory criterion, so empty generators do not break it. For empty indexing sets fullness restricts the initial-object universal property just as for nonempty ones. The proof does not require a small generating class or enumerate a proper class. The specialized example also includes the empty scheme, whose derived category is zero; it asserts no nonzero or noncomplete object exists. These checks expose no false assertion. I checked C1 and C4 explicitly: no specialized source statement is being used as a generic theorem, no theorem is inferred from merely naming a functor, and the only substantial structural facts are the exact full-subcategory statements cited. B's new-node requirements are vacuous; D's prohibition on moving clauses into new nodes is respected because all the argument stays in the five steps; E's missing-hypothesis and wrong-coefficient-category cases have been checked as above.

Procedural note: one accidental read-only `git status --short` command was run in the shared repository while checking the JSON work. It made no changes. All file writes were confined to the sandbox; no Lean was written, no compiler/Lake/build ran, and no agents were started.

## What could not be finished

Nothing remains in the mathematical split. Required delivery dry run is recorded below when completed. The second reader must review and deliver; this worker does not push.

## Second reading by Q11

- Item statement: checked against `sk-prop-proper-image-localizing-principle.md` and its proof; all generic hypotheses, the inclusion conclusion, exact restriction, coproduct preservation, and the pro-etale specialization are present, with the inline `Loc` convention making the generic statement explicit; verdict pass.
- Step 1: checked against the first proof paragraph and `def-weil-triangulated-subcategory`; intersection preserves zero, repleteness, shifts, triangles, and ambient sums, and minimality follows from containment in every candidate; empty and zero cases pass; verdict pass.
- Step 2: checked against the first proof paragraph and `def-weil-triangulated-category`/`def-weil-triangulated-subcategory`; the subcategory `S` contains the generators and is closed under zero, isomorphisms, shifts, triangles, and sums using exactness and sum preservation; verdict pass.
- Step 3: checked against the second proof paragraph and the two triangulated definitions; the restricted additive functor, shift isomorphism, and distinguished triangles are inherited from the ambient categories; verdict pass.
- Step 4: checked against the second proof paragraph; fullness identifies the restricted Hom sets with ambient Hom sets, so ambient coproduct cocones are coproducts in both closures, including the empty family; verdict pass.
- Step 5: checked against `sk-def-localizing-closure` and clause (1) of `det-def-localizing-closure-existence`; the specialization uses the stated unbounded module-object derived category and its arbitrary ambient sums, without adding coefficient or completeness hypotheses; verdict pass.
- New nodes: none; therefore B1--B7, duplicate checks, and new-node Mathlib-leaf checks are vacuous. Existing cited nodes were opened and their quoted statements in `citations.json` were checked as verbatim substrings; verdict pass.
- Edge cases checked: empty generator families, zero category and zero functor, identity functors, empty coproducts, and the empty scheme specialization; no statement or proof failure found.
- Changes made: none to the node or citations; appended this second-reading record only. The required dry run was attempted and is being rerun after the delivery worktree lock clears.
