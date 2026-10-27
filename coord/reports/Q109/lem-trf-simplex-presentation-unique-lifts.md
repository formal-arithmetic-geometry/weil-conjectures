# Worker report: lem-trf-simplex-presentation-unique-lifts

## Files written

- dag/nodes/sec-trace-formula/lem-trf-simplex-presentation-unique-lifts.json: statement, split into four steps; not itself a Mathlib leaf.
- citations.json: verbatim statement excerpts for every step/node citation.
- report.md: this report. Searches are retained in searches.jsonl.

New nodes: 0. New Mathlib leaves: 0. Existing generation leaf reused.

## Attachments

None for this item. The project declaration simplexPresentation_faithful in lean/WeilConjectures/CategoryTheory/SimplexPresentationFaithful.lean:247 states only injectivity, as recorded in lem-sc-module-cup-godement-simplex-presentation-faithful; it does not state all the present item's clauses. Searches for the item tag, SimplexCategoryGenRel, presentation, and unique lifts in WeilConjectures found no declaration asserting the full item. No compiler or build was run.

## Wanted literature

None. Read literature/stacks-project/simplicial.tex, Tag 0168 (lemma-face-degeneracy-category), Tag 016B (lemma-characterize-simplicial-object), and the preceding displayed generator relations. Tags verified in tags/tags. Tag 0168's proof is omitted; the proof supplied here is therefore marked agent-written rather than attributed to a nonexistent Stacks proof.

## Errors and changes

The original item had no proof. Its statement is unchanged, including the degree ranges, typed relations, and strict inverse claims. Retained all original metadata, source references, inherited blueprint ancestry, and previous search records. Added the four actual logged searches run on 2026-10-23. The two semantic phrasings and typed search find only definitions, block factorization, or equivalences with NonemptyFinLinOrd, not this unique-lift statement. NormalForms.lean explicitly calls equivalence a future goal. The supporting general generation result was already a Mathlib leaf, so no duplicate node is justified.

## Unfinished work

None in this one-level split. No new node awaits a split.

## Not duplicates

No new nodes. Reused lem-sc-simplex-morphism-property-generators rather than making a generation, factorization, or fullness node. Reused lem-sc-module-cup-godement-simplex-presentation-faithful for uniqueness. Searches of the whole DAG and blueprint_refs.py searches for simplex, generators, and unique lift found no imported node stating the whole present item. The blueprint ancestor command confirms lem-trf-local-term-locality; its inherited auxiliary reconstruction branch is retained. Read the ancestor statement and proof in literature/blueprint/latest and the chapter/unit records. This foundational argument does not replace either geometric unit step.

## Review by Q109

I read delivery-errors.md B through E, including its merged copy, against the node and source. There are no new statements, definitions, or Mathlib leaves to audit for B1--B9. The existing statement introduces both categories and the canonical functor completely. Its coface and codegeneracy conventions agree with the Stacks relations; both adjacent mixed identities are present.

For step 1 I opened the statement of lem-sc-module-cup-godement-simplex-presentation-faithful: it defines the same P and J with these object labels and generator images. The witnesses for identity, composition, and each generator are written explicitly; functoriality gives their images. This is a few-line elementary verification, not a new lemma. The verbatim citation records this definition portion, not merely its faithfulness conclusion.

For step 2 I opened lem-sc-simplex-morphism-property-generators and Mathlib/AlgebraicTopology/SimplexCategory/MorphismProperty.lean:74--87. Its statement applies to any property containing identities and closed under composition that contains all cofaces and codegeneracies. Step 1 verifies exactly these hypotheses for existence of a lift, with fixed endpoints; the result gives existence for every arrow. It makes no assumption of uniqueness or of a pre-existing inverse functor. This is a substantive cited generation theorem, not a definition used as a theorem.

For step 3 I read the faithfulness node's last sentence: equal J-images of parallel P-arrows imply equality. Both candidate lifts have the same fixed endpoints and image alpha, so that sentence proves exactly the required uniqueness. I also read the corresponding project declaration and its docstring, but use the node's statement, not implementation details of its proof. Because its recorded unit differs, split_report.tool_uses declares this generic tool with the reason; no maintainer-owned top-level tool_uses was written.

Step 4 uses only the established existence and uniqueness from steps 2 and 3 and the functor laws of the given J. The identity and composite candidates have their displayed images; the generator candidates have the stipulated images. These prove the lift laws and hence the K functor laws. For KJ, f itself is a lift of J(f), which forces KJ(f)=f. Both object maps fix the natural-number labels, so this proves strict functor equality, not just isomorphism. The direct uniqueness arguments are elementary and require no additional theorem node.

I tested degree zero: the identity lift of [0] is its empty word; the two maps [0] to [1] lift to the two cofaces, and [1] to [0] lifts to sigma_0. The mixed identities reduce both sigma_0 after these cofaces to the identity. Constants in higher degrees are covered by the same generation property, and identities and empty generator composites satisfy step 1 without any positive-degree assumption. No empty ordinal [-1] is introduced. All source and target compositions in steps 1 and 4 are typed. Neither cited theorem depends on this item, so there is no circular lifting argument. There are no hidden normal-form claims, uncited non-elementary facts, or steps exceeding 2000 characters; the assembly proof totals 1550 characters. Citation excerpts were checked as literal substrings of the live statements, and proof_deps is exactly the union of uses.
