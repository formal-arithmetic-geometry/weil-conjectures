## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-uncountable-almost-disjoint-family.json`: item, statement unchanged, complete five-step split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-cantor-no-powerset-injection.json`: statement, exact Mathlib leaf `Function.cantor_injective`, `Mathlib/Logic/Function/Basic.lean:376–378`.
- `citations.json`: verbatim statement excerpts for every citation of every item step.

Attachments: none. Searches in `lean/WeilConjectures/` for the blueprint tag, almost-disjoint terminology, and Cantor declaration names found no project declaration stating the item or the new node.

WANTED: a human-written set-theory reference for the binary-prefix construction of an uncountable almost-disjoint family of infinite subsets of the natural numbers, for `lem-sfb-uncountable-almost-disjoint-family`. This request is inherited from the item's source record. The blueprint paragraph gives its coefficient context, not this combinatorial theorem; the proof is explicitly agent-written. Cantor's theorem itself has the exact local Mathlib source above. No Stacks tag is asserted for either statement; no SGA source is used.

The item was an unsplit auxiliary with no proof. Its inherited `blueprint.from.node` is null: `tools/blueprint_refs.py ancestor lem-sfb-uncountable-almost-disjoint-family` returned None. I retained that ancestry and its full via chain, filled the place for the new leaf by the coefficient auxiliary in paragraph (3), and recorded the construction's relationship to that paragraph. I read both `dag/chapters/sec-six-functors-basics.json` and `dag/units/sk-thm-sf-ctf-stability.json`, as well as the current source paragraph. The unit record is in sec-six-functors whereas this imported auxiliary is filed in sec-six-functors-basics; neither record nor the inherited fields were altered. The construction is below the unit route, so no unit proof is replaced.

Nothing mathematical remains unfinished in the split. The only new node is already a Mathlib leaf. The wanted human reference remains an explicitly recorded provenance limitation, not an unproved step.

## New nodes

`lem-sfb-cantor-no-powerset-injection` is the general Cantor no-injection theorem for an arbitrary type X. It is an exact Mathlib leaf, not a restatement of the item's existence theorem or a new binary-sequence uncountability clause. Its statement is self-contained: the power set means all subsets, and no additional notion is introduced. It has no proof steps or proof dependencies. Mathlib source lines 374–378 were opened and read; its implicit type parameter is arbitrary and it needs no hypotheses. Loogle, LeanFinder, LeanSearch and grep searches in its record are copied from searches actually run by msearch.py and recorded in searches.jsonl. All were available. The earlier item searches are preserved; the new item searches try both almost-disjoint-family and binary-branch formulations. They give ingredients but no exact theorem for the whole item.

## Not duplicates

Whole-DAG searches were made for almost-disjoint, uncountable, binary words/sequences, countable words/lists, Cantor declaration names, and power-set no-injection terminology, inspecting statements rather than mistaking search records for statements. Blueprint searches for cantor, power set, powerset, no injective, and almost disjoint returned no existing theorem of this form. The three DAG files hit by the Cantor-name/terminology search were opened:

- `lem-sfb-cantor-no-powerset-injection` vs `lem-coef-sset-cellular-comparison`: the latter is a comparison theorem for colimit-preserving simplicial-set functors, not a theorem about power-set injections.
- `lem-sfb-cantor-no-powerset-injection` vs `lem-trf-derived-basis-increasing-union`: the latter glues derived objects along an ordinal-indexed open cover; it has no power-set assertion.
- `lem-sfb-cantor-no-powerset-injection` vs `lem-coef-small-family-accessibility-rank`: the latter supplies a common uncountable accessibility rank, not Cantor's theorem.

There are no shared Stacks tags. The new id was checked absent before writing it. The elementary prefix coding and finite-intersection arguments were kept as steps, not inflated into new nodes.

## Review by NF

I read paragraph (3) in the current `main-20261015` file named by the item. It treats proper and open direct images and their compactification, so it supplies only the location of the coefficient auxiliary, not a source proof of this combinatorial assertion. I did not attribute the prefix argument to that paragraph: `proof_origin.by` is agent. For the new leaf I read `Function.cantor_injective` at lines 376–378 of Mathlib/Logic/Function/Basic.lean and checked that its arbitrary type and arbitrary function agree exactly with the new statement, without an added cardinality, nonemptiness or finiteness assumption. For the two definition citations I opened the DAG nodes and read their statements: countability is existence of an injection into N; infinite means not finite.

Step 1 cites the new Cantor node with X=N. Its statement literally denies every injective map from P(N) to N, and the cited countability definition identifies precisely the prohibited map. No cardinal-arithmetic or continuum hypothesis is being used. Taking I=P(N) avoids a hidden equivalence between binary sequences and subsets.

Step 2 has no external result hidden in it. The positive code is defined recursively with the empty-word marker 1. Its injectivity is an induction on the sum of word lengths, with an explicit empty/nonempty case (all nonempty codes are at least 2) and parity/cancellation step. Thus no theorem about countability of finite words or uniqueness of binary expansions is silently cited. This short induction is elementary and remains in the item.

Step 3 forms the first n membership digits of each subset S and defines its set of natural-number codes. Equality of codes gives equality of words by the previous step; comparing lengths then gives n=m, and comparing entries gives agreement on every coordinate less than n. These are the elementary consequences of the explicit construction, not uses of an unstated prefix lemma.

Step 4 uses only those unequal lengths and the cited meaning of infinite. If A_S had r elements, the first r+1 prefix lengths would already give too many distinct elements. This is finite counting, and it establishes infinitude for every S including the empty subset and the full subset of N. It does not infer infinitude merely from having an unbounded list with repetitions.

Step 5 uses extensionality to obtain any coordinate k on which distinct subsets disagree; k need not be the least one. An element of the intersection must be represented by equal-length words. Length greater than k would force agreement at k, so the intersection lies in the displayed list of k+1 codes. The finite-set definition cited by this step gives exactly the conclusion claimed. Both the n=m identification and the strict inequality k<n are written out, so the common-prefix bound is not hidden behind “standard”.

I checked small cases: the empty prefix has code 1 for every S; the one-letter words 0 and 1 have codes 2 and 3; the two-letter words 00, 01, 10, 11 have distinct codes 4, 6, 5, 7. If subsets first differ at coordinate 0 the intersection is exactly {1}; if they first differ at coordinate k, all and only the lengths 0 through k can occur in the intersection. Equal subsets are intentionally excluded from the finite-intersection clause; their own prefix ranges are infinite. Empty and singleton base types also satisfy the general Cantor node (for an empty type no power-set-to-base function exists; for a singleton its two subsets cannot inject into it).

Against delivery-errors B–E: the single new node is statement-only, complete and literally matched by its source; its live-DAG and blueprint duplicate searches are documented above. Every cited node's statement was opened and its actual required clause is quoted in citations.json. The only non-elementary theorem used is Cantor's theorem, explicitly cited in step 1. The construction, parity induction and finite counting are short elementary steps; no step exceeds 2000 characters. The family is constructed in the item itself rather than delegated to a new restatement. The statements need no hypothesis repairs, and no false source assertion was copied. I retained the existing statement, provenance, prior searches and ancestry; I replaced the missing proof with the explicit argument and added the exact Mathlib leaf. The graph points only to that leaf and to the existing definition leaves, so no new cycle or off-unit proof tool is introduced.

Dry-run repair: the first preflight required an explicit statement-dependency citation on the generic Cantor leaf. I opened the existing size-convention statement and made its fixed universes explicit in the leaf, adding `def-weil-size-convention` to `stmt_deps`. This scopes the type X in the project universes and changes none of the theorem’s mathematical assumptions; the Mathlib theorem is polymorphic in precisely that universe. I updated the verbatim citation as well. No new definition was introduced.
