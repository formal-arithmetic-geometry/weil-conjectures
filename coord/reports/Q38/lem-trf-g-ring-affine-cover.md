# Worker report: lem-trf-g-ring-affine-cover

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-g-ring-affine-cover.json`: unchanged statement; six proof steps; status `split`.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- No new nodes and no new Mathlib leaves.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, the exact blueprint docstring tag, `G-ring`, `G_ring`, `GScheme`, and `g-ring` found no project declaration stating the item. The read-only upstream master also has no exact declaration. No Lean code was written or compiled.

## WANTED

None.

## Source and corrections

I read Stacks `properties.tex`, Tag 0HA5 (`lemma-locally-G-scheme`, (3) implies (2)), and Tag 0HA4 (`lemma-characterize-G-scheme`), together with Tag 01OW (`lemma-locally-Noetherian`) and `more-algebra.tex`, Tag 07GH (`definition-G-ring`). The item is correct without a local Noetherianity or quasi-compactness hypothesis: the G-ring cover itself gives local Noetherianity. The proof expands the source's stalk argument, using the fact that localizations of two affine neighbourhoods at the same point identify with its stalk. It does not assert that intersections of affine opens are affine.

The first draft introduced two criterion nodes for directions of the local G-scheme criterion. On checking the full DAG again, I found the existing transport statements `lem-weil-pbc-adic-completion-ring-equiv` and `lem-weil-pbc-regular-ring-map-ring-equiv`. I removed both proposed nodes and expanded the actual localization/completion argument in the item's steps. The final delivery supersedes the earlier pushed draft and contains only the item node. The statement, its definition dependencies, and the historical blueprint ancestry are retained. There is no source error or statement dispute.

The whole-DAG searches included `G-ring`, `G-scheme`, `0HA4`, `0HA5`, `lemma-characterize-G-scheme`, localizations, affine-open stalks, and ring/completion equivalences. Whole-blueprint searches using `tools/blueprint_refs.py` found no equivalent blueprint statement to the item. The ancestor is `lem-trf-local-term-locality`; the inherited component-locality place is preserved. Searches for proposed intermediate nodes were made with `msearch.py` and read, but those nodes are absent from the final delivery. Existing item searches from its creation are preserved, including their second phrasing. No search was fabricated.

## Review by Q38

I checked the unchanged item statement against 0HA5 with arbitrary index set and arbitrary affine open, and opened the statement of every node used in the final six steps.

1. `def-weil-pbc-g-ring` explicitly includes Noetherianity; `pqf-def-locnoeth` defines local Noetherianity by the existence of precisely this sort of affine Noetherian cover. This step is a direct use of definitions.
2. `pqf-lem-affine-open-locnoeth` states that every affine open of a locally Noetherian scheme has a Noetherian coordinate ring. Its Mathlib status is supported by the affine-cover theorem and `IsLocallyNoetherian.component_noetherian`. Hence the arbitrary ring B is Noetherian before its G-ring criterion is used.
3. `lem-weil-pbc-affine-open-spec-points` supplies the canonical open immersion and prime/point correspondence. Clause (c) of `lem-weil-pbc-affine-open-stalk-localization` explicitly gives each localization-to-stalk ring isomorphism. Applying it to V and to a covering chart containing x provides an equivalence from the chart's localization R to B's localization S. Neither chart is assumed to lie in the other.
4. A ring equivalence preserves units in both directions, so it identifies the unique maximal ideals of the local rings R and S. `lem-weil-pbc-adic-completion-ring-equiv` then gives an equivalence E of the completions together with exactly the commuting-square equality needed in step 5. The completion ideals are the respective maximal ideals, not ideals in the original global section rings.
5. The G-ring definition applied to A_i at the corresponding prime gives regularity of R to its completion. `lem-weil-pbc-regular-ring-map-ring-equiv` has exactly four commutative rings, two equivalences and the required commuting-square hypothesis; its conclusion gives regularity of S to its completion. Both algebraic transport lemmas are declared generic tool uses, since the unit has no replacement for their statements.
6. Noetherianity of B and the completion condition for every prime are exactly the G-ring definition. This is elementary assembly.

The citations file quotes the actual current statements, including the full clause (c) localization formula and the full commuting-square conclusions; nothing is taken from a cited node's proof. All steps are under 600 characters and hide no comparison lemma. All nodes cited are existing unmerged nodes, and proof_deps is exactly the union of uses. The only non-definition, non-Mathlib citations are the two declared transport tools. No SGA source is used; no coefficient-category change is involved.

I checked the empty scheme, empty cover, empty affine open, a single affine chart, and a disconnected or non-quasi-compact scheme. For the empty affine open, B is the zero ring, Noetherianity comes from the same affine-open theorem and there are no primes to test. For nonempty V, every prime point lies in a covering chart by the given cover, with no finiteness assumption. Thus no case is dropped.

## What I could not finish

Nothing. Final server checks and the required dry run are run before pushing the corrected delivery.
