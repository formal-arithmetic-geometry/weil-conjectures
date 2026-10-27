# Stage 1: lem-sfb-space-diagonal-locally-finite-type

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-diagonal-locally-finite-type.json`: item, split using existing nodes; not a Mathlib leaf.
- `citations.json`: verbatim statement excerpts for all four step citations.
- `report.md`: this report. The required search command maintains `searches.jsonl`.

No new nodes, no Mathlib leaves, no Lean files or compilation.

## Attachments

None. Searched `lean/WeilConjectures/` by the blueprint id, diagonal/local-finite-type expressions, and algebraic-space terminology. No exact project declaration was found. The diagonal discussion in `ExistsIsSeparatedOverPullbackMap.lean` concerns schemes.

## WANTED

None. All mathematical sources used are available in the read clone.

## Corrections and reuse

The item statement is unchanged and agrees with Stacks spaces-morphisms.tex, Tag 03HK, label lemma-properties-diagonal, clauses (1) and (2). The original node had no proof. Whole-DAG searches by tag, title and statement found `lem-sfb-space-diagonal-scheme-tests`, an existing stronger statement for an arbitrary base scheme and with an additional monomorphism conclusion. I reused it instead of creating an equivalent supporting node. The item's own statement is the Spec Z specialization with a chartwise convention, so the proof explicitly performs the remaining convention comparison.

The existing blueprint ancestry has `from.node: null`; this was not invented or changed here. I retained its detailed `from.place` and `via` chain, and read the latest blueprint chapter, unit and direct-images proof (3). The generic diagonal input supports the inherited separatedness-descent route, without changing a unit or chapter. Blueprint searches for `03HK` and `scheme tests` found zero imported blueprint nodes; the wider diagonal search did not find an exact imported statement. `same_as` remains empty.

## Mathlib searches

Ran the prescribed Q18 msearch command with LeanFinder (two phrasings), Loogle, grep and LeanSearch. All succeeded. The exact queries and returned declaration summaries are in the item's `mathlib_searches`, and the command's original digest records are in `searches.jsonl`. LeanFinder/LeanSearch returned scheme diagonals, local-finite-type definitions and separated/formally-unramified scheme results. Read Mathlib `AlgebraicGeometry/Morphisms/FiniteType.lean:37-44`, `Separated.lean:39-46` and `FormallyUnramified.lean:126`: their ambient objects are schemes, so they do not state this algebraic-space item. The regular-expression search found only the formally-unramified scheme instance. Loogle gave no hits. This confirms the inherited non-leaf decision with searches actually run for this delivery; no new node needs a search.

## Not duplicates

No new nodes. Existing `lem-sfb-space-diagonal-scheme-tests` is deliberately cited as a generalization, rather than restated as a new node. It was created independently for `lem-sfb-space-separated-diagonal-closed` and has no proof dependencies, so this citation does not point back to the item.

## Review by Q18

I read Stacks spaces-morphisms.tex Tag 03HK, including the factorization through the absolute diagonal and the etale presentation argument, and spaces.tex Tag 025V (definition-relative-representable-property), which tests a representable map on every scheme. The imported statement is valid without finiteness or separation assumptions, so no statement dispute or hypothesis correction is needed. There are no new-node sources to review.

Step 1 uses the statement, not the proof, of `lem-sfb-space-diagonal-scheme-tests`: it expressly supplies a scheme D_T for every scheme T mapping to the relative product, together with a locally finite type projection. Its base B is arbitrary, so B = Spec Z meets every hypothesis, and its relative product U ×_V U is exactly the target in this item. The statement of `def-trf-algebraic-space` expressly defines representability by these scheme pullbacks. This proves the representability clause without inferring it from chart-local representability. The extra monomorphism conclusion is unused.

Step 2 uses `def-trf-algebraic-space` for a representable surjective etale scheme atlas of W; W is an algebraic space by the fibre-product clause already present in the item's statement dependencies. I read the entire statement of `lem-sfb-space-local-properties-chart-test`, which explicitly includes locally finite type, permits any target atlas and a scheme atlas of the pullback, and assumes no quasi-compactness or separation. Here that pullback is the scheme D_T furnished in step 1, so its identity is the permitted source atlas. The criterion now gives exactly the chartwise local finite type used by the item. This avoids silently identifying two conventions. Tag 03MJ is the source of that existing chart criterion. Every non-elementary input in both steps is a cited existing node; there is no hidden claim requiring a new node. Both steps are shorter than 2000 characters.

For edge cases, U empty gives empty scheme pullbacks and the identity source atlas of the empty scheme. If W is empty, its empty scheme atlas is allowed by the chart criterion, which explicitly includes empty charts. For a representable scheme morphism the test reduces to ordinary scheme local finite type. I checked that no argument uses quasi-compactness, finite presentation, separatedness or a nonempty atlas. Verbatim quotes for every step/node pair are checked against the exact node statements and recorded in citations.json. The inherited statement definitions were retained; there are no unsupported notions, new statement-only proofs, fabricated Mathlib searches, route replacements, or SGA sources.

## Unfinished work

None for this one-level split. The cited scheme-test lemma remains its own existing DAG item; no claim is made that it has already been formalized or proved in Lean.
