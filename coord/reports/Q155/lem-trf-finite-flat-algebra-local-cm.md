# Stage-1 delivery: lem-trf-finite-flat-algebra-local-cm

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-flat-algebra-local-cm.json: statement, split; unchanged statement, five proof steps. No exact Mathlib match.
- citations.json: 14 entries, one verbatim full-statement quote for each step/node citation.
- report.md: this report. searches.jsonl records the searches run by msearch.py; write_split.py is sandbox preparation only.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by Cohen–Macaulay, depth/flatness and finite-flat terminology. The regular-local miracle-flatness declaration has the opposite direction, and the depth formula and Cohen–Macaulay resolution results do not give this item's finite-flat ascent. No declaration found states every clause of this item.

## Wanted literature

None. All sources used are present in literature/stacks-project/algebra.tex.

## Corrections and findings

The item was unsplit and the sandbox had no item, report, or earlier search log. The statement is correct and unchanged. In particular, the finiteness of B as an A-module must not be silently transferred to B_q as an A_p-module. The proof obtains dim B_q <= dim A_p directly: chains of primes below q contract strictly by integrality and incomparability. This supplies the dimension hypothesis of the second alternative of Stacks 00R5, after which its actual regular-sequence argument proves the result. No claim of finite generation of B_q over A_p is used.

DAG searches for 00R5/045M and the algebraic ingredients, plus whole-blueprint searches for 00R5, Cohen Macaulay, finite flat and the exact item id, found no duplicate of the full item. The returned blueprint finite-flat nodes concern group schemes, descent, curves or finite duality. Existing generic algebra nodes already cover all ingredients; making nodes for a local ascent clause, or for the chain comparison, would add unnecessary nodes.

The latest blueprint ancestor lem-trf-local-term-locality proof (1)--(2), chapter sec-trace-formula and unit sk-i-curve-zero were read. This item's existing descendant role is the tensor-field Cohen–Macaulay input for relative associated specialization in the flat-family branch. The proof stays below that node-level algebra input and changes neither the chapter nor unit route. The only off-unit non-Mathlib proof ingredient is lem-weil-pbc-depth-le-support-dimension, declared in split_report.tool_uses as a generic tool.

## Unfinished work

None for this one-level split. The existing dependencies remain the project's independently tracked items.

## Not duplicates

No new nodes, so no new/existing node pairs require comparison.

## Review by Q155

I read the actual statement and proof of Stacks 00R5 (lemma-finite-flat-over-regular-CM) and the use of that result in 045M (lemma-tensor-fields-CM). The proof of 00R5 chooses a dimension-length regular sequence in the Cohen–Macaulay base, transfers it along the flat local map by 00LM, and uses the dimension upper bound and depth bound. My proof follows these operations. I also read 00GK (finite is integral), 00GT (integral incomparability), 00E3 (prime correspondence for localization), 00HR (local flat implies faithfully flat), 00KQ (Noetherian local dimension), 00LI/00LF (depth and regular sequences), and 00LK (depth bounded by support dimension), checking their labels against tags/tags. There are no new nodes needing a separate source review.

For step 1 I read lem-weil-pbc-finite-algebra-noetherian: its hypotheses are exactly Noetherian A and module-finite B, and it gives Noetherian B. I read lem-weil-pbc-flat-local-ring-maps: its statement supplies both locality and flatness of A_p -> B_q and Noetherianity of both local rings from precisely the rings already known to be Noetherian. No assertion about a finite localized algebra is needed.

For step 2 I read lem-weil-pbc-finite-algebra-is-integral and lem-weil-pbc-integral-incomparability: the former gives integrality for our module-finite map, and the latter makes every strict inclusion of primes remain strict after contraction. I read lem-weil-pbc-localization-dimension-chains-below-prime, which explicitly identifies the two local dimensions with suprema of lengths of chains below their primes. Contraction takes every chain below q to a chain of the same length below p, proving the upper bound without a separate hidden theorem. This is a finite chain argument in the item, not a new node that restates a clause.

For step 3 I read lem-weil-pbc-noetherian-local-finite-krull-dimension, def-weil-pbc-depth and def-weil-pbc-regular-sequence. The first makes d a natural number. Depth is exactly the supremum of regular-sequence lengths in the maximal ideal, and the statement's hypothesis makes that supremum d. A bounded set of natural numbers attains its finite supremum; the proof explicitly gives the d-1 argument and treats d=0 by the empty sequence. The exceptional infinite-depth branch does not occur since the maximal ideal is proper in the nonzero local ring. This is the only step marked elementary, because the only additional inference is the finite-supremum observation.

For step 4 I read lem-weil-pbc-flat-local-hom-faithfully-flat and lem-sfb-regular-sequence-faithfully-flat-ascent: the map from step 1 has exactly the local/flat hypotheses of the first, and the resulting faithful flatness meets the second. The ascent statement includes that the final quotient is nonzero, so the images form a regular sequence in the convention actually used by depth. Locality puts its entries in the maximal ideal. def-weil-pbc-depth then gives d <= depth S.

For step 5 I read lem-weil-pbc-depth-le-support-dimension, whose statement applies to a nonzero finite module over a Noetherian local ring. S as its own module is generated by 1, nonzero and Noetherian local by step 1. Its support is its whole spectrum; the proof writes out the fraction test showing this, using the meaning of localization and the chain definition of Krull dimension, rather than citing a definition for a theorem. The resulting depth S <= dim S closes the chain of inequalities and proves all equalities. The Noetherian conclusion was already established in step 1.

Small cases checked: B=0 has no primes and is Noetherian; A=0 forces B=0 for a unital map; d=0 gives the empty regular sequence and forces dim S=depth S=0. Over a field every finite algebra, including k[e]/(e^2), has local dimension and depth zero. The finite flat algebra A x A illustrates the case where the map is not local globally; choosing q and forming the local map is essential. A map A -> A x A/I with A=k[t] and I=(t) is finite but not flat; the proof correctly fails at step 1/4 rather than proving the false ascent without flatness.

I checked delivery-errors B through E point by point: no new-node schemas, fabricated searches, duplicate nodes, relabelled clauses, sources-only proof steps, or circular deductions were introduced. Every non-elementary input is a cited existing statement and citations.json contains verbatim quotes of the statements actually read. Proof dependencies are precisely the union of step uses, all statements introduce their objects, the blueprint ancestry is preserved, and no step exceeds 2000 characters. The new recorded msearch hits were read: they supply partial results about flatness, faithful flatness, localization, dimensions and regular elements, not this complete Cohen–Macaulay ascent. No Mathlib match was claimed for the item.
