# Report

1. Files written:
- `dag/nodes/sec-six-functors/lem-coef-infinity-inner-horn-collapse-filtration.json`: statement node, split; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim citation quotes for all four proof steps.

2. Attachments: none.

3. WANTED: an archival local copy of Lurie, *Higher Algebra*, Lemma 2.4.4.6 (the proof was read online at the URL recorded in the node).

4. The imported node had no proof steps. I checked the source proof for the case i>1. Its phrase “nondecreasing” is inconsistent with sigma_1 = Delta^N; the split and statement use the forced nonincreasing ordering and record this source discrepancy. No hypothesis or endpoint was changed.

5. I could not finish the split until checking the coface argument and the terminal collapse; those checks are now written as four explicit steps.

## Review by Q132

I read the item statement, the definition node `def-cbc-enhanced-diagrams-cones`, the unit record `sk-prop-sf-biduality-general`, and the online source at Higher Algebra Lemma 2.4.4.6, printed pages 308–309. The definition node supplies the meanings of standard simplices, horns, simplicial subsets, and degreewise pullbacks; its statement is cited verbatim in `citations.json` for every step.

Step 1 constructs the finite family of vertex sets mapping surjectively to all four ordinal blocks, orders it by decreasing dimension, and deletes each set with its face omitting i. It verifies that the full set is first and that every required face occurs once. Step 2 checks the nontrivial closure hypothesis: every coface of a deleted simplex is deleted, and the remaining faces of each attached simplex are exactly the horn faces, giving K_j intersect sigma_j = Lambda_{p_j}^{n_j} and K_{j-1}=K_j union sigma_j. Step 3 checks the hypotheses on every S_j directly from the four blocks: all four blocks force i-1 and i, the predecessor of i is i-1, and the position and dimension inequalities follow; only the full set has dimension N. Step 4 checks both endpoints degreewise. At the first stage the surviving faces are Lambda_i^N; after all pairs are removed, survival is equivalent to the collapse image omitting at least one of blocks 0, 1, or 3, which is exactly the pullback of Lambda_2^3. Omitting only block 2 does not suffice.

I verified that each cited node says the fact taken from it, that all proof dependencies equal the union of uses, and that no clause was moved into a new node. The proof is the finite combinatorial argument itself, so no additional lemma node is warranted. Small edge checks include N=3,i=2 (the family has only the full four-block face and its i-omitting partner) and the fact that a face omitting i cannot be surjective because it misses block 2. The only source correction is the ordering typo documented above.


Continuation audit (2026-10-17): I retained the four proof steps, source, statement and inherited searches, compared them with the current unsplit repository node, and reused all five searches recorded in searches.jsonl, appending their actual records to mathlib_searches. I read Horn.lean:32–70 and RelativeCellComplex.lean:337–350: the former gives the horn definition, and the latter presupposes a proper pairing/rank function, so neither proves the ordered four-block filtration in one line. Searches of WeilConjectures for the blueprint tag, inner horns, horn filtrations and collapses found no project attachment. The whole-blueprint search for horn and DAG searches for four-block/collapse/surjective-simplex found no duplicate of the item. No new node is needed: each finite-set calculation is fully written in the item's steps. All four steps are below 2,000 characters and contain no omitted standard lemma.

I independently checked the complete deletion construction by enumerating all nonempty vertex subsets for every 3 ≤ N ≤ 8 and 1 < i < N (21 parameter pairs). Closure, the horn intersection, restoration union, position/dimension bounds and both endpoints all passed. Since every simplex has its image vertex set and precomposition only shrinks that image, the proof explains why these subset calculations give all degrees. I rechecked every verbatim quotation against the current definition node; step 4 additionally quotes its degreewise pullback sentence. The endpoint wording above corrects the older report's ambiguous “omitting a block”; the node's proof already distinguished blocks 0, 1, 3 correctly. The inherited unit/chapter and ancestor route are unchanged.

## Source error

Higher Algebra Lemma 2.4.4.6, printed p. 308, says the dimensions are nondecreasing while also putting the full simplex first. For N=4, i=2 the surjective faces have dimensions 4 and 3, so this combination is impossible. The source's earlier i=1 filtration uses decreasing dimensions. The item already uses the consistent nonincreasing ordering; no mathematical statement was changed by this delivery. I reread the official online PDF, pp. 308–309; an archival local copy remains WANTED as recorded above.
