1. Files written

- `dag/nodes/sec-picard-framework/lem-pc-degree-zero-properties.json`: item split; no new nodes and no Mathlib leaves.

2. Attachments

None. No sorry-free project declaration states this item exactly.

3. WANTED

None.

4. Problems found

The imported proof had one paragraph with `elementary: null` and omitted the actual argument. I replaced it with three explicit steps. The parenthetical references to `def-pc-finite-locally-free` and `lem-pc-flf-properties` are retained in the imported statement, although the cohomology argument itself does not use finite locally free morphisms.

5. Incomplete work

Nothing remains for this split.

## Review by J1

I read the item source metadata and the imported proof paragraph, and searched the project source for the blueprint tag and the mathematical notions. The source paragraph gives exactly the two cases used here: a representative in degree zero and a representative shifted to degree `i`. Step 1 spells out the derived-category meaning of an isomorphism and the induced invariance of cohomology; step 2 computes the single-term complex in degree zero; step 3 computes the shifted single-term complex. Each step is marked elementary because it is a direct unfolding of the derived-category, complex-shift, and cohomology definitions, and no step cites a node, so `citations.json` is empty. I checked the edge cases `i = 0`, `i < 0`, and the zero module: the conclusions reduce respectively to the degree-zero case, the same shift convention at a negative index, and vanishing with the zero isomorphism. The Mathlib searches found only general single-complex homology APIs and no exact target declaration; LeanSearch was unavailable and is recorded as such.

## Second reading by J1

- Source statement: checked against the imported blueprint node `lem-pc-degree-zero-properties` (order 820); both the degree-zero and shifted-complex clauses, including all hypotheses, agree. The locally-free module notion is now explicitly tied to `def-amb-finite-locally-free-module`.
- Step 1: checked against `def-pc-derived-category` and the definition of derived-category isomorphism; the zig-zag of quasi-isomorphisms and induced cohomology isomorphisms are exactly the facts used, and the step is elementary.
- Step 2: checked by direct calculation of the complex concentrated in degree zero; the zero object in every other degree gives the stated vanishing and identification, and the step is elementary.
- Step 3: checked by the cohomological shift convention (the complex `E[-i]` has `E` in degree `i`); the same calculation gives vanishing outside `i`, and the step is elementary.
- New nodes: none; duplicate and Mathlib searches were checked in the repository and recorded searches, so there are no new-node B1--B7 obligations or citations to quote.
- Edge cases checked: the zero scheme and zero module, a scheme over a field, `i = 0`, and negative `i`; all reduce to the displayed single-term complex calculation.

Changes made: added the missing module-definition citation to the statement; retained the three explicit elementary proof steps and the empty citation list.
