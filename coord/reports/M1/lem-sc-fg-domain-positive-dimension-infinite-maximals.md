1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-fg-domain-positive-dimension-infinite-maximals.json`: item, split; no new nodes; Mathlib leaves used are existing nodes `lem-weil-pbc-finite-type-over-field-prime-intersection-maximal` and `lem-weil-pbc-proper-ideal-contained-in-maximal`.

2. Attachments: none.

3. WANTED: none.

4. What was checked and changed: the item was not present as a declaration in the Lean source. I searched the DAG and blueprint for the statement and for the finite-maximal-ideal argument; the existing Jacobson node already supplies the needed finite-type-over-a-field fact, so no duplicate node was created. The item now has a complete proof in four steps. Step 1 reads the Jacobson node literally at the zero prime and uses the existing maximal-ideal existence statement for the empty finite-set edge case; the product argument is written explicitly and uses only the domain hypothesis. Steps 2–4 are elementary consequences: the contradiction forces a field, a field has only the zero prime and dimension zero, and positive dimension rules out finiteness. The source was checked against the imported Stacks Algebra references 00G1 and 00FV cited by the node. Small cases checked: a field has dimension zero and one maximal ideal; `k[t]` has positive dimension and the argument predicts it cannot have finitely many maximal ideals.

## Review by M1

I read the item node, the chapter and unit records, and the two cited node statements. The Jacobson node states exactly that every prime is the intersection of maximal ideals containing it, so its specialization to `(0)` gives the zero intersection used in step 1. The maximal-ideal node states existence above every proper ideal and in particular for every nonzero ring, covering the empty finite-set case. Step 1 also checks the domain hypothesis: a zero maximal ideal makes the ring a field, while otherwise each maximal ideal supplies a nonzero factor whose finite product remains nonzero. Steps 2–4 are one-line algebra and the definition of Krull dimension. I verified the statement against the source description (finite-type domain of positive dimension) and tested the field and polynomial-ring edge cases. No statement-only node was needed, no duplicate blueprint fact was introduced, and all citations in `citations.json` are verbatim excerpts from the cited node statements.
