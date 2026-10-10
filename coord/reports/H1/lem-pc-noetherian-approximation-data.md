1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-noetherian-approximation-data.json` (statement, split)
- `dag/nodes/sec-picard-framework/lem-pc-finite-flat-proper-support-descent.json` (statement, unsplit; Mathlib no match)
- `dag/nodes/sec-picard-framework/lem-pc-perfect-complex-descent.json` (statement, unsplit; Mathlib no match)

2. Attachments: none.

3. WANTED: none; the cited Stacks source files are represented by the project's citation inventory.

4. The imported item had no proof and its blueprint place still contained stale tags (0C0C and 09RK). I retained the item statement and routed the morphism descent through the existing `thm-pd-spreading-out` node (Tag 01ZM), while replacing the stale tags by the actual flat/proper-support tags 01ZR, 05LY, 081G and 30.26.7, and perfect descent Tag 09RF. The two genuinely non-elementary combined facts are statement-only nodes, rather than hidden inside proof steps. I searched the whole DAG for these tags and concepts; no existing node states either combined fact. The only nearby 01ZR use is the etale finite-data node, whose statement is about finite etale diagrams and does not state module or perfect descent.

5. Nothing remains unfinished in the split. The new nodes are intentionally unsplit leaves of this worker's one-level decomposition.

## Not duplicates

lem-pc-finite-flat-proper-support-descent vs lem-weil-pbc-etale-finite-data-descent: the existing node descends finite etale schemes, morphisms, relations, and coverings; the new node descends bounded finitely presented flat module complexes and proper supports.
lem-pc-perfect-complex-descent vs lem-pc-noetherian-perfect-direct-image: the existing node proves perfectness of a derived direct image over a Noetherian base; the new node descends an already perfect object from a filtered colimit stage.
lem-pc-finite-flat-proper-support-descent vs lem-pc-noetherian-approximation-data: the item is a simultaneous existential conclusion for X, G^\\bullet, and E; the new node states only the G^\\bullet descent clause with its precise support and flatness data.
lem-pc-perfect-complex-descent vs lem-pc-noetherian-approximation-data: the item is a simultaneous existential conclusion for X, G^\\bullet, and E; the new node states only the E descent clause.

## Review by H1

I read the item's source references in the node and the parent proof in `lem-pc-proper-support-perfect-direct-image.json`, then checked the existing `thm-pd-spreading-out` statement before using it. Step 1 uses exactly its finite-presentation descent clause. Step 2 uses the new node whose statement explicitly supplies boundedness, finite presentation, flatness over the Noetherian stage, proper support, and the base-change identification; these are precisely the hypotheses and conclusion needed. Step 3 uses the new perfect-complex node, which explicitly supplies a perfect stage object and its base-change identification. Step 4 uses both new statements only for their preservation-under-later-base-change conclusions and the directedness of the filtered system; the stage enlargement is the elementary filtered-colimit bookkeeping argument.

I checked the hypotheses against the item: R is a filtered colimit of Noetherian rings, X is finitely presented over Spec(R), G is bounded and termwise finitely presented and S-flat with proper supports, and E is perfect. I corrected the stale blueprint tags and recorded the Mathlib searches for the item and each new node; LeanSearch was unavailable, while LeanFinder, Loogle, and source grep found no exact geometric theorem. I also checked the two possible duplicate nodes and documented why their statements differ.

## Second reading by H1

- Item statement: checked against Limits Tags 01ZM, 01ZR, 05LY, 081G and Perfect Tag 09RF, hypothesis by hypothesis; verdict: agrees, including simultaneous stage enlargement.
- Step 1: checked against `thm-pd-spreading-out` and Tag 01ZM; verdict: the finite-presentation morphism clause supplies exactly the claimed model.
- Step 2: checked against the statements of `lem-pc-finite-flat-proper-support-descent` and Tags 01ZR, 05LY, 081G (with Cohomology Lemma 30.26.7); verdict: finite presentation, flatness, and proper support are all explicit and are applied termwise.
- Step 3: checked against `lem-pc-perfect-complex-descent` and Tag 09RF; verdict: the stated perfect stage object and base-change isomorphism are exactly what is used.
- Step 4: checked against both cited node statements and filtered-system directedness; verdict: taking a common later stage and base-changing preserves each listed property and identification.
- `lem-pc-finite-flat-proper-support-descent`: checked as a self-contained statement against Tags 01ZR, 05LY, 081G and 30.26.7; verdict: no missing hypothesis or conclusion.
- `lem-pc-perfect-complex-descent`: checked as a self-contained statement against Tag 09RF; verdict: no missing hypothesis or conclusion.
- Small cases checked: the zero complex and empty support satisfy the clauses vacuously; over a field the filtered system may be constant; for an empty scheme the descended data remain empty; no n-parameter occurs.
- Changes made in this second reading: none; the worker's corrected tags, citations, searches, and blueprint metadata passed review.
