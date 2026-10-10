1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-adjoint-functors.json` — split statement, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-pre-derived-adjoint-functors-general.json` — statement-only node, no Mathlib match.
- `citations.json` — verbatim statement quotes for both proof steps.

2. Attachments: none.

3. WANTED: none.

## Not duplicates

lem-pc-pre-derived-adjoint-functors-general vs lem-pc-derived-adjoint-functors: the new node treats one pair of complexes with derived systems defined only at those objects, whereas the item asserts the everywhere-defined derived functors and the resulting global adjunction.
lem-pc-pre-derived-adjoint-functors-general vs prop-weil-pbc-derived-inverse-image-adjunction: the new node is the general unbounded abelian-category theorem, while the existing node is a scheme-specific bounded-below etale inverse/direct-image adjunction with explicit unit and counit representatives.
lem-pc-pre-derived-adjoint-functors-general vs lem-weil-pbc-termwise-adjunction-homotopy: the new node concerns Hom sets after passage to derived categories and essentially constant ind/pro systems, while the existing node concerns termwise additive functors and Hom sets in homotopy categories before localization.

4. What was checked and changed: the item was copied from the repository before editing. I read its Stacks source context in `derived.tex`, including Lemma 0FND (the general pre-derived adjunction at lines 9516--9567), Lemma 0DVC (the complex-level specialization at lines 9570--9588), and Lemma 09T5 (the item at lines 9596--9605). The Lean source tree was searched by the item tag and by derived-adjunction names; it contains no sorry-free declaration stating this item exactly. A whole-DAG and blueprint search found no node for 0FND, so I created the statement-only prerequisite rather than duplicating an existing node. Step 1 cites the new node for exactly the canonical Hom isomorphism and checks that its hypotheses specialize to the item's pointwise hypotheses. Step 2 cites the same node for its explicit bifunctoriality clause; the remaining identification of a natural Hom bijection with the definition of an adjunction is elementary. The item's statement dependencies remain the two definitions it names. Both the item and new node were searched with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was recorded as unavailable, while Mathlib's `CategoryTheory.Adjunction.derived` was read as requiring stronger absolute-derived hypotheses and therefore was not a match. I tested the split on the identity adjunction (where both systems are constant immediately) and on the zero functors between zero abelian categories; both satisfy the hypotheses and yield the stated Hom bijection. No source or statement error was found.

## Review by F1

I checked the item statement against Stacks Lemma 09T5 and the new node against the preceding general Lemma 0FND. In step 1, the cited node says precisely that defined-at-$K$ and defined-at-$M$ derived systems give the canonical Hom isomorphism, so no proof-only construction is being cited. In step 2, the same node explicitly includes functoriality in both variables on the subcategories where the derived functors are defined; since the item assumes those subcategories are all of the derived categories, the adjunction definition applies. I verified the hypotheses category by category: $F$ and $G$ are functors between the stated abelian categories, $G$ is left adjoint to $F$, and the item assumes the two derived systems are defined everywhere. The new node is statement-only as required for an unsplit non-Mathlib dependency, introduces its complexes and defined-at conditions, and records its source and all searches. The small identity and zero-category cases confirm that the direction of the Hom bijection and the everywhere-defined condition are coherent. No corrections were needed after the DAG and citation checks.

5. What could not be finished: nothing; the required dry run is the remaining mechanical check.

## Second reading by F1

- Item statement: checked against Stacks Derived Categories Lemma 09T5 (derived.tex lines 9596--9605); the hypotheses and adjunction conclusion agree, including the everywhere-defined derived functors.
- New node `lem-pc-pre-derived-adjoint-functors-general`: checked against Lemma 0FND (derived.tex lines 9516--9567); its pointwise defined-at hypotheses, Hom isomorphism, and functoriality clause agree, with complexes, homotopy categories, and quasi-isomorphisms supplied by `def-weil-abstract-derived-category`.
- Step 1: checked against 0FND and 09T5; repaired the text to state explicitly that the cited isomorphism is inverted to match the item's Hom-bijection orientation.
- Step 2: checked against 09T5 and 0DVC; the cited node supplies functoriality on the subcategories, and the everywhere-defined hypotheses make these the full derived categories; recognizing the natural Hom bijection as an adjunction is elementary.
- Small cases: identity adjunctions and zero abelian categories satisfy the defined-at hypotheses and give the stated bijection; no source or statement error was found.
- Search and form checks: searched the DAG for duplicate derived-adjunction or essentially-constant nodes and Mathlib for localization-based derived adjunctions; the existing Mathlib declarations require stronger absolute-derived hypotheses, so the statement-only prerequisite remains necessary. The node is self-contained through the cited derived-category definition, has a Stacks tag/label source, and records all searches.
- Change made: clarified the Hom-isomorphism direction in proof step 1; no node statements or dependencies were otherwise changed.
