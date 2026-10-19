1. files written
- item: lem-weil-pbc-faithfully-flat-maximal-ideal-nonzero (Mathlib leaf; no new nodes)

2. attachments

3. WANTED:

4. what was wrong in the node, the blueprint, or the brief

5. what you could not finish, and why

## Review by ND
I checked the item against Stacks Project Algebra, Lemma Tag 00HP (lemma-ff), implication (1) => (4), which states that a faithfully flat module has nonzero fibres at every maximal ideal. The existing definition node def-weil-pbc-faithfully-flat-ring-map identifies a faithfully flat ring map with the target ring viewed as a faithfully flat module, so the ring-map statement is the direct specialization M=S; the quotient S/mS is the maximal fibre. I searched the DAG for the tag and for faithful-flat maximal-ideal and quotient formulations and found no duplicate statement of this implication. The Mathlib declaration Module.FaithfullyFlat.submodule_ne_top (Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean) gives m • (⊤ : Submodule R S) ≠ ⊤ for every maximal m; under the standard ideal/submodule identification this is exactly mS ≠ S, hence S/mS is nonzero. The item is therefore recorded as a Mathlib leaf rather than split into a node that would merely restate its conclusion. Small cases R=S and a field base confirm the quotient is respectively the residue field and S itself, both nonzero. No hypotheses were added or removed.

## Second reading by ND

- Item statement: checked against Stacks Algebra Tag 00HP (lemma-ff), lines 9123–9138, including the flat-module hypothesis, all maximal ideals, and the equality of the tensor fibre with $S/\mathfrak mS$; verdict: agrees hypothesis by hypothesis.
- Mathlib leaf: checked `Module.FaithfullyFlat.submodule_ne_top` at Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean lines 63–64 and the existing ring-map definition node; verdict: the properness criterion specializes to the stated nonzero quotient, with no additional node needed.
- Edge cases: checked $R=S$, a field base, and the zero ring/module boundary; the maximal-fibre conclusion has the expected nonzero residue-field behavior under faithful flatness.
- Blueprint and DAG search: checked the ancestor `lem-weil-pbc-etale-contraction` proof place and searched for duplicate faithful-flat fibre statements; verdict: no duplicate node and the blueprint route is correct.
- Searches: checked every entry in `searches.jsonl`, including the unavailable LeanSearch result; verdict: recorded results match the node metadata.

Changed the node's `created.item` to the delivered item (it incorrectly named an unrelated item), and recorded the missing unavailable LeanSearch query in `mathlib_searches`. No mathematical statement or proof route was changed.
