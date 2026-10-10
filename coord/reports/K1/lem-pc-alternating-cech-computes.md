Files written:

- `lem-pc-alternating-cech-computes.json` (statement, split; no Mathlib leaf)
- `citations.json` (verbatim dependency quotes)

Attachments: none.

WANTED: the vendored Stacks source file for Section 20.23 is absent from this checkout; the split follows the cited section as recorded in the imported node.

The item had no Lean declaration and no existing DAG node for the ordered-to-alternating comparison. I retained its statement and supplied the standard three-part proof: restriction is a cochain map, antisymmetric extension gives a retraction, and the repeated-index kernel is contracted by inserting the first repeated index. The only non-elementary construction is written out in the steps rather than moved into a duplicate child node. Mathlib searches found only general alternating-face-map constructions, not this site Cech comparison; LeanSearch was unavailable and recorded as such.

## Review by K1

I read the item node, the parent blueprint proof in `lem-pc-projective-space-cohomology-bound`, and the existing definitions `def-weil-pbc-site-cech-complex` and `def-sc-zariski-site`. Step 1 uses exactly the Cech degree and differential formula from the former and the poset nature of the Zariski site from the latter; both statements are quoted verbatim in `citations.json`. Steps 2 and 3 spell out the permutation-sign extension and the contracting homotopy on repeated tuples, including the cancellation identities, so they do not rely on an unstated theorem or on a new node restating the item. I checked edge cases: for a one-element cover the alternating complex has only degree zero, and for repeated indices the homotopy removes the repetition; the formulas reduce to the identity and zero complexes respectively. I also recorded the required LeanFinder, Loogle, grep, and unavailable LeanSearch searches in the node.

## Second reading by K1

- Item statement: checked against Stacks Tag 01FG, Lemmas 20.23.3, 20.23.4, and 20.23.6; hypotheses and the ordered differential agree, including the one-element and empty-cover edge cases.
- Step 1: checked against `def-weil-pbc-site-cech-complex` and `def-sc-zariski-site`; the restriction map and commuting face restrictions are elementary.
- Step 2: checked against Stacks Lemma 20.23.3 (Tag 01FI); the signed extension is the stated ordered-to-alternating complex isomorphism.
- Step 3: checked against Stacks Lemma 20.23.6 (Tag 01FK); replaced the incorrect repeated-index contraction with the explicit sorting and semialternating homotopies and their cancellation identities.
- New node `lem-pc-alternating-cech-computes`: statement is self-contained, uses definition nodes for scheme, Zariski site, and Cech complex, and has no proof fields beyond the item split; the Mathlib grep, LeanFinder, Loogle, and unavailable LeanSearch searches were checked in `searches.jsonl`.

Changes: corrected the source to Stacks tags and labels 01FG/01FI/01FJ/01FK, and repaired Step 3 to match the actual Stacks homotopy. No nodes were removed or added.
