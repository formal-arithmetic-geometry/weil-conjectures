# Worker report: `lem-weil-pbc-injective-resolution-ses`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-injective-resolution-ses.json`: split the imported horseshoe statement into four proof steps; no new nodes.

Mathlib verdict for the item: no complete horseshoe theorem was found. The existing Mathlib `ShortComplex` splitting lemmas cover the termwise split argument only.

## Attachments

None.

## WANTED

None. The cited Stacks source is represented by the existing literature reference.

## Review by C

I checked the statement against Stacks Project Tag 013T and retained its hypotheses and the stronger degreewise split conclusion. The proof now explicitly constructs the degree-zero pushout, repeats the construction on cokernels, records compatibility of the lifted maps with differentials, and verifies exactness of all three augmented complexes. The proof dependencies are exactly the existing abelian-category and injective-resolution definitions. The node already contained LeanSearch, LeanFinder, Loogle, and Mathlib-source grep searches; these collectively found no complete Mathlib horseshoe result. `tools/check_dag.py` and `tools/review_split.py lem-weil-pbc-injective-resolution-ses` were run after the edit.

## What was wrong

The imported node had an empty proof despite being an ordinary Stacks lemma. No statement correction was needed.

## Could not finish

No unfinished work remains for this item.
