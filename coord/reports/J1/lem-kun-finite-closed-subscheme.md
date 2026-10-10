Files written:

- `dag/nodes/sec-smooth-purity/lem-kun-finite-closed-subscheme.json`: statement, split proof, no new node; Mathlib searches found no full match.

Attachments:

- `lem-weil-pbc-finite-type-over-noetherian` is used as the finite-type-over-a-field Noetherianity result.
- `lem-sc-noetherian-closed-points-finite` is used for the closed-subset conclusion.

WANTED: none.

The original imported proof had one paragraph with no citations and an unrelated `def-kun-support` dependency. I removed that dependency from the statement dependencies and made the proof explicit in two steps. The first step uses Stacks Morphisms Lemma 01T6 through the existing DAG statement, after checking that `Spec K` is Noetherian for a field. The second step applies Stacks Properties Lemma 0BA8 through the existing general theorem; its hypotheses are exactly that `X` is Noetherian, `E` is closed, and every point of `E` is closed. No new node was created because both required facts already exist in the DAG, and the second is strictly more general than this item.

## Not duplicates

`lem-kun-finite-closed-subscheme` vs `lem-sc-noetherian-closed-points-finite`: the existing node assumes a Noetherian scheme, while this item assumes finite type over a field and derives Noetherianity in step 1.

## Review by J1

I read the item's blueprint proof and Stacks Properties Lemma 0BA8, plus the source and statements of both cited DAG nodes. Step 1 takes exactly the existing finite-type-over-Noetherian conclusion and verifies its base hypothesis using that a field has Noetherian spectrum. Step 2 takes exactly the existing theorem's conclusion for a closed subset with all points closed; no proof detail from that node was used beyond its statement. I checked the hypotheses against the item, including that the subset is closed and that “all of whose points are closed” means closed in `X`. The empty subset and a singleton closed point satisfy the conclusion; an integral curve is correctly excluded because its generic point is not closed. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as such. No declaration in the slopmaster2 source states this item exactly.

## Second reading by J1

- Item statement: checked against the blueprint node and Properties Lemma 0BA8 (tag 0BA8), hypothesis by hypothesis; finite type over a field, closedness, and closedness of every point are all present, and the conclusion is finiteness.
- Step 1: checked against Morphisms Lemma 01T6 (tag 01T6) and the statement of `lem-weil-pbc-finite-type-over-noetherian`; the field base is Noetherian and the structure morphism is finite type, so the cited conclusion applies.
- Step 2: checked against the statement of `lem-sc-noetherian-closed-points-finite`, which exactly supplies finiteness for a closed subset of a Noetherian scheme whose points are closed; no proof internals were used.
- New nodes: none; both dependencies are existing nodes, so B1-B7 and duplicate-node checks are vacuous.
- Edge cases: the empty closed subset and a singleton closed point are finite; a positive-dimensional integral scheme is excluded because its generic point is not closed.
- Changes: none to the worker's node or citations; the proof, dependencies, source tags, and recorded searches were already correct.
