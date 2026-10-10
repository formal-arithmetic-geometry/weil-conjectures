1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-ample-positive-degree.json` (split item)
- `dag/nodes/sec-abelian-varieties/lem-sc-ample-connected-positive.json` (statement-only, no Mathlib match)
- `dag/nodes/sec-abelian-varieties/lem-sc-degree-additive-clopen.json` (statement-only, no Mathlib match)
- `citations.json`

2. Attachments: none.

3. WANTED: none.

4. I read the item's blueprint node and `Modules/Ample.lean` lines 501-591. The direct theorem `degree_pos_of_isAmple` is not attachable because its connected input is sorried transitively. I searched the whole DAG for Tag 0B5X, component additivity, and restriction of ampleness. The connected input is recorded as a new statement-only node, sourced to Stacks Tag 0B5X and audited against the exact project declaration. The additivity node records the exact project theorem at lines 374-397; it is not in pinned Mathlib. Step 1 cites that node for the sum formula. Step 2 checks restriction of ampleness directly from the definition. Step 3 cites the existing finite-discrete zero-dimensional node and the new connected-positive node; the local invertible-module calculation is written out as the elementary component contribution. Step 4 uses the Hilbert-degree definition and polynomial node for the dimension-one coefficient and the nontriviality conclusion. I tested the edge cases in the source: a zero-dimensional component contributes coefficient zero, while dimension one forces at least one positive component; the item itself records the dimension-zero counterexample.

## Review by E1

I checked every cited statement verbatim and copied the relevant sentences into `citations.json`. The new connected node states exactly the connected clause and carries the sorried declaration audit; the additivity node states the finite clopen sum and has the source theorem and all three required searches. The item keeps its original hypotheses and statement, fills the blueprint reference, and has no circular dependency. The only nontrivial external input is the connected Stacks 0B5X result; all other steps either cite the two smaller statements or unpack the definitions in a few lines.

## Not duplicates

lem-sc-ample-connected-positive vs lem-sc-ample-positive-degree: the new node assumes connectedness and states only the one-dimensional connected component coefficient, while the item allows disconnected curves and concludes positivity of the total degree.
lem-sc-ample-connected-positive vs lem-pc-ample-positive-degree: the existing node is an if-and-only-if theorem for smooth projective integral curves over an arbitrary field; the new node is only the forward positive-degree clause for connected proper curves over an algebraically closed field and uses Hilbert degree.

5. Nothing remains unfinished.

## Second reading by E1

- Item statement: checked against the blueprint proposition and the dimension-one specialization of the existing Tag 0BEV node; hypotheses and the zero-dimensional counterexample agree.
- Step 1: checked against `lem-sc-positive-ample-hilbert-degree`, `def-sc-hilbert-degree`, and `lem-sc-hilbert-polynomial`; each cited statement supplies the positivity or coefficient identification used.
- `lem-sc-ample-connected-positive`: checked against Tag 0B5X and the existing Tag 0BEV node; removed because it is a special case of the existing stronger theorem and was unnecessary.
- `lem-sc-degree-additive-clopen`: checked against the project declaration and component argument; removed because the existing stronger theorem makes clopen additivity unused.
- Existing tool node: searched the whole DAG and verified `lem-sc-positive-ample-hilbert-degree` states positivity for every nonempty proper scheme, so it applies with $X=C$ and $g=1$.
- Audited an alternative proof through Tag 0BEV, then restored the prescribed two-node proof route after the route checker rejected that departure; citations and dependencies were kept consistent.
- The stronger Tag 0BEV node was considered but rejected by `review_split.py` because it departs from this unit's prescribed route; the original two-node route was restored, with the zero-dimensional generic fact recorded as a tool use.
