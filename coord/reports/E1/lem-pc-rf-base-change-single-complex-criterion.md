1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-rf-base-change-single-complex-criterion.json` (statement, split; no Mathlib match).
- `lem-pc-rf-single-complex-inherited-tensor-condition` (statement-only supporting node; no Mathlib match).
- `lem-pc-rf-single-complex-qcqs-induction` (statement-only supporting node, faithful to Tag 0DJ9; no Mathlib match).
- `citations.json`.

2. Attachments: none. WANTED: none.

3. The returned version incorrectly routed the item through an affine-condition child and stated the qcqs child as an induction over affine opens. I read `/home/ubuntu/c1-stacks-review/perfect.tex` at Tags 0DJ8, 0DJ9 and 0DJA. The qcqs child now states Tag 0DJ9 itself: for an arbitrary cartesian square, qcqs `f`, a map `L(g')^*K -> K'`, and the stalkwise 0DJ8 condition, the composite `Lg^*Rf_*K -> Rf'_*L(g')^*K -> Rf'_*K'` is an isomorphism. The affine child was deleted. The item applies 0DJA(1) to `L(g')^*G^bullet -> (g')^*G^bullet` and arbitrary `E`, then applies the qcqs child with `K = E tensor^L G^bullet` and `K' = L(g')^*E tensor^L (g')^*G^bullet`; the final identification is elementary.

## Review by E1

I checked the item against `/home/ubuntu/c1-stacks-review/perfect.tex`, Tag 0DJA(1), and Tag 0DJ9. The item hypotheses retain qcqs `f`, arbitrary base change `g`, arbitrary `E`, bounded-above quasi-coherent `G^bullet`, and the pointwise 0DJ8 stalk condition. The inherited-tensor node says exactly that the 0DJ8 stalkwise condition for `L(g')^*K -> K'` is inherited by `L(g')^*(E tensor^L K) -> L(g')^*E tensor^L K'`; this is the sole input to Step 1. The qcqs node was rewritten to say exactly the Tag 0DJ9 conclusion for arbitrary `S` and `S'`, with no affine or intersection hypothesis in its statement and no proof prose. Step 2 cites that statement with the required substitutions `K = E tensor^L G^bullet` and `K' = L(g')^*E tensor^L (g')^*G^bullet`, so its conclusion is the target composite. Step 3 only identifies this composite with the canonical map by definitions and functoriality, which is elementary. I removed the former affine-condition citation and all unsupported claims about affine charts, non-affine intersections, localization, and Mayer–Vietoris from the item. The citation quotes were replaced with verbatim portions of the repaired node statement. The item and qcqs node searches were rerun through `msearch.py`; LeanSearch was unavailable and is recorded as unavailable in the node search log.

## Not duplicates

lem-pc-rf-single-complex-qcqs-induction vs lem-pc-rf-base-change-single-complex-criterion: the supporting node is the general Tag 0DJ9 statement for arbitrary `K` and `K'`, while the item specializes it using the inherited condition for `E` and `G^bullet` and states the resulting target map.

lem-pc-rf-single-complex-inherited-tensor-condition vs lem-pc-rf-base-change-single-complex-criterion: the supporting node only preserves the stalkwise 0DJ8 condition under tensoring, while the item concludes derived direct-image base change.

## Second reading by E1

- Item statement: checked against `perfect.tex` Tags 0DJ8, 0DJ9, and 0DJA; hypotheses and target agree, including arbitrary `g`, qcqs `f`, and the stalk cohomology map.
- Step 1: checked against Tag 0DJA(1) and the inherited-condition node; the cited statement supplies exactly the tensor-preserved stalk maps.
- Step 2: checked against Tag 0DJ9; the substitutions `K = E tensor^L G^bullet` and `K' = L(g')^*E tensor^L (g')^*G^bullet` match its conclusion.
- Step 3: checked from the definitions of derived pullback, tensor product, and comparison maps; the identification is elementary.
- `lem-pc-rf-single-complex-inherited-tensor-condition`: checked against Tag 0DJA(1), with explicit self-contained stalk cohomology maps and definition dependencies; no existing duplicate found by node search.
- `lem-pc-rf-single-complex-qcqs-induction`: checked against Tag 0DJ9, with explicit self-contained stalk cohomology maps and qcqs hypotheses; no existing duplicate found by node search.
- Changed both supporting statements to spell out the Tag 0DJ8 map rather than referring to the tag as a definition; repaired the citation quotes accordingly. Tested zero/field and empty-scheme cases at the level of the stated maps: they reduce to identity or zero complexes without contradiction.
