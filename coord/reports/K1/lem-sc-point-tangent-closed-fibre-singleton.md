# Delivery report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-point-tangent-closed-fibre-singleton.json`: statement node, split in two proof steps; no new nodes; Mathlib search verdict remains no direct match.
- `citations.json`: two verbatim citations to `lem-sc-finite-type-nonclosed-closure-closed-points`.

2. Attachments: none.

3. WANTED: none.

4. The imported item was unsplit and had an incorrect `created.item` value from its parent delivery; this was corrected to the delivered item. The statement itself is retained. The proof makes explicit that a fibre over a closed point is closed, so closures of its points remain in the fibre, and it does not assume the fibre is quasi-compact.

5. Nothing remains unfinished.

## Review by K1

I read the item node and the unit route in `sk-thm-picard-rr`, and checked the source cited in `literature/stacks-project/varieties.tex`, Tag 0E8S, lemma-separate-points-tangent-vectors, at the paragraph after condition (1), together with Tag 0478. The item statement has the same hypotheses and conclusion: an algebraically closed base, a locally finite type source, a closed target point, and injectivity on closed points.

Step 1 uses only the existing statement `lem-sc-finite-type-nonclosed-closure-closed-points`; its quoted sentence explicitly gives infinitely many closed points in the closure of a nonclosed point. The remaining facts are elementary topology: the inverse image of the closed singleton `{p}` is closed, and a closed subset contains the closure of each of its points. I checked that all resulting closed points lie in the same fibre and therefore have the same image, which contradicts the item hypothesis.

Step 2 uses the same cited statement, with the same verbatim quote, to rule out every nonclosed point in the fibre. Once all fibre points are closed, injectivity on closed points gives at most one point; step 1 gives existence in the nonempty case. The empty-fibre case is preserved explicitly. The cited node was opened and its statement, source (Tags 0478 and 0A21), hypotheses, and Mathlib searches were checked before citation. Small cases checked were an empty fibre and a one-point fibre over `Spec k`; the argument also correctly rejects a hypothetical nonclosed point by producing multiple closed specializations.
