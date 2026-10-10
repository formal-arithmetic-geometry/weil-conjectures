1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-picard-locus-closed-valuation-criterion.json` (statement, split)
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-valuation-probe-closure.json` (statement-only, unsplit; Mathlib searches found no exact match)
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-closed-range-preimmersion.json` (Mathlib leaf: `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion`)
- `citations.json`

2. Attachments: none.

3. WANTED: none.

4. The item had no sorry-free declaration in the project source. The split follows Stacks Tags 02JQ and 01R8. The new node isolates the valuation probe at a closure point; it is strictly smaller than the item and does not restate the conclusion.

5. Nothing remains unfinished.

## Not duplicates

lem-sc-picard-valuation-probe-closure vs lem-sc-picard-locus-closed-valuation-criterion: the new node supplies the valuation probe at each closure point, while the item concludes that the image is closed from the factorization hypothesis.
lem-sc-picard-valuation-probe-closure vs def-nagata-dense-valuation-probe: the existing definition selects a probe only for an affine target and a schematically dominant source; the new statement applies to an arbitrary quasi-compact immersion and every point in the closure of its range.

## Review by C1

I read the item source in `literature/stacks-project/morphisms.tex` at Tags 02JQ and 01R8, and checked the corresponding source-side implementations in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean` and `WeilConjectures/Compactification/ValuativeCriterion.lean`. No declaration tagged with this item exists in `WeilConjectures/`.

Step 1 uses exactly the new probe statement: it supplies A, K, the generic map through j, and the closed-point map to an arbitrary closure point. Step 2 uses only the item's valuative hypothesis and the definition of closure, so it is elementary once Step 1 has supplied the probe. Step 3 uses that an immersion is a preimmersion and the Mathlib leaf `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion`; the leaf states precisely the needed closed-range criterion.

For the new node I searched the whole DAG and blueprint for valuation-probe and Tag 02JQ duplicates, then ran LeanFinder, Loogle, and Mathlib grep searches. LeanFinder returned only general valuation-criterion and image-density declarations; Loogle returned no match; grep found no exact declaration in Mathlib. I tested the statement on the identity immersion (where the probe can be the local valuation ring at the point) and on a closed immersion (where the conclusion is immediate), and verified that the hypotheses include quasi-compactness needed by Tag 02JQ.

## Second reading by C1

- Item statement: checked against More on Morphisms, Tags 02JQ and 01R8 and the parent proof use; the quasi-compact immersion and valuative-factorization hypotheses and the closed-image/closed-immersion conclusions agree.
- Step 1: checked against Tag 02JQ and the statement of `lem-sc-picard-valuation-probe-closure`; it supplies exactly the valuation ring, fraction field, generic lift, commutative restriction, and closed-point specialization used.
- Step 2: checked against the item hypothesis and the definition of topological closure; applying the factorization hypothesis puts the closed point in the range, and the closure argument is elementary.
- Step 3: checked against the statement of `lem-sc-picard-closed-range-preimmersion` and the definition of immersion; the Mathlib leaf gives the stated closed-immersion criterion.
- `lem-sc-picard-valuation-probe-closure`: checked hypothesis by hypothesis against Tag 02JQ (using the quasi-compact immersion as the quasi-compact morphism); tested on an identity immersion, a closed immersion, and the empty-source edge case. It is statement-only and strictly smaller than the item.
- `lem-sc-picard-closed-range-preimmersion`: checked against `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion` in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`, line 65; the declaration is an exact match and all three Mathlib searches are recorded.

Changes made: no mathematical statements or proof steps required correction. I verified that the existing imported dense-source probe is specialized to affine schematically dense maps and therefore does not replace the new closure-point probe. I added this independent source-and-node review, retaining the worker's citations and search records.
