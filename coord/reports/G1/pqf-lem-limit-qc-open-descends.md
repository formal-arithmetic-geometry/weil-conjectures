# Stage 1 report: pqf-lem-limit-qc-open-descends

## Files written

- `dag/nodes/sec-nagata-compactification/pqf-lem-limit-qc-open-descends.json`: statement, Mathlib leaf; no new nodes.
- `citations.json`: empty, because the node is a Mathlib leaf and has no natural-language proof steps.

## Attachments

None. No sorry-free project declaration states this item.

## WANTED

None.

## Not duplicates

None. The existing `lem-weil-pbc-limit-affine-transition` node states existence and affine-stage restriction of scheme limits; it does not state descent or eventual equality of quasi-compact opens. The existing `lem-weil-pbc-limit-cone-affine-projections-opens` node states affine projections and the restricted-limit cone, but not the compact-open descent and eventual-equality clauses.

## Review by G1

I read the imported item and the unit route in `sk-prop-nagata-sketch-zmt`, then checked the source overlay `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`. `AlgebraicGeometry.exists_preimage_eq` states that a compact open of a limit is the preimage of a compact open at one stage, matching clause (1). `AlgebraicGeometry.exists_map_preimage_eq_map_preimage` states eventual equality of the preimages of two compact opens whose limit preimages agree, matching clause (2). `AlgebraicGeometry.isLimitOpensCone` identifies the limit of the preimages of an open at a stage; the same file supplies compactness of the later preimages and affine transition maps, matching clause (3). The hypotheses in the item (filtered inverse system, affine transitions, and quasi-compact/quasi-separated stages) specialize these declarations; the existing project Mathlib leaf `lem-weil-pbc-limit-cone-affine-projections-opens` records the latter interpretation. I ran LeanFinder, Loogle, and Mathlib grep searches for the item; Loogle returned no hits, while the source grep located all three declarations. Since the whole statement is a conjunction of one-line Mathlib specializations, I removed the imported agent proof and marked the item `status: mathlib`.

## What was wrong or incomplete

The imported node had a long agent-written proof despite all three clauses being directly available in Mathlib. No statement correction was needed.

## What remains

Nothing for this item.

## Second reading by G1

- Item statement: checked against Stacks Limits Lemma 32.4.11 (Tag 01Z4, `lemma-descend-opens`) and Lemma 32.2.2 (Tag 01YX, `lemma-directed-inverse-system-has-limit`), hypothesis by hypothesis; the filtered inverse system, affine transitions, qcqs stages, and quasi-compact open hypotheses are all present. Verdict: agrees with the imported statement and its cited source clauses.
- Mathlib leaf statement: checked against `AlgebraicGeometry.exists_preimage_eq` (AffineTransitionLimit.lean:341), `exists_map_preimage_eq_map_preimage` (:294), and `isLimitOpensCone` (:234). Clause (1) is the direct compact-open descent specialization; clause (2) first passes to a common upper stage and then applies the same-stage equality declaration; clause (3) is the restricted-open limit cone, with quasi-compactness of preimages and affine transition maps supplied by the affine-transition hypotheses. Verdict: valid specialization; no new node or proof step is required.
- Small cases: the empty open and whole scheme are covered by the compact-open hypotheses; affine schemes and a one-point field scheme reduce to the corresponding principal-open cases; no hypothesis is used when the index has one object.
- Blueprint audit: `tools/blueprint_refs.py search pqf-lem-limit-qc-open-descends` found only the item blueprint node; no duplicate blueprint statement exists. The node's recorded `same_as` list is empty.
- Search audit: reran LeanFinder, Loogle, and grep searches recorded in `searches.jsonl`; LeanFinder found `exists_preimage_eq`, Loogle was unavailable/no-hit for the unqualified names, and grep located the three declarations at the recorded lines.
- Changes: none to the node or citations; this section records the second-reader source, dependency, edge-case, blueprint, and search checks. The dry-run delivery preflight passed.
