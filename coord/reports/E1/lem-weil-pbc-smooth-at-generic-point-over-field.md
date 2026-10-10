# Delivery: lem-weil-pbc-smooth-at-generic-point-over-field

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-smooth-at-generic-point-over-field.json`: split into two steps following Stacks 07ND, 00TV and 00TB.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-local-separable-residue-smooth.json`: statement, Stacks 00TV; Mathlib verdict: no match after LeanSearch, Loogle and source grep.
- `coord/reports/E1/lem-weil-pbc-smooth-at-generic-point-over-field.md`: this report.

## Attachments

None.

## WANTED

None. The source was read in the checked-out Stacks Project at `algebra.tex`, Lemma 00TV (`lemma-separable-smooth`), Lemma 07ND (`lemma-smooth-at-generic-point`) and Definition 00TB (`definition-smooth-at-prime`).

## Corrections and findings

The item statement is faithful to the field-base specialization of Stacks 07ND and was not changed. The imported source description mentions 07ND's finite-presentation and fraction-field base-change reductions. In this specialization they are unnecessary: the base is already the field `k`, and Stacks 00TV applies directly to the finite type `k`-algebra `S` at `(0)`. The proof now records the substantive argument: `S_(0) = L = kappa((0))`, a field is regular, the residue extension is separable, and 00TV gives smoothness at `(0)`; 00TB yields the stated nonzero `g`.

The new node is the full 00TV equivalence, strictly more general than the item. It is self-contained, carries no proof sketch, and cites definition nodes for localization and residue fields, field extensions, separability, smoothness at a prime, and regular local rings.

## Unfinished

The new 00TV node is intentionally `unsplit` and joins the Stage 1 queue. Nothing else is unfinished in this delivery.

## Review by E1

I read Stacks Algebra Lemmas 07ND and 00TV and Definition 00TB. The item's domain, finite-type, fraction-field separability, and generic-prime hypotheses match 07ND; the child states 00TV with its field, finite-type algebra, prime, separable residue-field, and regular-local hypotheses. Step 1 uses the localization statement to identify both the local ring and residue field with the fraction field, then uses the existing field-regularity node and the item's separability hypothesis. Step 2 applies exactly the regular-local direction of 00TV and expands smoothness at $(0)$ using 00TB; each cited node states the fact used, and neither step hides a non-elementary argument. The new node is statement-only, has the Stacks tag/label source, TeX, complete object introductions, and independent LeanSearch, Loogle, and Mathlib grep records; I searched the DAG for an existing 00TV declaration before accepting it. I checked the edge case $S=k[x]$ at $(0)$, where the fraction field is separable and the conclusion gives the expected generic smooth locus. No section A-F issue remains: one commit, only item/new-node/report files, split report present, no duplicate node or cycle, and no statement or route was weakened. No correction was sent back to the worker.
