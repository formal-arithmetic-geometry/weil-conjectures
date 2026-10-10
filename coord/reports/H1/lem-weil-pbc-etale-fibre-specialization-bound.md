# Stage 1 report

1. Files written:

- `lem-weil-pbc-etale-fibre-specialization-bound.json` (repaired item proof and metadata)
- `citations.json`

2. Attachments: none. I searched the slopmaster2 source by item id, source notions, and declarations; no sorry-free declaration states this item.

3. WANTED: none.

4. The returned split was wrong in three ways. Its Zariski shrinking claim that a union of etale neighbourhoods becomes finite is false; its idempotent node was not a fact used in the proof of Tag 09Z0 and had an incorrect source; and its dense-open argument incorrectly assumed every point has a generization in the dense open. I removed that node and replaced the route with the source's 07RZ stratification argument. The degree strata are closed by the universal property applied to residue-field points, and closedness gives both specialization monotonicity and the dense-open strict bound.

## Review by H1

I read the item, its blueprint ancestor `lemma-weil-pbc-finite-refinement-etale-cover`, and the existing statements of `lem-weil-pbc-etale-algebra-flat`, `lem-weil-pbc-etale-algebra-finite-presentation-localization`, `lem-weil-pbc-etale-ring-map-quasi-finite`, `lem-weil-pbc-flat-fp-qf-stratification`, and `lem-weil-pbc-etale-algebra-over-field-product`. Their hypotheses match the affine restriction of a quasi-compact separated etale morphism: flatness, local finite presentation, quasi-finiteness, and separatedness are all present before invoking 07RZ.

Step 1 uses exactly those etale consequences and the hypotheses of the stratification node. Step 2 uses the stratification statement's universal property for `Spec kappa(y)` and the finite separable product statement to identify degree with geometric points; the cited statements say these facts explicitly. Step 3 is elementary closed-set stability under specialization and therefore has no citation. Step 4 uses the same closed degree stratum and the elementary fact that a closed subset containing a dense open is the whole affine open; it does not quantify over generizations.

I checked the edge cases of an empty fibre, a one-point finite etale fibre, and an identity morphism. I also checked that the new proof has no finite-etale shrinking or idempotent-lifting assertion, that every cited step quote is present verbatim in `citations.json`, and that the item source now names Tag 07RZ and the relevant sentence of the Tag 09Z0 proof. The deleted idempotent node is not included in the delivery.

5. Nothing remains unfinished in the split; delivery preflight is the remaining check.
