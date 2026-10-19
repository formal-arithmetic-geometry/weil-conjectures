# Stage-1 report: sk-d-dl-a1-setup

## Files written

- `dag/nodes/sec-deligne-laumon-a1/sk-d-dl-a1-setup.json`: item, definition, split; no new node and therefore no Mathlib leaf.
- `dag/units/sk-d-dl-a1-setup.json`: filled the key unit's `realized` and `realized_by` fields.
- `citations.json`: empty because the item is a definition with no proof steps.

## Attachments

- `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant` belongs to `sk-d-dl-a1-setup`, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/DeligneLaumon/AffineLine/Defs.lean:72` (the exact source declaration is sorry-free).
- `AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity` belongs to `sk-d-dl-a1-setup`, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/DeligneLaumon/AffineLine/Defs.lean:94` (the exact source declaration is sorry-free).

## WANTED

None.

## What was wrong or incomplete

The imported item was still `unsplit`, had no statement dependencies, and left `blueprint.same_as` null even though `rem-dl-a1-conventions` gives the same setup in a more detailed form. I changed only the item metadata: it is now `split`, cites the existing definition and theorem nodes that supply each convention, and records the blueprint overlap. No new node was created because every non-elementary notion is already present in the DAG; creating separate restatements for the two source predicates would have duplicated existing declarations. The item remains the concise setup statement from main-20261015, while the extra irreducible-lisse material in `rem-dl-a1-conventions` is not silently copied into it.

## Review by Q88

I read the complete item source `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-d-dl-a1-setup/_section.md`, the chapter and unit records, and the complete existing `rem-dl-a1-conventions` node. I also read `Defs.lean` at the two tagged declarations and checked that neither declaration contains `sorry`. The finite-field, affine-space, projective-line, geometric-cohomology, geometric-Frobenius, Weil-sheaf, lisse, punctual-weight, and Tate-twist clauses are supplied by `def-weil-finite-field-fiber`, `def-sbc-affine-space`, `def-sc-p1-standard`, `def-weil-ordinary-compact-cohomology`, `def-weil-frobenius-detailed`, `def-weil-weil-sheaf-complex`, `def-pod-lisse-l-adic-sheaves`, `def-weil-punctual-weights`, `def-wf-tate-twist`, and `lem-tw-tate-twist-weight-shift`. The direct-image definition and its inertia-invariant stalk formula are stated by `def-wf-middle-extension` and `lem-wf-boundary-stalk-invariants`; the curve perverse identification is stated by `lem-dl-a1-curve-intermediate-extension`; and the extension-at-infinity and geometric-constancy definitions are stated in the attached source declarations and fully described by `rem-dl-a1-conventions`. Since this is a definition, there are no proof steps or nontrivial citation quotes. I verified that all fourteen dependency IDs exist, that none depends back on the item, and that the unit realization now points to this key node. No statement was changed and no duplicate node was introduced.
