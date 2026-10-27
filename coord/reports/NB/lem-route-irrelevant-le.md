# Worker report: lem-route-irrelevant-le

## Files written

- `dag/nodes/sec-nagata-compactification/lem-route-irrelevant-le.json` — item, statement split, no Mathlib leaf.
- `dag/nodes/sec-nagata-compactification/lem-route-graded-basechange-irrelevant.json` — closed attachment node for `GradedRingHom.IsGradedBaseChange.irrelevant_le`.
- `citations.json` — verbatim step citations.

## Attachments

`GradedRingHom.IsGradedBaseChange.irrelevant_le` belongs to `lem-route-graded-basechange-irrelevant` (source `WeilConjectures.AlgebraicGeometry.RelativeProj.ChartBaseChange`, lines 177–188; no `sorry`).

## WANTED

None.

## Not duplicates

- `lem-route-graded-basechange-irrelevant` vs `lem-nagata-affine-proj-scalar-extension`: the new node is the generic irrelevant-ideal consequence of coefficientwise base change; the existing node is the full affine Proj scalar-extension construction with chart formulas and a cartesian square.
- `lem-route-graded-basechange-irrelevant` vs `prop-nagata-relative-proj-functoriality`: the new node isolates the generic graded-ring inclusion; the existing proposition states several relative-Proj functoriality clauses and does not state this generic lemma as a standalone result.

## What was wrong or provisional

The imported item was a machine-made provisional restatement of a SHEAF theorem whose proof was `sorry`; it did not identify the coefficientwise base-change intermediate or the existing generic irrelevant-ideal theorem. I replaced it with the exact affine restriction inclusion and retained the source route through the local-squares argument. No hypothesis was added or removed.

## What I could not finish

No additional statement-only node was needed: the affine quasi-coherent section theorem is cited from the existing DAG node `lem-weil-pbc-quasi-coherent-affine-section-base-change`, and the only new support node is the closed attachment recorded above.

## Review by NB

I read the live item declaration `AlgebraicGeometry.RelativeProjAlgebra.irrelevant_le` in `lean/Sheaf/AlgebraicGeometry/RelativeProjData.lean` (lines 121–129), including its hypotheses `W ≤ V`, its source and target gradings, and the map `A.restriction h`. I also read the source definition and route in `RelativeProjAffineRestriction.lean`, and the blueprint proof of `lemma-nagata-relative-proj-exists`, especially the local-squares paragraph. The item statement now matches the declaration's inclusion exactly in words and keeps the affine-open and graded-section context from the source.

Step 1 applies the existing `lem-weil-pbc-quasi-coherent-affine-section-base-change` statement degreewise to the homogeneous components; its canonical tensor isomorphism is exactly what the coefficientwise hypothesis requires, and assembling the degrees is elementary from the grading and restriction definitions. Step 2 applies `lem-route-graded-basechange-irrelevant`, whose statement is exactly the target irrelevant ideal inclusion for a coefficientwise graded base change. That node is attached to the existing sorry-free declaration `GradedRingHom.IsGradedBaseChange.irrelevant_le`, and I checked its source proof at lines 177–188. The step is non-elementary and cites both statements; `citations.json` quotes the precise clauses used.

I searched the whole DAG and blueprint for the generic irrelevant-ideal fact and for `irrelevant_le`; the generic project theorem had no existing DAG node, so I attached it in the new closed node. I checked the nearby existing nodes `lem-nagata-proj-affine-restriction`, `lem-nagata-affine-proj-scalar-extension`, and `prop-nagata-relative-proj-functoriality` to rule out duplicate statements and recorded the distinctions above. I checked the edge cases of degree zero (irrelevant ideals use only positive degrees), empty positive-degree components, and the identity affine restriction: the generic lemma still gives the inclusion, and no flatness or equality of degree-zero algebra with the base is assumed. The pre-report server check returned `check_dag OK`.
