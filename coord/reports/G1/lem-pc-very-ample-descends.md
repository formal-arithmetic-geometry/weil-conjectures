# Delivery report

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-very-ample-descends.json`: item, statement, five proof steps, and split metadata.
- `dag/nodes/sec-picard-framework/lem-pc-fpqc-descend-closed-immersion.json`: statement-only dependency, Mathlib no-match.
- `dag/nodes/sec-picard-framework/lem-pc-proper-descends-field.json`: statement-only dependency, Mathlib no-match.

## Attachments

None. `AlgebraicGeometry.IsVeryAmple.of_pullback` in `WeilConjectures/AlgebraicGeometry/Modules/Ample.lean:468-482` still contains `sorry`.

## WANTED

None.

## What was wrong

The returned version used an auxiliary finite section space and an enlargement lemma, which did not meet the complete-linear-system definition of very ampleness. I deleted that node and rewrote steps 1-3 around the complete system: after properness descends, flat coherent base change identifies the complete system over $K$ with $H^0(X,\mathcal L)\otimes_kK$, so the complete system over $k$ base changes to $i_K$. I also made the common-zero argument and the exact fpqc target cover explicit, removed the properness lemma from `stmt_deps`, and corrected its source to Descent Tag 02L1. The Lean theorem `AlgebraicGeometry.IsVeryAmple.of_pullback` still has `sorry`; no attachment was possible.

## Review by G1

I reread the blueprint proof for `lem-pc-very-ample-descends`, the returned node, and the source Lean docstring and declaration in `WeilConjectures/AlgebraicGeometry/Modules/Ample.lean:468-482`. I read the exact statements of `def-sc-ample`, `def-pc-base-change`, `lem-sc-flat-base-change-coherent`, `lem-pc-proper-descends-field`, and `lem-pc-fpqc-descend-closed-immersion`; the properness node source now reads `Descent, Lemma Tag 02L1 (label lemma-descending-property-proper)`. I also verified that the deleted enlargement node is not cited anywhere in the repaired item.

Step 1 uses the complete-linear-system clause of `def-sc-ample` to obtain $i_K$ and properness descent. Step 2 uses the flat cohomology formula from `lem-sc-flat-base-change-coherent` after step 1 has made $X$ proper, and uses `def-sc-ample` to identify the defining space. Step 3 uses the same formula, the complete-system clause, and `def-pc-base-change` to identify the base-changed morphism with $i_K$. Step 4 explicitly checks that the common zero locus pulls back to the empty common zero locus on $X_K$ and that $X_K\to X$ is surjective. It then uses the single-member fpqc cover `{P(V^\vee)_K\to P(V^\vee)}`, the base change of `Spec K -> Spec k`, whose member is affine and quasi-compact, and cites `def-pc-base-change` plus the exact closed-immersion descent statement. Step 5 uses only the complete-linear-system and tensor-power clauses of `def-sc-ample`, so no separate very-ample-implies-ample node is needed.

For each retained new node I checked the DAG, blueprint, Lean source, and Mathlib searches. `lem-pc-proper-descends-field` and `lem-pc-fpqc-descend-closed-immersion` remain statement-only with complete hypotheses and no hidden proof. I checked the identity field extension and the empty scheme as edge cases; the common-zero argument also handles the possibility that a section space might otherwise fail to define a projective morphism. The citation manifest contains a verbatim quote for every cited node at every step. The repaired item has no off-unit `tool_uses`, as required.

