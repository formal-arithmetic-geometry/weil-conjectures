Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-regular-dimension-one.json`: repaired item split with four direct proof steps; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-p1-polynomial-noetherian.json`: Mathlib leaf, `Polynomial.isNoetherianRing`.
- `dag/nodes/sec-picard-framework/lem-sc-p1-polynomial-regular.json`: Mathlib leaf, `Polynomial.isRegularRing_of_isRegularRing`.
- `dag/nodes/sec-picard-framework/lem-sc-p1-polynomial-dimension-one.json`: Mathlib leaf, `IsPrincipalIdealRing.ringKrullDim_eq_one`.
- `citations.json`: verbatim statement excerpts for every step citation.

Attachments: none.

WANTED: none.

The returned version was wrong because its first two auxiliary nodes merely restated the first two clauses of the item, and its dimension step used a topological dimension theorem for a different projective-line construction. I deleted those three relabelling nodes. The repaired proof starts from the standard cover `U_0 = Spec k[t]`, `U_1 = Spec k[s]`; it proves quasi-compactness using the existing affine-spectrum result, local Noetherianity from the Noetherian polynomial-ring leaf, and regularity from the polynomial regular-ring leaf. The dimension step uses the affine stalk localization statement, the existing localization-height statement, and the existing supremum-of-heights statement, with the strict chain `(0) subsetneq (t)` for the lower bound. Every new node has complete `created` metadata and is statement-only.

## Review by H1

I read the returned item, its parent blueprint node `thm-sc-p1-duality`, Stacks Example Tag 01JE, and the statements of every cited node. Step 1 now cites the exact standard-chart formulas from `def-sc-p1-standard`, the existing statement that `Spec R` is quasi-compact, the new statement that `k[t]` is Noetherian, and the definition of locally Noetherian; these hypotheses are sufficient for the finite two-chart cover. Step 2 cites the chart formulas, the new polynomial regularity statement, and the regular-scheme definition, whose statement explicitly requires affine neighbourhoods with Noetherian regular coordinate rings. Step 3 cites the existing affine-open stalk statement (which explicitly identifies the local ring with the localization), the existing localization dimension/height statement, and the existing ring dimension as the supremum of prime heights, then applies the new `dim k[t] = 1` leaf. The lower-bound chain `(0) subsetneq (t)` is written directly, so no projective topological dimension result is used. Step 4 is the short definitional assembly and cites the definitions it unfolds.

For the three new leaves I searched the DAG and blueprint first and then checked LeanSearch, Loogle/LeanFinder, and Mathlib source grep. The Noetherian leaf was checked at `Mathlib/RingTheory/Polynomial/Basic.lean:759`; the regular leaf at `Mathlib/RingTheory/RegularLocalRing/Polynomial.lean:78`, using the existing field-regular node; and the dimension leaf at `Mathlib/RingTheory/KrullDimension/PID.lean:37`. I tested the dimension claim on the field case and the chain `(0) subsetneq (t)`, and checked both standard charts are symmetric under renaming the variable. The repair also fixes the prior missing `created.by` and `created.date` fields.
