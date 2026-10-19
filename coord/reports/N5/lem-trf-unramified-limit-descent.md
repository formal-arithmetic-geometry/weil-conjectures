# Stage 1 report: lem-trf-unramified-limit-descent

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-unramified-limit-descent.json`: statement split, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-colimit-unramified-algebra.json`: statement-only node, no Mathlib match.

Attachments: none.

WANTED: none.

The item statement agrees with Limits Tag 0C4W, including only local finite type on the initial morphism and no finite-presentation, flatness, or Noetherian hypothesis. The source's affine algebra input is strictly smaller than the item and is recorded separately as Tag 0C4F. I searched the DAG and blueprint for 0C4F, colimit-unramified, and the corresponding keywords; no duplicate or blueprint node states that algebra lemma. The Mathlib searches for the new node found only formal-unramified, base-change, and finite-type APIs, with no finite-stage filtered-colimit descent theorem.

## Review by N5

I read the item's source at `literature/stacks-project/limits.tex`, Tag 0C4W, and the source of the new node at `literature/stacks-project/algebra.tex`, Tag 0C4F. Step 1 uses the qcqs finite affine covers and the local affine characterization in the cited scheme convention and unramified definition; I checked that the finite covers are available for the stated qcqs schemes and that no stronger hypothesis is introduced. Step 2 uses the existing affine-transition limit statement to identify every affine chart after base change with the corresponding limit of affine charts, and the locally-finite-type hypothesis supplies the finite-type ring map required by the algebra lemma. Step 3 uses the existing affine ring criterion exactly for the unramified affine chart, applies the new 0C4F statement, then takes a common directed upper bound of finitely many indices; the existing base-change stability node justifies passage to that upper stage. I verified every quoted citation against the cited node statements and recorded those verbatim in `citations.json`. Small cases checked include a constant inverse system, an identity morphism, an empty source chart, and a finite separable algebra over a field; all give the claimed eventual stage.
