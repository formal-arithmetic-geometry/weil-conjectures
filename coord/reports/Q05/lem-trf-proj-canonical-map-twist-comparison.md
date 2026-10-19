Files written:

- `dag/nodes/sec-trace-formula/lem-trf-proj-invertible-map-twist-iso.json` — statement-only Stacks comparison node; Mathlib searches found no exact match.
- `dag/nodes/sec-trace-formula/lem-trf-proj-canonical-map-twist-comparison.json` — split item; Mathlib searches found no exact match.
- `citations.json` — verbatim citations for the two non-elementary uses.

Attachments: none. No sorry-free declaration in `WeilConjectures/` carries the item, and the source grep found no declaration tagged `(blueprint: lem-trf-proj-canonical-map-twist-comparison)`.

WANTED: none.

The imported item is well-typed and matches Stacks Constructions Tags 01NK and 01N8. The item proof has three steps: the existing generation-locus Proj construction identifies the stated canonical map; quasi-compactness gives a finite nonvanishing subcover and a common positive degree, whose powers generate every multiple; and the new general comparison node applies the 01NK/01N8 graded comparison in each degree `d*k`. I did not weaken or change any hypothesis. I checked that the empty scheme, a degree-one generator, and the case `k=1` are all covered by the same finite-subcover argument (for the empty scheme the finite subcover is empty and any positive `d` works).

## Review by Q05

I read the item source record and the full statements of `lem-trf-space-line-module-proj-map` and the new `lem-trf-proj-invertible-map-twist-iso`. Step 1 uses only the former's explicit scheme clause saying that its generation-locus map is the usual canonical morphism from graded maps into tensor powers, so the cover hypothesis identifies its domain with all of `Z` and its chart characterization agrees with the item's `r`. Step 2 uses no external node: quasi-compactness supplies finitely many nonvanishing opens, taking a common multiple of their positive degrees preserves each nonvanishing locus under powers, and the resulting degree-`d` sections generate; taking further powers gives generation in every degree `d*k`. Step 3 uses the new node's exact hypothesis and conclusion with `V=Z` and degree `d*k`; its statement is the general open-subscheme form of the Stacks 01NK graded comparison, while the item is only the finite-subcover specialization. I read `constructions.tex` at the 01NK graded comparison/final assertion and 01N8 converse construction, including the local fraction maps and uniqueness. I also checked the node metadata, blueprint ancestry, statement dependencies, Mathlib search logs, and the verbatim quotes in `citations.json`. The server `check_dag` preflight passes.

What could not be finished: no Lean proof was written or compiled, as required for this stage-1 delivery.

## Not duplicates

lem-trf-proj-invertible-map-twist-iso vs lem-trf-proj-canonical-map-twist-comparison: the new node is the general open generation-locus theorem with a degree-d graded sheaf isomorphism; the item specializes it to a quasi-compact global cover and all common multiples.
lem-trf-proj-invertible-map-twist-iso vs def-sc-invertible-section-ring: the new node is a comparison theorem for an arbitrary graded map into a line module; the existing node only defines the section-ring graded algebra.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-ample-proj-canonical-map-chart-formula: the existing node treats the section ring and fraction pullback equations, while the new node treats arbitrary A and proves the pullback twist isomorphism.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-ample-proj-canonical-map-preimage-forward: the existing node proves one pointwise basic-open implication for a section-ring map; the new node gives a sheaf-level twist isomorphism for arbitrary graded maps.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-ample-proj-canonical-map-preimage-reverse: the existing node proves the reverse pointwise implication; the new node proves no pointwise criterion and instead proves the generated-degree line-bundle comparison.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-ample-proj-canonical-map-preimage: the existing node combines pointwise inverse-image implications for the section ring; the new node is the arbitrary graded-map twist comparison.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-ample-proj-compatible-quotient-charts: the existing node constructs compatible local quotient morphisms and scalar fraction identities only; the new node asserts the generated-degree pullback line-module isomorphism.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-proj-chart-pullback-fraction-relation: the existing node is a ring-level cross-multiplication identity on one chart; the new node is a sheaf-level canonical twist isomorphism.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-section-ring-chart-denominator-generator: the existing node proves freeness of powers of one denominator section on a section-ring chart; the new node compares the Proj twisting sheaf with an arbitrary target line module.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-section-ring-chart-cross-multiplication: the existing node proves a numerator equation between two section-ring charts; the new node proves the canonical degree-d pullback map is an isomorphism.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-section-ring-coefficient-data-arithmetic: the existing node extracts coefficient ring arithmetic from numerator equations; the new node concerns Proj twisting sheaves and arbitrary graded maps.
lem-trf-proj-invertible-map-twist-iso vs lem-sc-section-ring-coefficient-data-numerator: the existing node constructs local coefficient numerators; the new node states the global generated-degree twist comparison.
