# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-generic-constancy-geometric-reducedness.json`: split statement; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-generic-fibre-geometrically-reduced-open.json`: new statement node for Stacks Tag 0578; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-generic-fibre-not-geometrically-reduced-open.json`: new statement node for Stacks Tag 0577; no Mathlib match.
- `citations.json`: verbatim statement quotes for every proof dependency.

Attachments: none.

WANTED: none.

No statement, blueprint, or brief error was found. The item is a specialization of the two finite-type Stacks lemmas because quasi-compact plus locally finite presentation is finite type by definition. The generic-fibre alternatives are genuinely smaller than the item and are not restatements of its biconditional.

## Not duplicates

- `lem-trf-generic-fibre-geometrically-reduced-open` vs `lem-trf-generic-constancy-geometric-reducedness`: the new node assumes geometric reducedness of the generic fibre and concludes only geometric reducedness on an open; the item includes both alternatives and an equivalence.
- `lem-trf-generic-fibre-not-geometrically-reduced-open` vs `lem-trf-generic-constancy-geometric-reducedness`: the new node assumes failure at the generic fibre and concludes only failure on an open; the item includes both alternatives and an equivalence.
- `lem-trf-generic-fibre-geometrically-reduced-open` vs `lem-trf-geometrically-reduced-fibre-locus`: the former is the 0578 generic-fibre spreading lemma; the latter is the separate affine constructibility and arbitrary-base-change theorem for the entire reduced-fibre locus.
- `lem-trf-generic-fibre-not-geometrically-reduced-open` vs `lem-trf-geometrically-reduced-fibre-locus`: the former is the 0577 non-reduced generic-fibre alternative; the latter concerns constructibility and base change, not this implication.

## Review by Q50

I read the item node and its unit route, the source passage in `literature/stacks-project/more-morphisms.tex` at Tags 0577, 0578, and 0579, and the existing `lem-trf-geometrically-reduced-fibre-locus` node. The item statement keeps exactly the imported hypotheses: a quasi-compact, locally finitely presented morphism, an irreducible base with generic point, and the fibrewise geometric-reducedness equivalence, with no flatness, reducedness, Noetherianity, or nonempty-fibre assumption. The two new statements match the corresponding Stacks hypotheses and conclusions clause by clause, including allowing empty fibres.

Step 1 uses only the definition node `def-weil-finite-type-morphism`, whose statement says that finite type means quasi-compact together with the finite-type local condition; the given locally finite presentation condition supplies locally finite type. I marked this step elementary because it is the direct definitional implication. Step 2 uses the exact conclusion sentence of the 0578 node in the geometrically reduced case and the exact conclusion sentence of the 0577 node in the opposite case. Excluded middle supplies one of the cases, and in either case the resulting nonempty open has precisely the biconditional required by the item. The citations file quotes the relevant statements verbatim.

For each new node I searched the DAG and blueprint by the Stacks tags and by the generic-fibre/geometrically-reduced keywords before creating it; no existing node states either alternative. I ran LeanFinder, Loogle, and Mathlib grep searches for each alternative. The returned Mathlib declarations concern definitions and elementary reducedness criteria only, so neither alternative is a Mathlib leaf. I tested the alternatives on the identity morphism (reduced generic fibre and all fibres reduced), on a nilpotent thickening over a field (non-geometrically-reduced generic fibre and no reduced fibres), and on the empty source (the conclusions are vacuous). No cycle is introduced: both new nodes depend only on definitions, and the item depends on them.
