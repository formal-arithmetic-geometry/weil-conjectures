# Worker report: lem-zl-bertini-field-extension

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-field-extension.json` — split statement with nine proof steps.
- `lem-zl-geometric-irreducibility-transcendental` — statement node; no Mathlib match (Stacks Tag 0G31).
- `lem-zl-geometric-irreducibility-subextension` — statement node; no Mathlib match (Stacks Tag 037N).
- `lem-zl-geometric-irreducibility-add-transcendental` — statement node; no Mathlib match (Stacks Tag 0G32).
- `lem-zl-geometric-irreducibility-separable` — statement node; no Mathlib match (Stacks Tag 0G33).
- `lem-zl-finite-separable-closure` — statement node; no combined Mathlib match (Stacks Tag 037Q).
- `lem-zl-finite-intermediate-fields` — Mathlib leaf, `Field.finite_intermediateField_of_exists_primitive_element` in `Mathlib/FieldTheory/PrimitiveElement.lean:305` (using `Field.exists_primitive_element` for finite separable extensions).
- `citations.json` and this report.

## Attachments

None. I searched the slopmaster2 source for the item id, its Bertini names, and the statement's key terms; no sorry-free declaration states this item.

## WANTED

None.

## What I checked and corrected

I read the imported item, its parent `lem-zl-bertini-irreducible-member`, the unit and chapter records, the current main-20261015 blueprint proof for the parent, and the full Stacks Project proof of Tag 0G4D in `literature/stacks-project/more-morphisms.tex` (lines 8907–9009). I searched the whole DAG and blueprint for Tags 0G4D, 0G31–0G33, 037N, 037Q, and 030N and for the corresponding field-theoretic phrases. The only directly reusable existing result was the Mathlib primitive-element API; the six smaller nodes above therefore state exactly the remaining inputs used by the proof. Every new node has the required LeanSearch, Loogle or LeanFinder, and Mathlib grep searches recorded in its JSON; the item searches were rerun as well.

## Review by NR

The item statement agrees clause by clause with Stacks Tag 0G4D: `K/k` is finitely generated and geometrically irreducible, `n≥1`, the `g_i` and `c_i` satisfy the displayed algebraic-independence hypothesis in `Frac(K[x_1,…,x_n])`, and the conclusion is geometric irreducibility over `k(x_1,…,x_n,Σg_ix_i)`. I retained the imported statement and its four statement dependencies.

Step 1 reads the automorphism construction in Tag 0G4D. The substitutions preserve `K_0` and `K_2`; the asserted transcendence degree two follows directly from the hypothesis that `x_i`, `ξ`, and `δ` are algebraically independent, so I marked this elementary. Step 2 uses the full equivalence in `lem-zl-geometric-irreducibility-separable`, whose statement is exactly the reduction from geometric irreducibility to excluding separable algebraic elements. Step 3 applies `lem-zl-finite-separable-closure` to the finitely generated extension `Ω/K_2`, then the finite-intermediate-fields Mathlib leaf to its finite separable closure; the cited statements explicitly provide finiteness and the finite set of intermediate fields. Step 4 uses that finite set for the pigeonhole choice of distinct `a_1,a_2`, then writes the two linear identities for `ξ_1,ξ_2`; the remaining algebraic-independence and transcendence assertions are direct field calculations, so this is elementary apart from the cited finiteness.

Step 5 applies `lem-zl-geometric-irreducibility-transcendental` to `Ω/K_0`, `lem-zl-geometric-irreducibility-subextension` to `K_0(ξ_1,θ_1)`, and `lem-zl-geometric-irreducibility-add-transcendental` with `ξ_2`; the tower fields match each cited hypothesis. Step 6 uses the equality of the two chosen intermediate fields and the converse of the separable-element criterion to put `θ_2` in `K_0(ξ_2)`, then applies `σ_{a_2}^{-1}`. Steps 7–9 check the finite-field case exactly as the final paragraph of 0G4D: adjoining an independent `t` makes the base infinite, preserves the displayed algebraic independence, repeats the already-expanded infinite-field argument with all its hypotheses, and descends by the converse direction of the transcendental-extension node.

I checked edge cases `n=1`, an infinite ground field, a finite ground field, and the case `δ=0` (which is excluded by the stated algebraic independence). I also checked that the two chosen parameters are distinct before dividing by `a_2-a_1`, that `θ_i` lie in the finite separable closure used in Step 3, and that `ξ_2` is transcendental over `K_0(ξ_1,θ_1)` because `θ_1` is algebraic over `K_0(ξ_1)`. No source error or missing hypothesis was found.

## Not duplicates

lem-zl-finite-intermediate-fields vs lem-weil-pbc-finite-separable-extension-primitive-element: the existing node states existence of one primitive element generating a finite separable extension; this node states finiteness of the entire set of intermediate fields, a distinct consequence supplied by Mathlib's `finite_intermediateField_of_exists_primitive_element`.
lem-zl-finite-intermediate-fields vs lem-weil-pbc-finite-separable-primitive-element: the existing node states existence of one primitive element for a finite separable extension; this node states finiteness of all intermediate fields and records the separate Mathlib declaration that proves it.
