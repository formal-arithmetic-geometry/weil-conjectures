# Worker report: lem-coef-cartesian-marked-slice-restriction

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cartesian-marked-slice-restriction.json` — statement node, split; no new nodes; Mathlib search verdict: no match.
- `citations.json` — verbatim statement excerpts for every cited step/node.

## Attachments

None. I searched the slopmaster2 source for the item id, its title words, and the marked Cartesian slice formulation; no declaration states the item exactly.

## WANTED

- Archival local copy of Lurie, *Higher Topos Theory*, Proposition 3.1.1.11 and Proposition 2.4.1.8, which are cited by the item and are currently available only from the online PDF named in the node source.

## What I checked and changed

The imported statement already has the correct objects and hypotheses: the ordered join uses the initial simplex block followed by the diagram block, the base slice uses `pa`, and the restriction map records both the `U`-restriction and the base simplex. I found no duplicate statement in the DAG or current blueprint. The Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch) returned only ordinary Kan/model-category or ordinary fibered-category declarations, so this remains an unsplit project theorem rather than a Mathlib leaf.

I supplied a four-step proof and kept all four imported statement dependencies. Step 1 expands a boundary lifting problem into the degreewise pushout
`J_n=((∂Δ[n]⋆V)∪_{∂Δ[n]⋆U}(Δ[n]⋆U))→Δ[n]⋆V`, including the empty boundary for `n=0`. Step 2 filters the marked-anodyne map through its generators and explains the three relevant fillers: inner-horn cells use the inner-fibration condition, marked outer-horn cells use the defining final-horn condition for the specified `p`-Cartesian images of marked edges, and marking-extension cells use the same Cartesian-edge condition. The existing marked-anodyne lifting-calculus statement supplies the marked pushout-product construction. Step 3 checks closure under pushouts, transfinite compositions, and retracts and therefore obtains all diagonals with strict agreement on the prescribed `U`-part and base map. Step 4 matches vertex surjectivity and all positive-dimensional boundary fillers with the explicit definition of a trivial Kan fibration.

## Review by Q01

I read the item node, `sk-prop-sf-biduality-general.json`, `sec-six-functors.json`, and the current blueprint ancestor `prop-coef-integral-exceptional-adjoint.proof.md`. I also opened the statements of `def-cbc-enhanced-diagrams-cones`, `def-coef-infinity-fibrations`, `lem-coef-marked-anodyne-lifting-calculus`, and `def-weil-pbc-trivial-kan-fibration`. There are no new nodes to review. Step 1 uses the degreewise product/pullback convention and the explicit trivial-Kan boundary convention; those statements say exactly that products and pullbacks are degreewise and that the required data are boundary maps with a prescribed target simplex. Step 2 uses the quasicategory inner-horn clause, the Cartesian-edge final-horn clause, and the marked-anodyne pushout-product clause; I checked that the hypotheses match the item (`p` is an inner fibration and every marked edge of `V` maps under `q` to a `p`-Cartesian edge). Step 3 uses the explicit inner-fibration horn range and the marked-anodyne closure under pushouts, transfinite compositions, and retracts; these are exactly the closure operations used in the cell induction. Step 4 uses the verbatim definition of trivial Kan fibration, including the `n=0` surjectivity clause. I tested the edge cases `n=0`, `U=V`, `U=∅`, `V=∅`, and the identity map: the pushout description remains well-typed, and no extra nonemptiness or Cartesian-lift-existence hypothesis is introduced. I corrected the proof from a generic “marked-anodyne maps lift” claim to an explicit generator-by-generator argument so that only the stated inner-fibration and Cartesian-edge properties are used.

## What remains

No unresolved proof or statement issue remains in this sandbox. The item has no SGA citation and introduces no additional coefficient category or base-change hypothesis.
