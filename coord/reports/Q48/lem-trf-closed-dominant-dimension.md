## Files written

- `dag/nodes/sec-trace-formula/lem-trf-closed-dominant-dimension.json`: repaired split statement and five proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-local-dimension-formula.json`: repaired statement-only supporting node; Mathlib search found no match.
- `dag/nodes/sec-trace-formula/lem-trf-generic-fibre-closed-chain.json`: repaired statement-only supporting node; Mathlib search found no match.
- `dag/nodes/sec-trace-formula/lem-trf-closed-map-specializing.json`: repaired Mathlib leaf for `IsClosedMap.specializingMap`.
- `citations.json`: replaced with verbatim citations for every use in every proof step.

## Attachments

No finished Lean declaration with the item statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

## WANTED

None.

## Not duplicates

- `lem-trf-local-dimension-formula` vs `lem-kun-dimension-formula`: the existing node is the field-base equality for `dim_x X`; this node is the local-ring inequality for an integral dominant morphism over a locally Noetherian base.
- `lem-trf-generic-fibre-closed-chain` vs `lem-sc-closed-irreducible-dimension-trdeg`: the existing node computes the dimension of an irreducible closed subset from its generic residue field; this node supplies a closed point and an explicit maximal specialization chain in the generic fibre.
- `lem-trf-generic-fibre-closed-chain` vs `lem-trf-geometrically-integral-curve-factorization`: the existing node constructs a proper factorization into relative curves under excellent Noetherian hypotheses; this node is the generic-fibre chain statement for an arbitrary nonempty integral finite-type scheme over a field.
- `lem-trf-closed-map-specializing` vs `lem-weil-pbc-proper-closed-image`: the existing node only states that the image of a proper morphism is closed; this Mathlib leaf states specialization lifting for every closed map.
- `lem-trf-closed-map-specializing` vs `lem-trf-closed-dominant-dimension`: the item is a dimension formula whose closed-map hypothesis is an assumption; this node is the general topological specialization-lifting lemma used to exploit that assumption.
- `lem-trf-generic-fibre-closed-chain` vs `lem-trf-closed-dominant-dimension`: the item concludes a global dimension equality; this node is only the generic-fibre closed-point and chain assertion used in the equality proof.
- `lem-trf-local-dimension-formula` vs `lem-trf-closed-dominant-dimension`: the item compares global dimensions and includes the closed-map equality clause; this node is only the local-ring inequality used for the upper bound.

## Review by Q48

I reread the item against Stacks `morphisms.tex`, Tag 02JX (`lemma-alteration-dimension`) and its proof, and reread the supporting statements against Tag 02JU (`lemma-dimension-formula`) and Topology Tag 0066 (`topology-lemma-closed-open-map-specialization`). The item still has exactly the four 02JX hypotheses: a locally Noetherian target, integral source and target, dominant morphism, and locally finite type; the equality clause still assumes only that the underlying map is closed. I made the function-field notation self-contained by defining `k(U)` and `k(V)` as the generic-point stalks, with the generic-point and stalk definition nodes cited.

The local-dimension node now states the 02JU inequality with `\operatorname{trdeg}_{\kappa(s)}\kappa(x)` and labels its source as 02JU. It defines `R(S)` and `R(X)` as generic-point stalks, so it no longer cites the curve-specific `def-sc-function-field` for arbitrary schemes. Its hypotheses and conclusion agree with 02JU clause by clause. The generic-fibre node has corrected TeX and now cites generic-point and stalk notions in its statement; its assertion is the 02JX equality-proof input (nonempty integral finite-type generic fibre, a closed point, a length-`r` chain, and finite residue extension). The closed-map node defines both “closed map” and “specializes” inline, cites the topological-space convention, and is sourced to Topology 0066; its Mathlib match is exactly `IsClosedMap.specializingMap`, `Mathlib/Topology/Inseparable.lean:400`.

Step 1 uses the existing Mathlib leaf `lem-sc-scheme-stalk-dimension-generalization-chains` for the equality between local Krull dimension and specialization/generalization-chain length, then uses the repaired 02JU node with the residue-field transcendence term `\operatorname{trdeg}_{\kappa(y)}\kappa(x)`. The nonnegative term is dropped and the local dimension is bounded by global dimension. Step 2 follows 02JX. I wrote out the missing generic-fibre check: after choosing affine neighbourhoods `\operatorname{Spec}A` and `\operatorname{Spec}B` around the generic points, dominance gives an injection `A\to B`; localization at `A\setminus\{0\}` gives a nonzero domain chart, preserves finite type, and has the same fraction field. The resulting fibre is nonempty, integral, locally finite type over `k(U)`, and its points and specialization chains identify with the points over the generic point in `V`, so the generic-fibre node applies. Step 3 uses the inline-defined closed-map specialization-lifting statement and iterates it along the base chain. Step 4 concatenates the fibre and lifted chains and takes the supremum over generic-point chains. Step 5 uses the existing proper-closed-map node and the elementary fact that a finite field extension has transcendence degree zero.

I checked every cited node's statement directly and rewrote `citations.json` with verbatim statement text for each citation in each step. I checked the hypotheses at the points where they are used, including dominance for the affine injection and nonemptiness, closedness for specialization lifting, and properness plus finite generic extension in the final clause. I tested the edge cases `r=0`, zero-dimensional integral schemes, and the generic-fibre localization when the base is a field; no statement was weakened. The seven returned faults are all repaired: the 02JU residue-field term and label, the 02IZ citation, the explicit affine generic-fibre argument, the broken TeX, the inline closed-map definition, the Topology 0066 label, and the curve-specific function-field citation.
