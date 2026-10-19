# Stage 1 report: lem-per-isolated-intersection-dimension-bound

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-isolated-intersection-dimension-bound.json` — statement, split proof, and five proof steps; no new Mathlib leaf.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-cohomology-change-rings.json` — statement-only node; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-cohomology-top-nonvanishing.json` — statement-only node; Mathlib searches found no match.
- `citations.json` — verbatim statement quotes for every cited node in every item step.

## Attachments

None. I searched the slopmaster2 source for the item tag and its mathematical terms; no sorry-free declaration states this item.

## WANTED

None. The Stacks source is present locally.

## Problems checked

The imported item is mathematically well-typed and agrees with Stacks Project Tag 0DXF. Its finite-dimensional local-ring hypothesis is retained. The closed-subset clause implies the closed point belongs to the subset, so the quotient ring used in the proof is nonzero. I found no statement error, blueprint error, or missing source dependency. I searched the DAG and blueprint for the two local-cohomology inputs and found no duplicate nodes; the quotient-spectrum and radical facts are existing Mathlib leaves and are cited instead of duplicated.

## Review by Q41

I read the item node and the unit/chapter records, then read the complete source proof of Stacks Project Tag 0DXF in `literature/stacks-project/local-cohomology.tex`. I also read the source statements of the existing quotient-spectrum node, the radical/zero-locus node, the Noetherian-ring definition, and the topological Krull-dimension definition. The two genuinely non-elementary inputs from the source, Tag 0DXA (change of rings for cohomological dimension) and Tag 0DXE (top local-cohomology nonvanishing), are recorded as the two new statement-only nodes with their own Mathlib searches.

Step 1 uses the existing quotient-spectrum statement to write the closed subset as the spectrum of a quotient, the Noetherian definition to transfer Noetherianity to the quotient, and the Krull-dimension definition to identify and bound its dimension. I checked that the hypothesis forces the defining ideal to be proper, hence the quotient is nonzero and local with maximal ideal induced by `m`.

Step 2 uses the existing quotient-spectrum homeomorphism and the existing radical/zero-locus statement. I checked that primes containing the extended ideal correspond exactly to primes containing both defining ideals, so the isolated-intersection hypothesis gives the radical of the extended ideal equal to the quotient maximal ideal.

Step 3 is the elementary finite-generation and power-containment argument. No new node is needed: Noetherianity gives generators of the maximal ideal, radical containment gives powers of each generator in the support ideal, and the monomial argument gives equality of the two torsion functors. Applying one injective resolution then gives equality of their derived functors and cohomological dimensions.

Step 4 uses the new change-of-rings node and the new top-nonvanishing node. I verified that the quotient map has Noetherian source and target, that the quotient is nonzero local of the finite dimension obtained in Step 1, and that nonvanishing in degree `d` forces `d ≤ cd` by the definition of cohomological dimension.

Step 5 applies the same quotient-spectrum statement to `Z = V(p)` and checks the prime-quotient identification, yielding the stated “in particular” clause. Every `uses` entry is included in `proof_deps`, and every citation quote in `citations.json` is copied verbatim from the cited node statement. The recorded Mathlib searches were run before writing the nodes; all returned declarations were inspected and found to be definitions or Krull/support-dimension results rather than these local-cohomology theorems.
