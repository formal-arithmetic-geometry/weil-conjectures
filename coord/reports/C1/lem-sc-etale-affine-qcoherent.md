# lem-sc-etale-affine-qcoherent

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-etale-affine-qcoherent.json`: repaired split, using the reviewed 03F9 criterion.
- `dag/nodes/sec-curve-estimates/lem-sc-etale-standard-cover-cech.json`: retained existing statement-only child (03OZ).

## Attachments

None. The generic criterion `lem-weil-pbc-cech-vanishing-criterion` is an existing reviewed node.

## WANTED

None.

## Repair

The returned version incorrectly used the 03OW spectral-sequence edge and filtration assertions, and added 03P1 as an unnecessary child. I removed that child and removed the spectral-sequence, cohomology-pullback-functorial, and locally-zero dependencies. The repaired proof uses the existing 03F9 criterion exactly as requested: affine fibre products establish condition (1), the 0218 affine refinement establishes condition (2), and the 03OZ disjoint-union comparison plus affine sections and Amitsur exactness establish condition (3). The final step identifies derived evaluation at the final object with the definition of etale cohomology.

## Review by C1

I read Stacks Sites Cohomology Lemma 03F9 and its proof, Etale Cohomology Theorem 03P2, Topologies Lemma 0218, Schemes Lemmas 01I4/01JQ, and Lemma 03OZ. The item statement is the affine clause of 03P2 with arbitrary affine X and quasi-coherent F; no extra finiteness or separatedness hypothesis was introduced. The retained child states the finite affine etale family/disjoint-union Cech comparison of 03OZ, including faithful flatness and compatibility of face maps.

Step 1 cites the 03F9 criterion, affine fibre-product node, and 0218. Their statements say respectively what conditions (1) and (2) require, that iterated products of affines over an affine are affine, and that every etale cover of an affine has a finite affine etale refinement. Step 2 cites 03OZ, affine fibre-product sections, pullback identity/composition, the etale quasi-coherent associated-sheaf definition, and Amitsur exactness. These statements identify every Cech term and face map with the Amitsur complex for a faithfully flat map, whose positive cohomology is zero. Step 3 applies 03F9 at U=X and cites `def-weil-pbc-etale-cohomology`, whose definition is derived global sections/evaluation at X.

I checked the empty family/zero-ring edge and the zero module: all terms are zero and the criterion still applies. I also checked q=1 directly: it is included because 03F9 proves all positive derived degrees by dimension shifting, so no spectral-sequence intermediate-row argument is needed. The parent proof dependencies equal the union of step uses, and no removed node remains cited. Mathlib searches for the item found no exact etale quasi-coherent vanishing theorem; the existing 03F9 node was checked transitively against the sorry map and is reviewed, so no attachment to a sorried Lean declaration is claimed.
