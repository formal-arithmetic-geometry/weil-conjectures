# Stage-1 report: lem-sfb-borel-root-product-coordinates

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-borel-root-product-coordinates.json`: split item; statement and statement dependencies unchanged; five proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-positive-weight-equivariant-inverse.json`: one new statement-only lemma, unsplit; no Mathlib match.
- `citations.json`: eight step/node entries, copied verbatim from the actual cited statements.
- `searches.jsonl`: actual msearch results, retained as generated.

## Attachments

None. Searches of the live `lean/WeilConjectures/` for the blueprint tag, Borel, unipotent radical, root subgroup, rootSubgroup, positive weights and Luna found no declaration of this theorem. The only unipotent hits are categorical biproduct matrices.

## WANTED

None. The required Milne book is present in `literature/milne-algebraic-groups_iAG2017.pdf`.

## Defects found and corrected

The imported item had no proof and no proof dependencies. Its statement is faithful to Milne 21.68(a) and Remark 21.69, so no statement correction or dispute is necessary. I expanded the two assertions that Milne states tersely: multiplication lands in the unipotent radical as a scheme morphism, and its tangent map is an isomorphism. Neither assertion is replaced by a new node restating an item clause. The single new node is the general inverse theorem for arbitrary smooth connected affine schemes with positive tangent weights, independent of reductive groups and ordered products.

The inherited blueprint ancestor is null. `blueprint_refs.py ancestor` confirms this; I retained that upstream field and its long via chain rather than inventing an ancestor. The item's exact place is already filled. The new node prepends this item to the inherited via chain and specifies 13.42 as the supporting argument in 21.68(a). Whole-blueprint searches for root subgroup, 21.68, Luna, positive weight, contracting and tangent space found no equivalent imported statement.

## Unfinished

No part of this one-level split remains unfinished. The new inverse lemma is deliberately unsplit, for a later worker. No Lean was written and no compiler, Lake or build was invoked.

## Not duplicates

lem-sfb-positive-weight-equivariant-inverse vs lem-sfb-projective-attracting-cells: the existing node constructs strata for a projective scheme with finite fixed locus; it does not assert that an equivariant map of affine schemes with invertible tangent map is an isomorphism.

lem-sfb-positive-weight-equivariant-inverse vs lem-sfb-luna-borel-attraction-charts: the existing statement concerns invariant affine opens of a Borel flag variety, not inverse morphisms or tangent-weight hypotheses.

lem-sfb-positive-weight-equivariant-inverse vs lem-sfb-cocharacter-limit-smooth-structure: the existing statement represents limit subgroup functors and computes Lie subspaces; it has no inverse theorem for general equivariant scheme morphisms.

lem-sfb-positive-weight-equivariant-inverse vs lem-sfb-borel-root-product-coordinates: the new node concerns arbitrary smooth connected affine schemes, fixed points and an independently supplied tangent isomorphism. The item must construct the multiplication map, prove its subgroup containments and compute its differential; none of those clauses is asserted by the new node.

No new node carries a Stacks tag shared with an existing node. Milne is the primary source here, so I did not invent a Stacks attribution.

## Review by Q29

I read the worker brief, stage-1 contract, GOAL, the three blueprint levels in SETUP, the item's chapter and unit records, and both copies of delivery-errors B--E. I read Milne 21.68(a) and Remark 21.69 (printed pp.445--446) for the item, 13.41--13.42 (pp.269--270) and the smooth tangent criterion before 13.35 (p.267) for the new lemma. The new statement specializes the torus to G_m and assumes both schemes smooth, so an invertible differential supplies precisely the local hypothesis of 13.42. Positive means positive integer character weights, with no characteristic-zero assumption. Its notions are introduced explicitly or cited by definition nodes; its proof, proof dependencies and proof origin are empty/null as required for a new unsplit node.

I opened the statement of every cited node. In step 1 the regular-cocharacter node explicitly supplies B=P(lambda), its Lie decomposition and positivity, and the Borel-pair node defines Phi+ as the roots in Lie(B). Thus this is the positive chamber for the given B, not a freely chosen incompatible chamber. Step 2 uses the limit-subgroup node's actual functor on all algebras, smoothness, normality and unipotence; the Borel-pair statement identifies U as the largest such subgroup of B. The root-parametrization statement gives the universal conjugation formula. The polynomial t^n a at n>0 extends over A[t] and vanishes at zero even when A is nonreduced, so the needed scheme containment follows without reasoning merely from geometric points. Step 3 takes the semidirect-product isomorphism and projection/kernel literally from the Borel-pair statement. The decomposition from step 1 plus equivariance of that projection kills each nonzero character component by comparing Laurent-polynomial coefficients. It does not use an unproved assertion about Lie-exactness of an arbitrary quotient. Step 4 takes the Ga parametrizations and their specified tangent spaces from the root-parametrization statement. Smoothness of the polynomial source is checked directly by lifting variables, equivariance by cancellation of adjacent t inverse/t factors, and the differential by the dual-number calculation; these are elementary steps and do not become nodes. Step 5 applies exactly the hypotheses stated in the new inverse lemma: smooth connected affine finite-type source and target, fixed points, equivariance, positive weights and the computed differential. Its quote includes the empty-weight convention and conclusion. All eight citations have contiguous verbatim quotes of the statements actually used.

I checked the item on a torus (no roots, U=1), SL2 in characteristic 2 (the root character still has positive integer cocharacter weight 2, even though its differential may vanish), and the upper triangular GL3 case in either order of the simple root factors: in order 12,23,13 the top-right coordinate is c+ab, with polynomial inverse c=z-ab. This illustrates why the theorem is a scheme isomorphism but need not be a group homomorphism from the direct product. I checked the new lemma on Spec F (vacuous positive weights), weighted affine spaces and triangular coordinate changes. The map z -> z^p in characteristic p fails the invertible-differential hypothesis; the Artin--Schreier map z -> z^p-z is not equivariant for any positive weight on the source and target. Disconnected extra components are excluded by connectedness. The positive-weight assumption avoids trying to deduce a global inverse from an arbitrary local inverse.

I searched the whole DAG by source numbers, Luna, positive tangent weights and equivariant etale keywords; read the nearby attraction and cocharacter statements; and searched the whole imported blueprint. The searches exclude elementary, duplicate, item-clause and Mathlib candidates for the one new node. The msearch logs show two semantic phrasings for the inverse theorem, Loogle, LeanSearch and two source greps; all queries ran successfully. Hits were etale/smooth definitions, general affine morphism properties or ordinary affine maps. The item's new searches found abstract root pairings and SL line stabilizers, which have neither group schemes nor the required product theorem. I read the apparent IsEtale and SL lineStab sources: they are not matches. All new-node search entries use the exact executed query text, and the old item search records are retained. No service failure is misreported as no match.

Finally I checked each step against C1 and C4, kept the elementary calculations in the proof, verified all other facts have a cited statement, and checked the union of uses equals proof_deps. Every proof step is under 1000 characters, so no long step hides another lemma. No SGA source, altered route, compiler invocation, repository write or launcher edit is involved.
