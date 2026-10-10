# def-pc-dimension

## Files written

- `dag/nodes/sec-abelian-varieties/def-pc-dimension.json`: split definition; no new nodes or Mathlib leaves.

## Attachments

None. The slopmaster2 audit records no declaration, and searches for the blueprint tag and the dimension notions in `WeilConjectures/` found no declaration stating this definition exactly.

## WANTED

WANTED: `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-def-av-jacobian/def-pc-dimension.md`, for `def-pc-dimension`. The local checkout has no `literature/blueprint/` directory. I checked the statement imported verbatim into the node against the available Stacks pages instead; the definition has no proof steps requiring that file.

## Corrections and limits

The imported statement depended on `def-pc-base-change` and `def-pc-scheme` but omitted the definitions of ring Krull dimension and finite type. It now cites `def-weil-pbc-krull-dimension-ring`, `def-weil-finite-type-morphism`, and `def-pc-scheme-fibre`; the fibre node already states the requisite base change. The phrase defining relative dimension over every base point was undefined when the fibre was empty, since this item defines dimension only for nonempty schemes. I restricted that clause to points with nonempty fibre; its final clause still quantifies over all nonempty fibres. No proof or cited fact was moved into a new node.

The blueprint's last clause is weaker than Stacks Tag 02NJ, which requires each nonempty fibre to be *equidimensional* of dimension `d`. For example, `Spec k` disjoint union `A^1_k` has dimension one but is not equidimensional. Over `Spec k`, its structure morphism has relative dimension one under the blueprint wording and does not under 02NJ. I retained the blueprint's definition rather than silently replacing it with the Stacks convention. This difference may matter to later users of the node.

LeanSearch returned HTTP 500 on three queries. LeanFinder, Loogle, and the local Mathlib source search completed; the failure is recorded in `mathlib_searches`. The existing unsplit `lem-pc-scheme-dimension-local-rings` already states the comparison with Mathlib's topological dimension, so I created no duplicate.

## Review by E1

I read the item's imported statement and the statements of all four dependency nodes. For the dimension clause I checked Stacks Properties Lemma Tag 04MU, which states exactly that the topological dimension of a scheme equals the supremum of the dimensions of its local rings. `def-pc-scheme` supplies schemes and their local rings; `def-weil-pbc-krull-dimension-ring` defines the Krull dimension used on those rings. For the fibre clause I checked Stacks Schemes Definition Tag 01K0: `def-pc-scheme-fibre` states its scheme-theoretic fibre `X_s`, and `def-weil-finite-type-morphism` states the finite-type hypothesis. The definition has no proof steps and cites no lemma to prove itself. `lem-pc-scheme-dimension-local-rings` is a separate comparison theorem, not a statement dependency of this definition.

I checked the other relevant source, Stacks Morphisms Definition Tag 02NJ, clause (3), against the last clause of the item. It requires equidimensional fibres, which the imported blueprint sentence does not say. I checked the distinction on the disjoint union of a point and an affine line over a field. I also checked the empty scheme: its dimension is excluded by the item's first clause, so the original pointwise phrase had no value at an empty fibre; the revised phrase now has the needed nonempty hypothesis. For `Spec k` the local ring and the fibre both have dimension zero, and for `A^1_k` both have dimension one, as expected.

For B1-B9 I checked that no new node was created, all notions in the revised statement have direct defining nodes, the TeX has single backslashes in the decoded JSON, and `blueprint.same_as` is `[]`: whole-blueprint searches found no other node with this combined definition. `def-kun-dimension` overlaps only the first clause and does not define relative dimension. For C1-C8 and D1-D5 there are no proof steps to cite or split; I removed the unused base-change edge and checked that the remaining four edges point to existing, unmerged definitions. For E1-E7 I checked the finite-type hypothesis, the empty-fibre boundary, and the dimension-one non-equidimensional example. The corrections were the missing dependencies and the nonempty-fibre qualifier; I did not alter the blueprint's weaker relative-dimension convention.
