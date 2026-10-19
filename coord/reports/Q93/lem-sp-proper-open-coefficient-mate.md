# Delivery report: lem-sp-proper-open-coefficient-mate

Files written:

- `dag/nodes/sec-smooth-purity/lem-sp-proper-open-coefficient-mate.json` — statement, split proof, blueprint provenance, and seven recorded Mathlib searches; no new nodes.
- `citations.json` — verbatim statement excerpts for every cited node in every proof step.

Attachments: none. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` or `/home/ubuntu/weil-newtargets-master/WeilConjectures/` carries the item tag or its exact coefficient/site statement.

WANTED: none.

The imported statement was retained. I checked the two coefficient rings on the edge case $A=\mathbf Z/4\to B=\mathbf Z/2$, where $B$ is not flat, so the use of derived tensor and the explicit “no flatness” clause are necessary. Identity proper/open squares reduce both displayed composites to the identity by the mate and adjunction triangle laws. The zero complex and empty open are also covered because all maps are natural transformations in the derived categories. The bounded-below hypotheses in the second display are exactly those required by the existing proper site-comparison mate; no boundedness was silently added to the first unbounded statement.

No source error or duplicate was found. The imported Mathlib searches were retained, and I reran the required item searches with both original and alternate phrasings. Mathlib returned only generic change-of-rings, pushforward, and mate-calculus declarations; none states this normalized proper/open coefficient square, so the item is not a Mathlib leaf.

## Review by Q93

I read the item node, its unit/chapter metadata, the Stacks source `more-etale.tex` at Tags 0F7B/0GL6, and the coefficient-reduction blueprint `sk-lem-sp-reduction-exceptional.md` and its proof. I also opened every node used by the three proof steps. Step 1 uses `lem-amb-unbounded-proper-open-interchange` for the exact open-adjunction normalization of $\Gamma_R^{\rm et}$, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` for the canonical derived tensor/pullback comparison and its naturality, and `lem-weil-pbc-mate-pasting` for uniqueness and composition of adjoint mates. These statements apply to the given finite commutative rings and to the unbounded first equation; the step explicitly checks that the two paths are mates of the same inverse-image composite.

Step 2 uses `lem-weil-pbc-comparison-pullback` for compatibility of $\nu^*$ with inverse image, `lem-weil-pbc-comparison-direct-image-canonical-mate` for the named proper counit mate $d_v$ and its normalization, `lem-cbc-proetale-extension-zero-comparison` for the natural open comparison $e_a$ and composition compatibility, together with the tensor and mate-pasting statements from Step 1. Their hypotheses match the finite-ring etale-origin bounded-below input in the item. The transported open-adjunction prescription is exactly the definition of $\Gamma_R^{\rm pro}$, so the step proves the named site map equality rather than an unspecified isomorphism.

Step 3 uses the naturality clauses of the tensor, proper-mate, open-comparison, and proper/open-interchange nodes. Since all displayed factors are natural, their composites are natural in $E$. I checked every quote in `citations.json` is a verbatim part of the cited node statement. No new node was introduced: the only non-elementary ingredients are already stated by the existing nodes, and the final naturality step is a direct composition consequence. The blueprint provenance is the existence/uniqueness/naturality paragraph of `det-sp-reduction-exceptional`, where coefficient maps are defined as adjoint transposes and normalized by the open adjunct.

What was corrected: the imported item had no proof, no proof dependencies, no blueprint `from.place`, and an empty `split_report`; these are now filled. The statement and all original statement dependencies remain unchanged.
