# Stage-1 worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-extension-zero-stratified-perfect.json`: existing item split into four proof steps; no new nodes.
- `citations.json`: verbatim citations for every node used by every proof step.

## Attachments

None. I found no sorry-free declaration in the source checkout carrying the item tag or its full statement.

## WANTED

None.

## What was checked and corrected

The item was checked against the source route named in its record (Bhatt–Scholze, Lemma 6.1.12, Proposition 6.6.11, and Definition 6.7.6/Lemma 6.7.7). The imported item had no proof. I kept its statement and dependencies, and made the open/closed argument explicit. Step 1 uses the localized-ringed-site node's exactness and sheafified extension-by-zero construction to justify the derived functor. Step 2 checks restriction on each stratum directly from that presheaf construction, then uses the profinite coefficient inverse-image node for the compatible completed-coefficient identifications and the perfect-complex and derived-tensor definitions for the model. Step 3 checks the presheaf on the slice over the closed complement is zero, so its sheafification and derived complex vanish. Step 4 verifies that the zero complex is perfect from the definition. I read the statement of every cited node and recorded the exact sentences used in `citations.json`; no cited node is being used for a fact absent from its statement. The finite affine Noetherian cover and quasi-compactness are retained as hypotheses of the item and are part of the ambient compactification setup, but the local extension argument itself does not need them.

## Review by NL

I read the item source and the four cited source statements in the DAG. For Step 1, `lem-pur-site-restriction-module-adjunction-exact` says both exactness and that extension by zero is the sheafification of the extension-by-zero presheaf; `def-weil-abstract-derived-category` supplies the localization at quasi-isomorphisms, and `def-pur-localized-ringed-site` supplies restriction to a slice. For Step 2, I verified that restriction to a stratum lying in U is sectionwise the identity by the localized-site definition, and that `lem-weil-pbc-profinite-coefficient-inverse-image` gives canonical inverse-image isomorphisms compatible with quotient transitions. The perfect model conclusion uses exactly the definition in `def-pc-perfect-ring-complex` and the stated derived tensor convention. For Step 3, the closed immersion hypothesis identifies the complement as a closed subset, and the extension-by-zero presheaf is zero on the slice over that complement; this proves the claimed inverse-image vanishing. Step 4 is the bounded zero complex, which is perfect by the cited definition. I checked the small edge cases (empty U or empty strata: the same presheaf and zero-complex arguments apply) and found no statement error or duplicate node to add.
