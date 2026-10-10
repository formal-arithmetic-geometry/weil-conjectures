# lem-weil-pbc-free-module-sheaf-sheafify-first

## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-free-module-sheaf-sheafify-first.json`: statement, 0 new nodes; Mathlib leaf through `CategoryTheory.GrothendieckTopology.W_of_preservesSheafification`.

## Attachments

None. No sorry-free Lean declaration states this item exactly.

## WANTED

None. I read `sites-modules.tex` from the read-only `/home/ubuntu/c1-stacks-review/` cache because this clone has not rebuilt `literature/stacks-project/`.

## Finding

`lem-weil-pbc-free-module-sheafification-local-iso` in the same chapter already has the same conclusion under the same hypothesis, and is a reviewed Mathlib leaf. The assigned node was created later as a duplicate for a different parent, so I marked this item itself as a Mathlib leaf rather than creating a new proof node or modifying its other user. Its old `mathlib_candidate` said the assertion was absent from Mathlib; I corrected that entry to the established match. The statement was kept. I added `def-weil-pbc-free-module` to its statement dependencies. Preflight required a non-null `proof_origin` even for a Mathlib leaf, so I recorded `by: agent` because 03AC omits its proof and the match is assembled from the cited Mathlib declarations.

## Review by E1

I read Modules on Sites Lemma 03AB (`lemma-obvious-adjointness-sheaves`) and Lemma 03AC (`lemma-may-sheafify-before-abelianize`) in `sites-modules.tex`, lines 370-409. Lemma 03AC says that forming a free abelian sheaf is unchanged when the set presheaf is sheafified first; its proof is omitted. The item's map-level formulation for a commutative coefficient ring is the corresponding naturality assertion, and follows from the free-module adjunction of 03AB. Neither lemma imposes a condition beyond a site and the coefficient object, so the item's hypotheses suffice.

I compared the assigned statement with `lem-weil-pbc-free-module-sheafification-local-iso`: both quantify over a site, a ring, set presheaves and a morphism whose set sheafification is an isomorphism; both conclude that the induced map on sheafified free-module presheaves is an isomorphism. The existing node allows any ring, so the assigned commutative-ring case is included. Searches across the DAG for the Stacks tags, assertion words and Mathlib names found that existing node; blueprint searches for the assertion and tags found no blueprint node with the same statement. A source-tree search found no sorry-free Lean declaration with this item's ID or its exact assertion.

I checked the Mathlib source used by that leaf: `ModuleCat.free` constructs the objectwise free module (`Adjunctions.lean:40`), `ModuleCat.adj` makes it a left adjoint (`:94`), `GrothendieckTopology.PreservesSheafification` is supplied for a left adjoint (`Sites/Adjunction.lean:107`), and `W_of_preservesSheafification` carries a local equivalence through objectwise free modules (`Sites/PreservesSheafification.lean:66-70`). `W_iff` (`Sites/Localization.lean:80-82`) says that being in this local-equivalence class is exactly becoming an isomorphism after sheafification. Thus the assumption on the set-presheaf map gives precisely the conclusion on the induced module-presheaf map. This is a leaf, so there are no proof steps and no uncited non-elementary facts to audit in steps.

For small cases, the identity on any presheaf gives an identity free-module map; an isomorphism of presheaves gives an isomorphism objectwise; the empty set presheaf gives the zero free module on each object. All agree with the statement. I checked the node's Stacks tag and label, the added definition dependency, the absence of a new node or cycle, the single-backslash TeX in JSON, and the blueprint ancestor and `same_as` fields. No mathematical correction to the statement was needed; the correction is the Mathlib verdict and the duplicate finding.
