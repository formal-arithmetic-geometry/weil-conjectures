# Stage-1 delivery: lem-pur-closed-support-open-counit

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-closed-support-open-counit.json: statement, split into five steps; no Mathlib match for the complete statement.
- citations.json: fourteen step/node records with verbatim statement quotations.
- searches.jsonl: actual searches retained from this attempt, including the second semantic phrasing completed before the provider interruption.

No new nodes; no Mathlib leaves created. The statement and statement dependencies are unchanged. No unit record is edited: this item is a supporting lemma, not the unit's statement.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, id, closed-support/open-counit terminology and alternate name spellings found no project declaration proving every clause. Nearby pro-etale closed-support results and Zariski module extension results have different categories and do not provide an attachment. No Lean file was written or compiled.

## WANTED

None. The sources used are available in literature/stacks-project/.

## Corrections and scope

The original unsplit statement is correct. Its source includes 095L, but that short exact sequence cannot be applied directly to the arbitrary open U without choosing a complementary closed subscheme. The proof instead follows 095L's geometric-stalk argument, using the already cited closed support k(Z) only to produce the open W on which F vanishes. The step does not assume that Y is Noetherian, that A is torsion, or that B is constructible. It does not use the Zariski O-module closed-pushforward stalk node for an etale A-module sheaf.

The imported Mathlib searches were preserved, and five actual NE search records were appended. Both semantic phrasings were read: the first returns Zariski Scheme.Modules restriction/pushforward adjunctions, whereas the second returns general derived exact-functor factorization and single-object comparison isomorphisms. Mathlib's general counit naturality is directly relevant to the final calculation, but a natural transformation's naturality is part of its definition and needs no new node. These hits do not prove the complete etale statement. No searches were invented or repeated after the interruption.

## Review by NE

I read Stacks etale-cohomology.tex Definition 03S3 (definition-extension-zero), the paragraph identifying inverse image for an etale morphism with restriction, the extension presheaf formula, Proposition 03S5 (proposition-describe-jshriek), and Lemma 095L (lemma-ses-associated-to-open), including its proof identifying the actual adjunction map on stalks. I also read derived.tex 015F (lemma-right-derived-exact-functor), including its statement for unbounded derived categories. The blueprint ancestor is thm-pur-rank-one-thom, current main-20261015 proof Step 2; its use is the compact image of the origin class in the affine chart. This split supplies only that sheaf/derived-counit comparison and follows no SGA route.

For step 1, I opened lem-weil-pbc-extension-by-zero-adjunction and checked that its statement explicitly identifies j^{-1}H(V) with H(V over Y), rather than merely asserting an abstract adjunction. def-weil-pbc-direct-image explicitly gives evaluation on the fibre product, including the constant-ring module action. def-weil-open-immersion identifies U with an open subscheme, so j is a monomorphism: maps into it are determined by their composites into Y. This proves the stated fibre-product comparison by its two projections. The identity on sections then commutes with restrictions and A-actions. It is not an appeal to general proper base change.

For step 2, def-weil-closed-immersion gives the closed subset k(Z). The direct-image formula evaluates on an empty fibre product over its open complement. A sheaf of modules has exactly one section on the empty object by the empty-cover sheaf condition, hence that module is zero. The same open-restriction description in the adjunction node proves that this is the asserted sheaf restriction, not just a statement about selected global sections.

For step 3, lem-weil-pbc-extension-by-zero-stalks states both the precise interior germ isomorphism and exterior zero stalk. The adjunction node states that the specified counit is induced by the identity on interior sections, so the stalk map itself is the identity under this isomorphism; an unspecified isomorphism between the two sheaves would not suffice. Outside U the open W from step 2 contains the point; intersecting any pointed etale neighbourhood with W kills its section germ, as the colimit definition def-weil-pbc-geometric-stalks requires. lemma-weil-pbc-geometric-stalk-conservative says exactly that the underlying abelian-sheaf map is invertible. I explicitly checked that the inverse is A-linear, rather than silently changing categories. This is the single non-elementary step, with all stalk theorems named. Its text is below 2000 characters.

For step 4, lem-weil-pbc-extension-by-zero-exact gives exactness and preservation of quasi-isomorphisms for j_! on constant-module sheaves, and prop-weil-pbc-inverse-image-modules-exact gives the corresponding module inverse image and exactness for every commutative coefficient ring. def-weil-exact-derived-adjunction specifies the exact derived adjunction's original localized counit. Thus the original counit's inverse localizes to an inverse, and applying the functor to rho and rho^{-1} preserves their inverse equations. This is a consequence of the cited exact adjunction and functor laws, with no resolution comparison or boundedness hypothesis hidden in the step.

For step 5, I checked the direction and types of every map. With J=Dj_! and P=D(j^{-1}), naturality is epsilon_M after JP(c) = c after epsilon_F. Precomposing with J(rho^{-1}) yields exactly epsilon_M after J(c_U) = c after e. Naturality is in the derived category and applies to arbitrary derived c, not only maps of sheaves. This proves the integer-shift clause without an extra cohomology/Ext identification. The only cited node is the definition of the specified adjunction, which includes a natural counit.

I checked delivery-errors B--E against the files: no new duplicate, elementary or clause-restatement nodes are introduced; every non-elementary input has a node whose statement I opened; all citations are verbatim and proof_deps is the union of uses; the source is specified by tags and labels. Definitions suffice for the routine section and functor computations, which are written out as elementary steps. The geometric-stalk argument retains the correct site and coefficient category. Generic off-unit sheaf tools are declared in split_report.tool_uses and do not replace the model-purity route. No step exceeds 2000 characters.

The edge cases B=0, Z empty, U=Y, and A the zero ring give the asserted zero or identity maps. If U is empty, Z is empty and both supported sheaves are zero; the naturality equation still has the displayed types. Removing closedness of k would invalidate the open-complement vanishing argument, but closedness is an explicit hypothesis. M remains arbitrary and unbounded throughout the final calculation.

## Not duplicates

No new nodes.

## Unfinished

Nothing remains in the stage-1 split; the existing unsplit dependencies remain their own items.
