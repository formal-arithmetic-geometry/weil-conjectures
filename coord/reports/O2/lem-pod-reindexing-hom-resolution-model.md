# Stage-1 report: lem-pod-reindexing-hom-resolution-model

## Files written

- dag/nodes/sec-poincare-duality/lem-pod-reindexing-hom-resolution-model.json — statement, split into eleven explicit proof steps; no complete Mathlib match.
- citations.json — one verbatim statement quotation for every step/node citation (22 entries).
- searches.jsonl — the prescribed search command's original log, retained without modification.
- report.md — this report. write_split.py is sandbox-only preparation code, not a delivered node.

New nodes: 0. New Mathlib leaves: 0. The statement is unchanged word for word. Added the missing statement dependencies defining module sheaves, tensor flatness, and the ordinary unbounded derived category. No chapter or unit record is changed: this item is a helper, not the unit's key statement.

## Attachments

None. I searched the complete live WeilConjectures source for the exact blueprint docstring tag, reindexing and resolution/Hom terminology, and inspected the pro-etale InternalHom file. AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar proves an underived fixed-coefficient comparison, not all the arbitrary completed-ring, K-resolution, product-complex and derived-normalization clauses of this item. It is not an attachment of this item. No compiler or Lake command was run.

## WANTED

None: the blueprint and the Stacks sources used here are present locally.

## Problems corrected

The live item was unsplit, with an empty proof. Its statement's reference to exact reindexing did not yet give the ring-action lifting for the nonconstant completed sheaf, preservation of K-injectives and K-flats, or the infinite-product complex comparison. These arguments are now written out rather than deferred to new nodes restating clauses of the item. I retained every statement clause, its source, blueprint ancestry, original search history and other existing metadata.

Stacks 0GMX is an underived comparison map, not the unbounded derived assertion. Stacks 0GN2 additionally assumes finite presentation and flatness; it cannot prove the arbitrary-source clause by direct application. I use the existing site-isomorphism Hom theorem instead, and form the derived comparison on actual product Hom complexes. The ordinary inverse image on completed-ring modules is kept distinct from the quotient-tower completed pullback, precisely as the statement requests. The intended identity of composites is under the canonical reindexing unit identifications; it is not an assertion of literal equality of chosen skeletal site functors.

## Unfinished work

None for this one-level split. Existing cited nodes remain responsible for their own proofs. This delivery contains no Lean files.

## Not duplicates

No new nodes were created. The generic site equivalence, tensor/Hom comparison, K-injective existence and RHom invariance are all reused from existing nodes. Whole-DAG and blueprint searches for reindexing, K-injectives and internal Hom found no existing blueprint statement giving all the item's arbitrary completed-ring and representative-level clauses. The blueprint internal-Hom pullback results for perfect inputs are more restrictive and do not replace the arbitrary unbounded-source comparison here.

## Review by O2

I read the chapter sec-poincare-duality and unit sk-def-weil, and the current main-20261015 proof of prop-pod-dual-tate-data-compatibility, especially Steps 1-2. The unit's strict-Weil-object route is unchanged; this item supplies the exact automorphism internal-Hom tool that those two blueprint steps had left implicit. There is no blueprint_update or released repair note for this item. No SGA source is used.

For source checking I read Stacks sites-modules.tex at 03EL (lemma-tensor-product-pullback), 0GMX (remark-pullback-internal-hom), and 0GN2 (lemma-pullback-internal-hom), and sites-cohomology.tex at 0A8X (section-hom-complexes), 0A95 (lemma-RHom-well-defined), and 08J7 (section-internal-hom). I compared those places with the statements of all cited nodes. The overall proof is marked agent-written: these sources anchor the construction, but none states all the required normalizations in one theorem. There are no new nodes needing a separate source review.

Step 1 uses clause 1 of lem-weil-proetale-isomorphism-inverse-image for the section formula and the site equivalence, and def-weil-sheaf-of-modules-category for action and linearity. I explicitly put the original action on reindexed sections and check reverse reindexing on actions. This is why applying the statement's constant-module clause to the completed nonconstant sheaf is unnecessary.

Step 2 uses the just-constructed inverse equivalence to prove preservation of arbitrary small cones and cocones by their Hom bijections. The module category definition supplies the abelian category; def-weil-abstract-derived-category supplies kernel/image cohomology and quasi-isomorphisms. Both directions are exact. Infinite products are preserved as limits; they are never assumed exact.

Step 3 uses clause 3 of the same isomorphism-inverse-image node, which really does state naturality for every ring homomorphism, hence the finite quotient maps. def-weil-completed-integral-coefficients gives the completed sheaf as the ring limit, and def-pur-sheaf-inverse-limit explicitly applies also to rings. I check each projection of the completed identification and each projection of both inverse composites, and then check that their scalar-action transports cancel. No interchange with a derived inverse limit occurs.

Step 4 uses lem-pur-isomorphism-inverse-image-tensor-hom, whose statement applies to an arbitrary commutative ring sheaf, gives both comparisons, their section normalizations and joint naturality. The finite and completed cases meet its hypotheses. def-pc-flat-sheaf-modules defines flatness as exactness of tensor, so applying reverse exact reindexing to a test exact sequence proves preservation in a few lines.

Step 5 uses the exact direct-sum total and its two signed differential terms from def-pc-tensor-complex-sheaves, together with def-pc-kflat-complex. I check the actual tensor differential and use the arbitrary acyclic test complex C through GC; no boundedness or flatness of individual terms is smuggled into K-flatness. The reverse argument gives reflection.

Step 6 uses exactly the global null-homotopy definition in def-pur-kinjective-complex. Given a map C to FI, I transfer it to GC to I, apply the defining null-homotopy, and transfer the equation back degree by degree. Thus no unproved assertion about restrictions of K-injectives to slice sites enters this step.

Steps 7-8 use the product term and signed differential of def-pur-hom-complex and the normalized sheaf-Hom comparison already cited in Step 4. I check the p-th projection for every integer p, including the sign (-1)^r, and the equation F(bfa)=Fb Ff Fa. These prove an isomorphism of actual unbounded complexes with joint naturality, not just separate cohomology isomorphisms.

Step 9 uses the full statement of lem-pur-rhom-well-defined: its source change is an arbitrary quasi-isomorphism, but its target change is between K-injectives. Step 6 supplies that hypothesis after reindexing. I do not assert quasi-isomorphism invariance of raw Hom(K,-) on arbitrary second-variable complexes.

Step 10 uses prop-pur-kinjective-resolutions-exist, which states existence on a site small in the chosen universe, and def-pur-derived-internal-hom, which states the model, its functorial descent and canonical independence of representatives. The small pro-etale convention of the item supplies the size hypothesis; products and diagrams stay in that fixed convention. Step 9 verifies the needed quasi-isomorphism compatibility, while def-weil-abstract-derived-category supplies the localization property. Thus the construction is natural on derived morphisms, including inverses of quasi-isomorphisms.

Step 11 checks the termwise unit/counit chain-map equations and triangle identities, as well as the shift differential -F(d), directly. The finite-level clause of def-weil-derived-pullback-tensor-hom specifies the same inverse-image functor and canonical coefficient action. Its integral quotient-tower construction is not used as a substitute for this ordinary completed-ring equivalence.

I checked delivery-errors B-E as mathematics, not just as JSON syntax. No elementary fact has been turned into a new node and no clause has merely been renamed. Every proof citation is to a statement read above, never to information available only in its proof. citations.json quotes literal substrings (in several cases the entire relevant statement to include all used clauses). All proof dependencies equal the union of the uses, and a reachability check found no cited node depending on this item. The four generic off-unit statement tools are explicitly declared in split_report.tool_uses; they do not change the unit route. Every step is below 2000 characters, and each is a direct calculation, universal-property application, or application of an existing cited theorem.

Edge cases checked: g=id gives identity coefficient maps and Hom comparisons; reverse g cancels on all coefficient projections and actions. Zero modules and the empty scheme give the zero-module case of every construction. The tower begins at n=1, and n=1 requires no division by the uniformizer. Unbounded complexes with nonzero terms in every degree still use the full integer product in Hom and the full direct sum in tensor. Negative r gives the same parity sign and differential identity. Arbitrary schemes are allowed: no noetherianity, constructibility, finite Tor dimension, perfectness or boundedness was added. ℓ-invertibility is retained from the statement but the reindexing argument itself needs only the site isomorphism.

The actual Mathlib search log contains two semantic phrasings, two Loogle searches, two source greps, and one LeanSearch search. I read the returned Mathlib sites-equivalence, exact-derived-functor, and KInjective declarations. They provide useful infrastructure but not a one-line specialization proving this entire item. All services used for these searches returned results; none was silently treated as a negative answer after failure. The old item search entries are retained as inherited metadata and are distinguished from this sandbox's logged searches.

The server review_split check has passed with zero new nodes and the declared tool uses. The full delivery dry run is the next required check.
