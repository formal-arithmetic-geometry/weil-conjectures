# Stage-1 delivery: lem-sfb-free-representable-derived-functions-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-free-representable-derived-functions-model.json`: statement node, now split; nine proof steps, no new nodes and no new Mathlib leaves. The statement is unchanged. Added the existing definitions of module-presheaf sheafification and localized ringed sites to `stmt_deps`.
- `citations.json`: a verbatim statement quotation for each step/node citation.
- `searches.jsonl`: the prescribed search command's actual log; existing item searches and citations were retained. `prepare_split.py` is a sandbox-only authoring aid and is not a DAG delivery file.

## Attachments

None. I searched the read clone's `lean/WeilConjectures/` for the exact blueprint tag and for free representables, freeYoneda, derived functions, and internal Hom. The free-Yoneda, resolution-cohomology and specialized pro-etale internal-Hom declarations do not state this arbitrary-ring-sheaf derived-presheaf comparison with its parameter and coefficient normalization. No attachment is claimed.

## WANTED

None. All source material used is present locally.

## Problems found and changes made

The imported item had no proof. Its statement is valid, including for nonflat coefficient rings: the correct intermediate fact is that the underlying abelian sheaf of an injective module is evaluation-acyclic on every object. It need not be injective. I retained the statement and supplied this argument rather than assuming preservation of injectives. The resulting comparison is an isomorphism in the derived category, not just a list of degreewise isomorphisms.

The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor` explicitly returns `None`. I retained that value and the complete existing `via` chain; its place already describes the profinite-functions continuity input to paragraph (3). This is a supporting tool node, not the key statement of `sk-thm-sf-ctf-stability`, so no unit realization record is changed. Blueprint searches for “free representable”, “representable derived”, “sheafified derived”, “derived sections”, “internal Hom” and “03FD” found no node stating the item. The existing general acyclicity and arbitrary-ringed-site module acyclicity nodes are reused.

During source checking I corrected a draft reference for uniqueness of resolution lifts: it is Stacks Tag 013S, `lemma-morphisms-equal-up-to-homotopy`; 013M is an equation, not that lemma. This was a citation correction in my draft, not a statement correction.

## Mathlib searches

I ran LeanFinder twice with different formulations, Loogle for `"freeYoneda"`, LeanSearch, and the recorded source grep through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`. The actual returned results are stored in `searches.jsonl` and appended to the item without modifying the earlier search records. All services returned successfully. The relevant hits were `PresheafOfModules.freeYonedaEquiv`, `CategoryTheory.Sheaf.freeYonedaHomEquiv`, module-sheafification adjunctions, and `LightCondensed.ihomPoints`. I read their local Mathlib sources in `Algebra/Category/ModuleCat/Presheaf/Generator.lean`, `CategoryTheory/Generator/Sheaf.lean`, and `Condensed/Light/InternallyProjective.lean`. They supply underived adjunctions; the light-condensed result also has a specialized site and constant coefficient ring. None is the derived statement of the item. Existing DAG Mathlib leaves already cover the underived free-generator adjunction, exact sheafification, exact evaluation, and exact-functor localization, so no new leaf is needed.

## Not duplicates

No new nodes. In particular the arbitrary-ringed-site theorem is already `lem-sc-injective-module-abelian-acyclic-zariski`, despite its id suffix; I read its statement and used it instead of creating another Tag 03FD node. `lem-weil-pbc-injective-module-abelian-acyclic` is only for a small etale site with constant coefficients and would not justify this item. `lem-trf-site-free-sheaf-sections` has abelian coefficients rather than an arbitrary ring sheaf, so I use the existing module presheaf free-Yoneda node and the module sheafification adjunction on the slice. `lem-sfb-derived-internal-hom-sections-model` concerns global derived sections of a general internal Hom and is not this presheaf-valued derived-inclusion comparison; it is not used to hide the item's argument.

## Review by NU

I read the item's sources in `sites-cohomology.tex`: Tag 08J7 (`section-internal-hom`) and, especially, the complete statement and proof of Tag 03FD (`lemma-cohomology-modules-abelian-agree`). The latter proves precisely the needed vanishing for underlying abelian sheaves of module injectives. I also read `sites-modules.tex` Tag 03EM, the module sheafification adjunction of 03CY, the ringed localization definition 04IX and its extension-by-zero/free-generator description, and exact forgetting in 03DA. For the homological passage I read `derived.tex` Tags 013K, 013P, 013S, 015E, 015F and 05TI. These establish resolution existence, lifting and its uniqueness, acyclic-complex computation and exact termwise derivation. The combined derived-presheaf statement is an agent argument assembled from these sources, and `proof_origin.by` is `agent`. There are no new node sources to audit.

Step 1 uses the actual statements of `lem-weil-pbc-ring-sheaves-grothendieck`, `lem-sp-grothendieck-enough-injectives`, `lem-weil-pbc-site-sheaves-enough-injectives` and `lem-weil-pbc-complex-injective-resolution-mono`. I checked smallness in the module universe, including the slice categories. To meet the acyclicity theorem's hypotheses on both abelian categories, presheaf enough-injectives is obtained by applying the existing site theorem to the trivial topology. The resolution-existence node supplies degreewise monomorphisms and the lower bound zero, exactly what the later strict lifting argument requires. These are general ringed-site and homological tools, not replacements of the geometric unit's route.

Step 2 uses `def-pur-localized-ringed-site` for the actual restriction formula and `lem-weil-pbc-module-sheafification-restriction` for the unit-preserving sheafification comparison. I checked continuity and cocontinuity of the slice forgetful functor directly: coverings lift with the same members, carrying their composite maps to V. Thus the cited theorem is applicable. The remaining identification is just the product universal property on each object of the slice, with basis elements explicitly matched, not an additional hidden lemma.

Step 3 uses `def-pur-sheaf-hom`, `def-weil-presheaf-modules-sheafification`, `lem-weil-pbc-free-yoneda-presheaf-module` and `def-weil-pbc-sheafification`. I checked that the free-Yoneda theorem allows an arbitrary presheaf of rings and therefore applies to R restricted to the slice. Its inverse is explicitly the restriction of s along (a,b), so it gives every required section and not merely full faithfulness of Yoneda. The formulas prove additivity and the V, M and P squares. They also fix the actual generator normalization, including the coefficient action for a nonconstant R.

Step 4 cites `lem-weil-pbc-module-sheaves-colimits-forgetful`, `lem-weil-pbc-sheafification-exact`, `lem-weil-pbc-abelian-presheaves-evaluation-exact`, `lem-weil-pbc-exact-functor-derived-factorization`, the definitions of sheaf Hom and the module-sheaf category, and `lem-weil-pbc-right-derived-plus-injective`. Their statements supply exact U and a, pointwise exactness for t_P, sectionwise kernels, and the actual derived-object computation on bounded-below injectives. H_P is left exact by the slice-Hom kernel formula. No projectivity of P is inferred.

Step 5 uses the right-derived-injective model, exact presheaf evaluation, the definition of object cohomology, and `lem-sc-injective-module-abelian-acyclic-zariski`. I verified the last node's statement is for any ringed site, any ring sheaf and every object W. The equality of derived-inclusion cohomology evaluated at W with H^q(W,A) follows on the same injective resolution and from exact evaluation. Consequently the presheaf vanishes object by object. No hypothesis on finite coverings, cohomological dimension, coefficient flatness or discreteness enters.

Step 6 applies `sk-thm-acyclicity` to the bounded-below complex UI_M and the left exact additive inclusion iota. I checked both enough-injectives hypotheses in step 1, exact U in step 4, and acyclicity in step 5. The cited statement gives an isomorphism in D^+, rather than only its cohomology. The natural comparison alpha is supplied by `lem-weil-pbc-right-derived-plus-injective`; composing with the inverse of derived U(r_M) fixes its normalization.

Step 7 is the explicit composite: apply step 3 to each degree, then apply the exact termwise functors to the isomorphism of step 6. `lem-weil-pbc-exact-functor-derived-factorization` and `lem-weil-pbc-right-derived-plus-injective` justify the two derived representatives. Naturality for the differentials is already proved in step 3, so no unidentified complex comparison is assumed.

Step 8 uses `lem-weil-pbc-lift-along-injective-quasi-iso`, `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` and the natural comparison in `lem-weil-pbc-right-derived-plus-injective`. Their statements give a strict augmented lift and homotopy independence, with no projective source assumption. I checked its target is bounded below and termwise injective, and its source augmentation is degreewise monomorphic. The displayed equation for c_N and c_M proves the required coefficient square at the derived-object level; applying the same equation to identity maps proves independence of resolutions.

Step 9 uses the already explicit parameter formulas, the definitions of sheaf Hom and injective resolution, exact sheafification and evaluation, and the derived localization definition. The same resolution is used for all P, and the map P' to P induces restriction in the correct direction along V times P' to V times P. Computing the zeroth kernels gives precisely the free-generator evaluation of step 3. Finally any functor D^+ to D preserves the resulting isomorphism and commuting squares; no claim about resolving an arbitrary unbounded input is needed.

I checked edge cases: the zero ring and zero module make all complexes zero; for terminal P the free module is R and the comparison reduces to a R iota(UM) representing UM; on a site with trivial topology it is the ordinary exact presheaf product-precomposition calculation. If P is an initial object admitting an empty covering, M(V times P)=0 whenever that product is sheaf-theoretically empty, in agreement with the free-generator Hom. The argument also works when R is not flat over the integer sheaf: step 5 explicitly avoids the invalid inference that U preserves injectives.

Against delivery-errors B–E, all non-elementary inputs are existing cited statements; the item carries the construction and its naturality rather than delegating them to a new restatement. Every step's cited statement was opened, and `citations.json` contains literal excerpts from those statements. There are no new unsplit statements to test or duplicate tag pairs. All nine steps are below 2000 characters; none contains an omitted standard comparison. No SGA source or forbidden route is used. The repository and launcher were only read; all authored files are in this sandbox and no Lean or compiler was used.

## Unfinished work and validation

Nothing mathematical remains in this split. Server `review_split` passed: 0 new nodes; the inherited unit has no realization recorded yet. The required delivery dry run and push follow this report.
