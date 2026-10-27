## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-ringed-topos-pullback-exact.json`: item split in four steps, statement unchanged; searched Mathlib, no matching declaration.
- No new nodes; no Mathlib leaves.
- `citations.json`: one verbatim statement quote for each use in each step.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and for flat/pullback/exact and flat/ringed combinations. The pro-etale module-object and fixed-coefficient exact pullbacks are narrower, and PullbackFlat.lean concerns preservation of flat sheaves, rather than exactness of tensor pullback for a variable target ring sheaf. Also read the adjacent `lean/Sheaf/` geometric inverse-image and ringed-flat-module interfaces. The latter concerns preservation of flatness, a different assertion.

## WANTED

None. All sources used are available locally.

## Findings and changes

The imported statement is correct and agrees with the second assertion of Stacks 04JC, `sites-modules.tex`, label `lemma-flat-pullback-exact`. Its source's flat-ring-map terminology is exactly flatness of the target ring as a module over the inverse-image ring. There is no statement dispute. The item previously had no proof.

I read the latest blueprint (ef6f9619, `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`) as well as the recorded chapter and unit. The lemma is a generic module-sheaf tool below the groupoid kernel/cokernel step of the existing ancestry; it replaces no unit-level argument. The inherited blueprint ancestry has `from.node: null`; `tools/blueprint_refs.py ancestor` likewise returns None. I retained the full inherited place/via chain rather than inventing an ancestor or altering other nodes. Searches of the whole blueprint for `04JC` and `flat morphism of ringed topoi` found no imported statement. The broad inverse-image search led to the existing general inverse-image node, which I reused.

The only extra proof tools are `lem-trf-geometric-inverse-image-exact` and `lem-weil-pbc-module-sheaves-colimits-forgetful`, declared in `split_report.tool_uses`. The first supplies the exact transported inverse image for arbitrary geometric morphisms; the second supplies exact scalar forgetting on arbitrary small sites. Neither is replaced by a special site presentation or by fixed coefficient rings. The closures of these two nodes (132 and 63 nodes in the read snapshot) do not contain the item.

Six fresh searches ran through the required msearch command and are recorded verbatim in searches.jsonl and the item's mathlib_searches: LeanFinder in two phrasings, Loogle, LeanSearch, and two grep queries. All services answered. I inspected the candidates in Mathlib `CategoryTheory/Sites/Pullback.lean:105-121`, `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:43-65`, and `Algebra/Category/ModuleCat/Descent.lean:42-46`. The first requires an inducing site functor; the second constructs such a pullback without the asserted flat exactness; the third concerns ordinary rings. None is an attachment or one-line specialization of this item.

## Review by Q48

I checked the item directly against Stacks 04JC, including both paragraphs of its proof. Its first paragraph is precisely the generic inverse-image input already provided by `lem-trf-geometric-inverse-image-exact`, whose statement I opened in full. Its second paragraph factors tensor pullback into inverse image and exact tensor. I also read Stacks 03ER (`definition-flat`, item (3)), 03DA (`lemma-abelian`), and 03DB (`lemma-limits-colimits`) and the statements of all six cited nodes. No new node needs a source review.

Step 1 uses `def-weil-pbc-ringed-topos-morphism` only for the finite-limit-preserving set-sheaf adjunction, and `lem-trf-geometric-inverse-image-exact` for its explicitly stated variable-ring module inverse image. Swapping the names of the two sites in that node gives exactly Mod(B) to Mod(f^{-1}B). It imposes no site-functor or constant-ring hypothesis. Additivity is explained by the transported addition diagram; no exactness of a non-flat extension of scalars is asserted here.

Step 2 uses the exact functor in `def-pc-flat-sheaf-modules` literally. This is not stalkwise flatness or a module over a section ring. The sheaf tensor and change-of-rings construction are in `def-pur-sheaf-tensor-product`. The flip between scalar-last and scalar-first tensor is written on pure tensors, checked against balancing, and inverted by the same formula. Thus this is an elementary identification, not a new theorem hidden behind a citation. Bilinearity also gives the displayed additivity equation. This keeps the A-action on the correct factor.

Step 3 uses clause (1) of `lem-weil-pbc-module-sheaves-colimits-forgetful`, which explicitly preserves kernels and cokernels, for both ring sheaves on the same site. Its sheafification hypothesis is satisfied because the site is small relative to the module universe; no colimit indexed by an oversized category is used. The comparison maps become isomorphisms after forgetting scalars because the underlying tensor is the exact functor of step 2. I wrote the equation proving that the inverse of an underlying isomorphism is A-linear, so reflection of isomorphisms is not an uncited assumption. This establishes exactness in Mod(A), not just in Mod(f^{-1}B).

Step 4 composes the two proved kernel and cokernel comparisons. The abelian category assertion needed here is explicitly in `def-weil-sheaf-of-modules-category`. In an abelian category a short exact pair is a kernel/cokernel pair, so the last sentence is elementary and supplies the requested short-exact clause in addition to the two preservation clauses.

For B1-B9 and C1-C5 I checked that no unnecessary new statement or restatement was introduced, every use has a verbatim statement quote, and the statement dependencies remain unchanged. For D1-D5 the four steps carry the full argument rather than moving a clause into a new node. Every step is shorter than 700 characters; none hides an argument over the 2000-character threshold. For E1-E6 I checked small sites, commutative ring sheaves, the exact flatness hypothesis, the two different module categories, and the absence of a presenting-site-functor requirement.

Small cases: identity geometric morphism with A=B gives the identity functor; a zero target ring gives the exact zero functor; empty sites and zero modules cause no exception; no nonempty-site or nonzero-ring hypothesis enters. On the point site the proof reduces to ordinary flat scalar extension. Dropping flatness would fail for Z to Z/2, since tensoring the injection Z --2--> Z then has zero map on Z/2; hence the hypothesis is being used in the right place. No faithful-flatness, enough-points, or sectionwise-flatness assumption was added. No statement correction was necessary.

## Unfinished work

None in the mathematical split. Validation and delivery are performed with the required server-side tools; no Lean, compiler, Lake or global-build command was run.
