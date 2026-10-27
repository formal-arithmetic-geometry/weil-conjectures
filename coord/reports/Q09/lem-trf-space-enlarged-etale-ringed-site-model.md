# Stage-1 repair: Q09

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-space-enlarged-etale-ringed-site-model.json`: existing statement retained exactly; four-step assembly, 2106 characters.
- `dag/nodes/sec-trace-formula/lem-trf-space-enlarged-site-scheme-density.json`: statement, unsplit; no Mathlib match; old steps 1–3.
- `dag/nodes/sec-trace-formula/lem-trf-space-enlarged-atlas-algebraic-extension.json`: statement, unsplit; no Mathlib match; old steps 4–5.
- `dag/nodes/sec-trace-formula/lem-trf-space-enlarged-chart-ringed-morphism.json`: statement, unsplit; no Mathlib match; old steps 6–7.
- `dag/nodes/sec-trace-formula/lem-trf-space-enlarged-ringed-composition-localization.json`: statement, unsplit; no Mathlib match; old steps 8–10.
- `citations.json`: verbatim statement excerpts for all five step/node pairs.
- `searches.jsonl`: actual msearch log retained; rate-limited LeanSearch recorded as unavailable.

## Attachments

None. The whole `lean/WeilConjectures` tree has no match for the item tag or enlargedRestriction/enlargedStructuralMap. The existing `lean/Sheaf/AlgebraicGeometry/EnlargedEtaleRingedSite.lean` is reference material: theorem enlargedRestriction_equivalence (145–148), enlargedModuleRestriction_equivalence (184–186), enlargedExtension_equalizer (215–225), and the geometric, structural, composition and localization theorems still contain `sorry`. The new nodes introduce no duplicate Lean definitions or modules. Existing declarations remain owned by the parent; stage 1 does not edit Lean or maintainer metadata.

## WANTED

None: the Stacks TeX sources used below are present and were read.

## What was wrong and what changed

The return requires spreading the 9743-character proof across at least three comparable new nodes, with a parent proof of at most 3000 characters. I extracted four work packages, carrying respectively 2661, 2055, 2286 and 2741 characters of old argument. None restates the whole item. The first exposes the site axioms and five comparison conditions; the second exposes normalized atlas descent and operation transport; the third exposes the finite-limit base-change criterion and a unique chart-normalized ring map; the fourth exposes projection-normalized ringed composition and the site/ring/topos localization identifications. These stronger intermediate interfaces retain the work behind the item's clauses. The new nodes are statement-only and unsplit, so their proofs can be assigned separately. No statement is weakened, no new representability assumption is imposed, and no chapter or unit route is changed.

The sandbox initially contained only dispatcher `.brief*` markers, not the claimed previous report or searches. I copied the current returned node from the read-only repository, retained all its fields, inherited searches and citations, and reconstructed the report from that ten-step proof. No old sandbox proof/report/search file was overwritten. The live returned node already records its former delivery and review. The comparison with current main uses that exact file as the baseline; deliver.py overlays only worker-owned fields on the server's current base.

## Search and duplicate audit

Searched the full DAG by the Stacks tags 03G0, 03G1, 03H7, 03G2, 03G7, 03G8, 03LP, 04LY and 04LZ and by the new ids and enlarged-site, chart-equalizer and density concepts. Searched the entire imported blueprint with blueprint_refs.py for enlarged, scheme charts, scheme density, algebraic extension, etale ringed, ringed morphism, ringed composition, localization morphism and the individual source tags. None states these interfaces. The unrelated field-extension hits and general projection-formula-map hit do not state them. The ancestor remains lem-trf-local-term-locality with the inherited historical route through section-algebra base change; each new `via` prepends this item. Read the current main-20261015 ancestor proof and the recorded unit/chapter; this work expands an existing generic ringed-site input and does not replace a unit argument.

Every new node has its own semantic query, Loogle pattern and Mathlib grep. A second phrasing was tried with LeanSearch; when the extension query was rate limited, another LeanFinder phrasing ran successfully. Read all returned hits. General dense-subsite tools `Functor.sheafInducedTopologyEquivOfIsCoverDense` (Mathlib/CategoryTheory/Sites/DenseSubsite/InducedTopology.lean:159) and `IsDenseSubsite.sheafEquiv` (DenseSubsite/Basic.lean:797) assume the geometric hypotheses of the first node. They do not prove them. Read their source and the presheaf over-category source returned by Loogle: that source is about presheaves over a presheaf, without an etale topology, algebraic spaces or structural rings. The semantic hits for the other nodes are scheme etale sites, Zariski gluing, ringed spaces and topological equalizers. None is an exact match or a one-line specialization for these full interfaces. Four new nodes, zero Mathlib leaves.

## Not duplicates

- lem-trf-space-enlarged-site-scheme-density vs lem-trf-space-enlarged-etale-ringed-site-model: This is one of four explicitly requested proper subarguments of the returned parent; the other three packages are also necessary. The parent retains only their short assembly.
- lem-trf-space-enlarged-site-scheme-density vs lem-trf-space-chartwise-etale-permanence: That node proves geometric permanence and cover axioms for chartwise etale morphisms, not the enlarged site comparison, canonical ringed morphism or ringed localization.
- lem-trf-space-enlarged-site-scheme-density vs def-trf-scheme-algebraic-space: That node defines a scheme as its representable fppf sheaf. It does not prove the site axioms, scheme-density conditions or sheaf comparison for an arbitrary algebraic space.
- lem-trf-space-enlarged-atlas-algebraic-extension vs def-trf-space-etale-module-functors: That node specifies small-etale module direct image by a chart-limit universal property and tensor pullback. It does not establish the enlarged-site comparison, normalized extension, chart ring-map descent or composition/localization interfaces here.
- lem-trf-space-enlarged-atlas-algebraic-extension vs def-trf-space-line-module-proj-input: That definition concerns cartesian scheme realizations of line modules and homogeneous maps for Proj, not extension of arbitrary sheaves of sets/rings/modules to the enlarged etale site.
- lem-trf-space-enlarged-atlas-algebraic-extension vs lem-trf-space-enlarged-etale-ringed-site-model: This is one of four explicitly requested proper subarguments of the returned parent; the other three packages are also necessary. The parent retains only their short assembly.
- lem-trf-space-enlarged-atlas-algebraic-extension vs def-trf-space-module-scheme-restriction: That definition restricts a small-etale module to Zariski opens of a scheme test. It does not establish extension to algebraic-space objects or an equivalence of enlarged-site module categories.
- lem-trf-space-enlarged-atlas-algebraic-extension vs def-trf-algebraic-space: That definition supplies an algebraic space and its small-etale structure sheaf. It does not prove atlas equalizer extension or the ring/module restriction equivalences.
- lem-trf-space-enlarged-chart-ringed-morphism vs def-trf-space-etale-module-functors: That node specifies small-etale module direct image by a chart-limit universal property and tensor pullback. It does not establish the enlarged-site comparison, normalized extension, chart ring-map descent or composition/localization interfaces here.
- lem-trf-space-enlarged-chart-ringed-morphism vs lem-trf-space-enlarged-etale-ringed-site-model: This is one of four explicitly requested proper subarguments of the returned parent; the other three packages are also necessary. The parent retains only their short assembly.
- lem-trf-space-enlarged-ringed-composition-localization vs def-trf-space-etale-module-functors: That node specifies small-etale module direct image by a chart-limit universal property and tensor pullback. It does not establish the enlarged-site comparison, normalized extension, chart ring-map descent or composition/localization interfaces here.
- lem-trf-space-enlarged-ringed-composition-localization vs lem-trf-space-enlarged-etale-ringed-site-model: This is one of four explicitly requested proper subarguments of the returned parent; the other three packages are also necessary. The parent retains only their short assembly.

## Review by Q09

I read Stacks spaces-properties.tex at definition-spaces-etale-site (03G0), lemma-compare-etale-sites (03G1), remark-explain-equivalence (03H7), lemma-functoriality-etale-site (03G2), definition-structure-sheaf (03G7), lemma-morphism-ringed-topoi (03G8), lemma-etale-morphism-topoi (03LP), and equation-localize / equation-localize-ringed (04LY / 04LZ). These are the source of the item and, respectively, the four groups of old steps listed below. The ring/module lifting and ring-map composition checks expand the source's omitted checks; their full old arguments remain below rather than being hidden behind 'standard'.

Assembly step 1 uses the exact finite-limits, five-condition and restriction-equivalence conclusions of the scheme-density node. It does not use merely a definition of density. Step 2 uses the extension node's normalized uniqueness, atlas equalizer naturality and ring/module conclusions. Step 3 uses that extension node for the actual rings and then the chart-ringed-morphism node for continuity, the left exact adjoint, the canonical small-topos identification and the normalized ring map. Step 4 uses the composition/localization node's entire comparison, including the structural ring map; equality of underlying topoi alone would not suffice. All these hypotheses are exactly those of the unchanged parent: arbitrary base scheme, arbitrary algebraic spaces and arbitrary morphisms, except for the explicit etaleness of the localization map. Every cited statement was read; citations.json contains the actual verbatim sentences used. No assembly step introduces an uncited non-elementary fact.

I also opened the statements of every dependency of the old proof. Chartwise-etale-permanence supplies composition, arbitrary base change, cancellation and cover axioms for possibly nonrepresentable etale arrows. Fibre-products-etale-covers supplies existence of space fibre products and scheme overlaps for representable scheme charts; I do not take its representable-cover wording as a claim that all etale space maps are representable. The special-cocontinuous definition gives all five conditions and the comparison theorem explicitly gives restriction in the required direction. Yoneda's node is the full Hom-to-sections bijection, not only full faithfulness. Algebraic-structures-objects states sectionwise products and ring/group objects. The left-exact-site criterion assumes finite limits and smallness, supplied here by the first package and the stated universes. Site-morphism-composition supplies the adjunction-normalized comparison; slice-subtopos-site-presentation states the product-evaluation direct image and restriction inverse image. These generic tools remain available to the future workers; their exact uses are retained with each old step below. They are not falsely listed as proved facts inside a new statement-only node.

I checked B–E of delivery-errors point by point against the sources. Each new statement introduces all its spaces, sites, rings and maps and cites its notions; it has no proof steps, proof dependencies, proof sketch or hollow construction. Source places give Stacks tags and TeX labels. The parent is unchanged and the new packages are not synonyms or a transfer of the whole result to one node. Repeated source tags are distinguished above. The statement-only interfaces preserve every old argument, including the finite-limit equalizers, scheme cover refinements, uniqueness relative to a specified restriction isomorphism, common refinements, lifted operations, semilinearity, ring-map adjunction and associativity checks.

For edge cases, if X is a scheme the identity chart gives the ordinary site comparison and equalizer. If X is empty, the empty covering enforces the unique section of a set sheaf (and the zero ring/module values); no nonempty-chart hypothesis was inserted. Atlas refinements may be arbitrarily many within the fixed small universe. No quasi-compactness, separatedness, affine atlas, representability of arbitrary f, or noetherian hypothesis is used. For f or u an identity the formulas yield identity comparisons. For an etale nonrepresentable u, cancellation is chartwise and no claim is made that every fibre product with a scheme test is a scheme; only representable scheme-atlas overlaps have that property. Normalized ring identifications are required, so an arbitrary automorphism of a structure-ring extension is not silently used.

The retained old step texts have lengths below 2000 characters each. The parent's new steps are also below 2000 and total below 3000. New statement lengths are not proof lengths: their proofs are deliberately empty. The prior long argument is preserved verbatim in the allocation below. No SGA source is used.

Repair recheck against immutable returned head 884bb858092: I read the returned and current statements of all twelve existing dependencies of the five delivery nodes. They are identical at server head d73b0bc8e7c21be4dfc082187b3bb7c16e5895b7; the local read snapshot agrees with that server tree. The four new statements also agree with the returned head and remain absent from current main. I re-read all four new statements and the five citation excerpts, and the Stacks source places listed above. In step 4 I now explicitly apply the composition/localization node's identity comparisons, unit laws and associativity for three maps, including ring maps. The normalization hypotheses come from step 3's chart-ringed-morphism statement; no representability assumption on the arbitrary maps is introduced. This is a concrete assembly change from the returned head. The parent statement and all four prerequisite statements are unchanged; the retained searches still answer the same questions.

Landing-return repair recheck, 2026-10-23: the initial required dry run passed at c7a6b8c0a9c. I compared all twelve existing dependency records with the saved current/returned-head comparison; the read snapshot has no changes to those records, so no changed cited statement requires a replacement. All four new prerequisites remain absent there. I read their complete statements, the five verbatim citation excerpts, and Stacks spaces-properties.tex at 03G0/03G1/03H7, 03G2, 03G7/03G8, 03LP and 04LY/04LZ again. The smallness hypotheses, chartwise etaleness, representable scheme charts, arbitrary base-change morphisms, and the extra etaleness hypothesis only for localization still match. In assembly steps 2 and 3 I now fix one normalized structure-ring extension for each space and reuse it for all maps. Thus the composable pair and identity maps in step 4 use the same rings and identifications: the chart-ringed-morphism node supplies exactly the normalization assumed by the composition/localization node. This is a concrete repair of the retained assembly, beyond rebasing. The item statement, four prerequisite statements, preserved old arguments, sources, citations and logged searches are retained. No search question changed, so I reused the logged results rather than repeating them. The final dry run and push use deliver.py's current-DAG overlay and preserve all maintainer fields.

## Preserved arguments for the four parallel work packages

This section preserves every old argument verbatim, with its old citation list and source. These are handoff material, not proof fields of the new statement-only nodes. References to 'step n' are to these old step numbers. Later workers can cite the other packages when a prior step supplies an input.

### lem-trf-space-enlarged-site-scheme-density

Source: literature/stacks-project/spaces-properties.tex; Tags 03G0 (definition-spaces-etale-site), 03G1 (lemma-compare-etale-sites); finite limits in Tag 03G2 (lemma-functoriality-etale-site), proof; chartwise convention Tag 03FR (definition-etale).

Old step 1 (740 characters):

Use the chartwise etale notion explicitly specified in the statement, as in [lem-trf-space-chartwise-etale-permanence]. That node supplies composition, arbitrary base change, cancellation between objects etale over the same base, and the etale-covering axioms. It also states agreement with representable etaleness when the source is a scheme. Consequently any scheme chart followed by a chartwise etale map is still a representable etale scheme map. This last observation is essential: it makes scheme charts into objects of $X_{\mathrm{et}}$, without assuming that all etale maps between spaces are representable. The existence of a surjective representable etale scheme chart for every space is exactly part of [def-trf-algebraic-space].

Cites: lem-trf-space-chartwise-etale-permanence, def-trf-algebraic-space.
Source: literature/stacks-project/spaces-properties.tex; Tag 03FR (definition-etale), Tags 03FT, 03FU, 03FV; the convention needed in Tag 03G0 (definition-spaces-etale-site)

Old step 2 (843 characters):

The terminal object of $\mathcal C_X$ is $X/X$. Pullbacks are the space fibre products of [lem-trf-space-fibre-products-etale-covers]; their projections and structure maps are etale by step 1. Binary products are pullbacks over $X$ and equalizers are pullbacks of diagonals, so $\mathcal C_X$ has finite limits. The identity, composite-cover and base-change-cover axioms are the etale-covering assertions of [lem-trf-space-chartwise-etale-permanence]. Thus this is a site as in [def-weil-pbc-sites-and-cohomology]. Choose the small representatives and covering families in [def-weil-size-convention], including scheme covers, and carry all identifications across these representatives. The scheme-object subcategory has the same coverings as $X_{\mathrm{et}}$: a map between its objects is etale by step 1, and joint surjectivity is unchanged.

Cites: lem-trf-space-fibre-products-etale-covers, def-weil-pbc-sites-and-cohomology, def-weil-size-convention, lem-trf-space-chartwise-etale-permanence.
Source: literature/stacks-project/spaces-properties.tex; Tag 03G0 (definition-spaces-etale-site), and Tag 03G2 (lemma-functoriality-etale-site), proof of finite limits

Old step 3 (1078 characters):

Let $i:X_{\mathrm{et}}\to\mathcal C_X$ be the inclusion. It is fully faithful: the Yoneda bijection [lem-galois-yoneda-hom-bijection] identifies maps between the representing scheme sheaves with scheme maps, also in the over category. It preserves covers and covering pullbacks, hence is continuous. To check cocontinuity, start with a cover $\{T_j\to U\}$ of a scheme object. Choose surjective etale scheme charts $W_j\to T_j$ using [def-trf-algebraic-space]. Their composites $W_j\to U$ form a scheme covering refining the given one, by step 1 and surjectivity. Local fullness and local faithfulness hold by full faithfulness, taking identity covers. Finally every $T\in\mathcal C_X$ has a surjective etale scheme chart $T_0\to T$; its composite with $T\to X$ is etale by step 1. These are all five conditions of [def-weil-pbc-special-cocontinuous-functor]. Apply [lem-weil-pbc-special-cocontinuous-sheaf-equivalence]. Its statement explicitly identifies the inverse image with precomposition by $i$, so the equivalence in question is restriction, with the required direction.

Cites: lem-galois-yoneda-hom-bijection, def-trf-algebraic-space, def-weil-pbc-special-cocontinuous-functor, lem-weil-pbc-special-cocontinuous-sheaf-equivalence.
Source: literature/stacks-project/spaces-properties.tex; Tag 03G1 (lemma-compare-etale-sites), using Sites Tag 03A0 (lemma-equivalence)

### lem-trf-space-enlarged-atlas-algebraic-extension

Source: literature/stacks-project/spaces-properties.tex; Tag 03H7 (remark-explain-equivalence); paragraph after Tag 03G7 (definition-structure-sheaf). Transport of ring and module operations expands this comparison using the sectionwise sheaf definitions.

Old step 4 (946 characters):

Choose a quasi-inverse of restriction and its specified restriction isomorphism to define $\widetilde F$. Full faithfulness of restriction gives the unique isomorphism between any two such extensions inducing the identity of $F$. Apply the sheaf equalizer condition of [def-weil-pbc-sites-and-cohomology] to the singleton cover $T_0\to T$. Its overlap $T_0\times_TT_0$ is a scheme by [lem-trf-space-fibre-products-etale-covers], since $T_0\to T$ is representable etale. The two terms therefore identify with $F(T_0)$ and $F(T_0\times_TT_0)$, giving the asserted formula. For a map $T'\to T$, pull this chart back and take a scheme chart of that pullback; the two equalizer maps then describe the restriction. A different chart gives the same restriction after their common refinement. The uniqueness part of the sheaf condition proves agreement and naturality in $T$; maps of sheaves induce maps of the same equalizers, proving naturality in $F$.

Cites: def-weil-pbc-sites-and-cohomology, lem-trf-space-fibre-products-etale-covers.
Source: literature/stacks-project/spaces-properties.tex; Tag 03H7 (remark-explain-equivalence)

Old step 5 (1109 characters):

In particular extend the underlying set sheaf of $\mathcal O_X$ from [def-trf-algebraic-space]. Restriction preserves products and the terminal sheaf, since these are computed sectionwise by [lem-weil-pbc-sheaf-algebraic-structures-objects]. Products of extensions are therefore extensions of products, uniquely by step 3. Lift $+,0,-,\cdot,1$ along the fully faithful restriction equivalence. All ring identities hold because their restrictions hold and restriction is faithful. The cited algebraic-structures node identifies the resulting ring object with a sheaf of rings $\widetilde{\mathcal O}_X$. For a module $M$, lift its addition, zero, inverse and action $\mathcal O_X\times M\to M$ in exactly the same fashion. The module identities and semilinearity are equalities of maps which hold after restriction, hence hold before restriction. By [def-weil-sheaf-of-modules-category] these are module sheaves. Maps lift uniquely and are linear because the action diagram can be tested after restriction. This constructs inverse equivalences on module categories; no exactness or derived assertion is needed.

Cites: def-trf-algebraic-space, lem-weil-pbc-sheaf-algebraic-structures-objects, def-weil-sheaf-of-modules-category.
Source: literature/stacks-project/spaces-properties.tex; Tag 03H7 and paragraph after Tag 03G7 (definition-structure-sheaf); elementary transport of operations along the restriction equivalence

### lem-trf-space-enlarged-chart-ringed-morphism

Source: literature/stacks-project/spaces-properties.tex; Tag 03G2 (lemma-functoriality-etale-site), (1),(3), and Tag 03G8 (lemma-morphism-ringed-topoi), proof; chart descent Tag 03H7 (remark-explain-equivalence).

Old step 6 (955 characters):

For $f:X\to Y$, form $v_f(V)=X\times_YV$ using [lem-trf-space-fibre-products-etale-covers]. Its structure map is etale by step 1. It carries covers to covers by [lem-trf-space-chartwise-etale-permanence], which permits nonrepresentable etale covering arrows. It preserves terminal objects, since $X\times_YY=X$, and preserves pullbacks by the universal property of fibre products; it consequently preserves the finite limits constructed in step 2. The smallness hypotheses are those fixed in [def-weil-size-convention]. Apply [lem-weil-pbc-left-exact-site-inverse-image-tensor] to obtain the geometric morphism with direct image $G\mapsto G\circ v_f$ and left exact inverse image. This also establishes continuity, either by its sheaf-precomposition conclusion or directly from preservation of covering pullbacks. Under step 3's equivalences this is exactly the small etale morphism of topoi constructed by the base-change site presentation in the source.

Cites: lem-trf-space-fibre-products-etale-covers, def-weil-size-convention, lem-weil-pbc-left-exact-site-inverse-image-tensor, lem-trf-space-chartwise-etale-permanence.
Source: literature/stacks-project/spaces-properties.tex; Tag 03G2 (lemma-functoriality-etale-site), clauses (1) and (3), using Sites Tag 00X6 (proposition-get-morphism)

Old step 7 (1331 characters):

We construct the structural map in adjoint form $\widetilde{\mathcal O}_Y\to f_*\widetilde{\mathcal O}_X$. For a scheme object $V\to Y$, take a scheme chart $U\to X\times_YV$. Pullback of regular functions along the scheme map $U\to V$ sends $s\in\Gamma(V,\mathcal O_V)$ to a section on $U$. Its two restrictions to $U\times_{X\times_YV}U$ agree, since the two composites to $V$ agree. Step 4 therefore gives a unique section on $X\times_YV$, independent of the chart: on a common refinement the two constructions are the same scheme pullback. Ring identities and compatibility with maps $V'\to V$ hold after this same chart test. Thus we have a ring-sheaf map on $Y_{\mathrm{et}}$ from $\mathcal O_Y$ to the restriction of $f_*\widetilde{\mathcal O}_X$. Full faithfulness in step 3 lifts it uniquely to the displayed map on $\mathcal C_Y$; step 5 ensures it is a ring map. By the adjunction in [lem-weil-pbc-left-exact-site-inverse-image-tensor], this gives $f^{-1}\widetilde{\mathcal O}_Y\to\widetilde{\mathcal O}_X$, a map of ring objects (the product and unit diagrams are the adjoints of the verified ring diagrams). By [def-weil-pbc-ringed-topos-morphism] this is a morphism of ringed topoi. On every pair of scheme charts it is pullback of regular functions, so it is the canonical structural map specified in the statement.

Cites: def-trf-algebraic-space, lem-weil-pbc-left-exact-site-inverse-image-tensor, def-weil-pbc-ringed-topos-morphism.
Source: literature/stacks-project/spaces-properties.tex; Tag 03G8 (lemma-morphism-ringed-topoi), construction in its proof; Tag 03H7 equalizer descent

### lem-trf-space-enlarged-ringed-composition-localization

Source: literature/stacks-project/spaces-properties.tex; Tag 03G2 (lemma-functoriality-etale-site), (2), and Tag 03G8 (lemma-morphism-ringed-topoi), (1); Tag 03LP (lemma-etale-morphism-topoi), proof; Tags 04LY (equation-localize), 04LZ (equation-localize-ringed).

Old step 8 (1061 characters):

For $W\xrightarrow{g}X\xrightarrow{f}Y$, the universal property gives a natural isomorphism $W\times_X(X\times_YV)\cong W\times_YV$. It commutes with arrows in $V$ because both maps have the same projections. Hence the direct images compose under this isomorphism. The adjunction-compatible inverse-image composition isomorphism is provided by [lem-weil-pbc-site-morphism-composition]. The structural maps agree as well: on scheme charts both composites pull a regular function back along the composite scheme map; the identity $(a\circ b)^\sharp=b^\sharp a^\sharp$ is the definition of composition of scheme morphisms [def-pc-scheme]. Chartwise equality implies equality globally by the equalizers in step 4. The same check for identity maps gives identity functors and identity structural maps. For three maps all associativity comparisons commute: each is the unique fibre-product map with the given projections, and every ring comparison is the same pullback of a regular function. This proves compatibility with composition, including the ringed structure.

Cites: lem-weil-pbc-site-morphism-composition, def-pc-scheme.
Source: literature/stacks-project/spaces-properties.tex; Tag 03G2, clause (2), and Tag 03G8, clause (1); expanded checks omitted in the latter proof

Old step 9 (937 characters):

Let $u:Z'\to Z$ be etale. The functor from $\mathcal C_{Z'}$ sends $T\to Z'$ to $(T\to Z,T\to Z')$; it is well-defined by step 1's composition assertion. Conversely an object of $\mathcal C_Z/Z'$ consists of $T\to Z$ etale and a factorization through $Z'$. Step 1's cancellation assertion makes $T\to Z'$ etale. These two functors are inverse on objects and arrows before taking small representatives, and they preserve exactly the covering families, since both use joint surjectivity of the same underlying arrows. This is the localized site of [def-pur-localized-ringed-site]. For every scheme $T\to Z'$, the restricted extended ring $\widetilde{\mathcal O}_Z|_{Z'}$ and $\mathcal O_{Z'}$ evaluate as $\Gamma(T,\mathcal O_T)$ by [def-trf-algebraic-space], with the same restrictions. The uniqueness of extension from step 3, now over $Z'$, identifies $\widetilde{\mathcal O}_Z|_{Z'}$ with $\widetilde{\mathcal O}_{Z'}$ as ring sheaves.

Cites: def-pur-localized-ringed-site, def-trf-algebraic-space.
Source: literature/stacks-project/spaces-properties.tex; Tags 04LY (equation-localize) and 04LZ (equation-localize-ringed); elementary site identification in the proof of Tag 03LP

Old step 10 (743 characters):

Apply [lem-trf-slice-subtopos-site-presentation] with $\mathcal C=\mathcal C_Z$ and object $Z'\to Z$. The finite limits and size hypotheses were checked in step 2. Its localization direct image evaluates at $V\to Z$ as $G(V\times_ZZ'\to Z')$. Under step 9 this is precisely precomposition by $v_u$, which is the direct image in step 6. The localization inverse image is restriction by the cited statement; uniqueness of the adjoint identifies it with the inverse image for $u$. Its structural ring map is the identification of step 9: on a scheme $T\to Z'$ it is the identity of $\Gamma(T,\mathcal O_T)$, just as the structural map of step 7. Thus the two morphisms agree as ringed-topos morphisms, not merely as morphisms of underlying topoi.

Cites: lem-trf-slice-subtopos-site-presentation, def-pur-localized-ringed-site.
Source: literature/stacks-project/spaces-properties.tex; Tag 03LP (lemma-etale-morphism-topoi), and Tags 04LY, 04LZ; Sites Tag 03CE (lemma-localize-given-products)

## What remains unfinished

The four new nodes are deliberately unsplit proof work for other workers. The earlier dry run at 7aa08f1d5f6 is retained as history. On this landing-return repair the required initial dry run completed with exit code 0 and printed `OK (not pushed) ... preflight passed` at 88e0babc2e0. The adjusted assembly and this report are submitted to a fresh dry run before the push.


## Landing return L repaired (2026-10-22)

The reader approved the earlier delivery, but landing reported that the side completion had not reached the live DAG. I continued the retained sandbox rather than reconstructing or discarding its proof, citations, search log or handoff arguments. I ran the required initial dry run first; it exited successfully at 88e0babc2e0 against the current origin/sheaf-dag through the prescribed delivery tool.

I also read the current server checkout directly, without a git command or any remote write, and saved the relevant node contents in sandbox-only live-node-comparison.json. The parent and every existing statement dependency of all five delivery nodes are identical to the shared read clone, including the chartwise-etale permanence and representable fibre-product interfaces. The four new package ids remain absent from that checkout. Thus no changed cited statement requires replacement, no duplicate package has landed, and the released stage-1 repair order still calls for this four-package split. The delivery tool reconstructs the commit on current origin/sheaf-dag and preserves its maintainer-owned fields, so no stale completion/review metadata is copied from the sandbox.

I re-read the four package statements against all five citation quotes. Step 1 takes finite limits, the five comparison conditions and literal restriction equivalence; step 2 takes normalized unique extension, natural atlas equalizers and ring/module equivalences; step 3 takes the two normalized rings and the chart-normalized ringed morphism; step 4 takes coherent composition and every part of ringed localization. I checked the unchanged definitions of scheme, algebraic space, scheme-as-space, small universes, site, module sheaf, geometric morphism, ringed-topos morphism, localized ringed site and special cocontinuity, plus the two geometric inputs. Their hypotheses match the four package statements. I read spaces-properties.tex again at 03G0, 03G1, 03H7, 03G2, 03G7, 03G8, 03LP and equations 04LY/04LZ; these establish the same route and include no extra separatedness or representability assumption on f.

I adjusted assembly step 4, correcting the old malformed prime notation and spelling out restriction as inverse image, fibre-product evaluation as direct image, and the normalized identification as structural ring map. This gives a concrete refinement beyond a rebase or unchanged re-push. It preserves the parent statement exactly, keeps the assembly below 3000 characters, and retains all old arguments in this report. No new Mathlib search question or node statement changed, so the existing actual search results and verdicts were reused. citations.json remains verbatim and complete. The empty-space, identity-map and possibly nonrepresentable etale-map checks in Review by Q09 still apply. No Lean, compiler, Lake or agent was started.


## Return L: comparison with returned head and current live DAG

For this retry I first ran the prescribed dry run; it exited 0 with `OK (not pushed)` at 034bbc35948. I then compared the actual returned commit 884bb858092 with the server checkout at d73b0bc8e7c21be4dfc082187b3bb7c16e5895b7 using read-only server operations. The complete comparison is retained in sandbox-only repair-current-returned-comparison.json. All twelve existing dependencies have identical contents. The live parent has the original ten-step proof; the returned delivery has the four-step assembly. The four proposed package ids exist in the returned commit and remain absent from current main. Thus the live tree has not received this side completion, exactly as L reported. The delivery tool rebuilds the repair on current origin/sheaf-dag and preserves current maintainer-owned metadata.

The repair preserves the retained proof, report, source citations, five verbatim step/node quotes and actual search log. It changes assembly step 4 to apply the precise identity, unit and associativity assertions, including structural rings. I checked every cited statement, the chartwise/representable distinction, the smallness assumptions, and the scheme/empty/identity cases described in Review by Q09. No dependency replacement or statement correction is required. All four new nodes remain statement-only, unsplit and of comparable work size; the total assembly remains below 3000 characters and every step below 2000. The unchanged Mathlib searches were read and reused, with no invented or repeated query. A fresh final dry run and push use only the prescribed delivery command.
