## Worker report

Repaired lem-trf-quasi-affine-fpqc-effective-descent for Q07, 2026-10-22. The sandbox was empty at session start, so the current read-only repository node supplied the returned ten-step proof. Its statement, recorded Lean, citations, searches, source and ancestry were retained. No git command was run in the shared repository, no Lean was written, and no compiler was run.

Files written under dag/nodes/sec-trace-formula/:

- lem-trf-quasi-affine-fpqc-effective-descent.json: statement unchanged; seven assembly steps, 2710 characters of proof text.
- lem-trf-canonical-affine-envelope-descent-datum.json: statement, unsplit; no Mathlib match. Carries the canonical envelope, its flat-base-change comparison, the extension of the datum and its triple-overlap cocycle.
- lem-trf-invariant-open-image-pullback.json: statement, unsplit; no Mathlib match. Carries saturation of the invariant open, openness and uniqueness of its image, its cartesian scheme model, and compatibility with any specified ambient effective descent identification.

Both new nodes are statement-only: proof=[], proof_deps=[], proof_origin=null. They have their own complete hypotheses, source and blueprint ancestry, and recorded searches. Other sandbox artifacts are citations.json, searches.jsonl, and this report. repair.py is a sandbox-only preparation script, not part of the delivery.

Attachments: none. Searching the upstream WeilConjectures tree by the item tag and quasi-affine descent found no declaration proving the entire item. The recorded theorem in lean/Sheaf/AlgebraicGeometry/QuasiAffineFpqcDescent.lean ends in sorry, which I read; its ten-step docstring is the returned argument, not evidence of completion. The related upstream EffectiveDescent/Gluing.lean has a proved isEffective_restrict_of_le, but that asserts effectivity of a restriction given an effective datum, not the explicit q(O) model, its unique image subset and its specified cartesian morphism. No new node claims that existing effectivity theorem as an exact attachment.

WANTED: none.

The return concerns granularity, not an error in the statement. No statement dispute or change of unit route was necessary. No SGA source is used.

## Repair of the return

The return requested at least two comparable statement-only nodes, every original argument preserved, and a parent proof of at most 3000 characters. Two independent arguments now become two nodes. The first carries old steps 3 (except the fpqc-cover verification), 4, 5, 6: about 3600 characters of the old proof. The second carries old steps 8, 9, 10 (except the final application of affine reduction): about 2200 characters. These are separate algebraic and geometric arguments. Neither is the item, nor an affine-case restatement of its effectivity conclusion: the first constructs an affine *datum* without descending anything; the second assumes an already available ambient model and has no quasi-affine hypothesis.

Old steps 1 and 2 remain verbatim as parent steps 1 and 2. Old step 3's cover verification remains in parent step 3. Old step 7 remains as parent step 5. The identification of the invariant open remains in parent step 6, which invokes the second node for saturation and the descended open model. Old step 10's final affine-reduction application remains as parent step 7. Thus no argument is removed by the re-split. The complete old ten-step text is transcribed below, with the destination of each argument, so future workers can recover the original calculations while their new nodes remain statement-only.

## Sources and search results

Read descent.tex, Tag 0247, lemma-quasi-affine, all of its proof: reduction to a flat surjective map of affines; canonical relative affine envelope; the flat-base-change display; induced algebra isomorphism and cocycle; effective affine descent; stable open subset and quotient-topology argument. Also read Tag 02W3, lemma-descending-types-morphisms, its three hypotheses and the reduction/gluing proof. The affine-spectrum presentation of the envelope agrees with properties.tex, Tag 01P9, lemma-quasi-affine, whose forward implication and proof I read. The topology used for the second node is morphisms.tex, Tag 02JY, lemma-fpqc-quotient-topology; I read its statement and proof reduction, and use the Stacks proof itself, not its bibliographic references.

For the first new node, I read Mathlib/AlgebraicGeometry/QuasiAffine.lean at the canonical open-immersion instance (line 46) and isPullback_toSpecΓ_toSpecΓ (line 115). The latter assumes an affine morphism between quasi-affine schemes; it constructs a different pullback square and neither extends a descent datum nor proves its cocycle. The search hits for HasAffineProperty.descendsAlong_of_affineAnd concern descent of morphism properties, not construction of a descended scheme or an induced affine-envelope datum. The existing DAG canonical-embedding node already provides the open immersion; it is not recreated.

For the second node I read Mathlib/AlgebraicGeometry/Morphisms/Flat.lean, Flat.isQuotientMap_of_surjective, line 124; PullbackCarrier.lean, Scheme.Pullback.exists_preimage_pullback, line 306; and FlatDescent.lean around the open-property descent statements. They provide ingredients for saturation and openness but do not give the combined invariant-open image, cartesian model and compatibility with a specified datum. The Loogle hits about Topology.IsQuotientMap likewise give only topological ingredients. This requires an argument, not a one-line specialization. The upstream isEffective_restrict_of_le at EffectiveDescent/Gluing.lean:96 gives only the effectivity consequence, not the full statement of the new node.

Each new node has LeanFinder queries in two phrasings, a Loogle query and a grep query run through msearch.py. The first also has a successful LeanSearch query. The second LeanSearch request timed out without a service response and is recorded as unavailable. Searches and their actual result summaries are copied from searches.jsonl; no unrun search is recorded. The item's earlier searches remain intact.

Before creating either node I searched the whole DAG for 0247, affine envelope, affinization, canonical descent datum, invariant open, saturated opens and the relevant upstream declaration names. I ran blueprint_refs.py ancestor on the item, and whole-blueprint searches for 0247, quasi-affine, affine envelope, canonical affine, invariant open, descent datum and global sections. No blueprint node states either result. In particular lem-trf-quasi-affine-relative-spec-embedding gives a factorization, not the affine-envelope cocycle; lem-pd-effective-invariant-open-cover glues given effective local data and does not descend an invariant open in a specified ambient model. The field-extension-specific lem-weil-pbc-galois-base-change-qc-open-descends is finite-stage descent, not this result for an arbitrary flat qc surjective morphism.

## Not duplicates

lem-trf-canonical-affine-envelope-descent-datum vs lem-trf-quasi-affine-fpqc-effective-descent: the new node constructs the canonical affine envelope and its cocycle over a flat surjective map of affines; it neither constructs a B-model nor asserts effective descent of V. Affine effectivity and invariant-open descent are still separate steps of the parent.
lem-trf-invariant-open-image-pullback vs lem-trf-quasi-affine-fpqc-effective-descent: the new node concerns an open immersion into a given scheme W with a flat qc surjective q to an already given W'; it constructs the particular open q(j(V)) and its cartesian pullback. It does not produce an ambient model, assume quasi-affineness, or perform the affine reduction.

## Review by Q07

I checked the statements against Tag 0247 with both new files and the statements of every parent citation open. For the envelope node the affine source and target and flatness of p are essential: they make the double and triple overlap projections flat between affines, while quasi-affineness makes V qcqs. The beta maps use precisely c tensor t mapped to the product of pulled-back sections. The contravariant ring map has direction Gamma(V_1) to Gamma(V_0), so its spectrum goes W_0 to W_1. I checked that the extension identity has direction psi j_0 = j_1 phi and that contravariance converts the given cocycle into psi_02 = psi_12 psi_01. Successive base change and naturality on triple overlaps remain explicit assertions in the node and the original generator calculation is preserved below. They have not been replaced by an unsupported word such as “transports”. No local finite-presentation assumption is used.

For the invariant-open node I checked separately the hypotheses on q: flatness and quasi-compactness alone do not give the quotient topology; surjectivity is present too. Its invariance hypothesis is equality of inverse images in the *scheme* fibre product. For two points over one point the residue-field tensor product has a point, as in the preserved argument; one cannot simply identify the underlying space of a scheme fibre product with the topological fibre product. This gives the fibrewise saturation, then q^{-1}(q(O))=O, then quotient topology gives openness. The open-subscheme pullback gives the cartesian square with its sheaf structure, not just equality of sets. The additional clause starts with a specified ambient identification W = W' times_B A and a specified compatible phi, so the resulting model induces that phi. It does not assume the conclusion of the parent.

Parent step 1 uses the definition of quasi-affineness and the actual statement of lem-trf-quasi-affine-base-change, which has arbitrary base change and no finite-presentation restriction. Isomorphism invariance is definitional. Step 2 uses the scheme-coproduct node's clopen component conclusion, the clopen-idempotent node's D(e) description, the principal-localization node's affine domain and image, the definition of quasi-affine, and clause (4) of affine-morphism-permanence. These statements do say what the step uses. The union is finite and therefore quasi-compact. The empty case is explicitly Spec(0); no finite-type hypothesis is smuggled in.

Parent step 3 uses affine-scheme-qcqs, qcqs-morphism-permanence (1), and the fpqc-cover definition. The target is quasi-separated and source quasi-compact because both are affine; the quasi-compactness conclusion is not inferred from an arbitrary singleton fpqc covering. Every inverse image of an affine open is quasi-compact, so a finite affine cover gives the required covering condition. Step 4 uses exactly the new envelope statement: it provides all of the open immersion, affine ambient morphism, extension identity and cocycle, not merely the existence of an embedding.

Parent step 5 invokes the affine-effectivity statement only after obtaining a genuine affine datum and the fpqc covering. It then uses flat base change, surjective base change and qcqs-morphism-permanence (3) to verify all three hypotheses on q. The affine-effectivity node does not promise W' affine, so the step deliberately needs no such assertion. Parent step 6 uses the open-immersion base-change statement, the fibre-product universal property and the open-immersion definition to identify the two open subschemes with r_i^{-1}O. Compatibility of the specified ambient datum implies their equality. The second new node now supplies the image U, its cartesian model and exact compatibility with phi; all of those clauses are stated. Step 7 uses the full three-condition statement of the fpqc-reduction lemma, with the conditions verified in the preceding steps. The two pre-existing off-unit tools remain declared as before; no new route is taken. citations.json contains a verbatim statement quotation for each citation at each numbered parent step.

Small cases: V empty gives C=0, an empty affine envelope and the empty image U. Identity p gives the canonical datum and recovers V. Empty affine bases force an empty source and do not require excluding the zero ring. For the second node O empty gives U empty, O=W gives U=W' using surjectivity, and identity q gives U=O. W' can be non-affine and V need not be quasi-compact. No step uses affineness of intersections on a merely quasi-separated scheme. The zero-component coproduct case remains in the parent. The uniqueness assertion for U follows from surjectivity, and the uniqueness of h follows from the open immersion being a monomorphism.

I checked B1–B10: new nodes contain no proof or proof sketch, introduce every object, cite or spell out the notions, use single-escaped TeX, use the actual Stacks label and tag, and do not claim a Mathlib match. C1–C8: every non-elementary fact in the parent is supplied by a cited statement; the envelope and open-model subarguments are now independent nodes; generic descent tools are retained in split_report rather than editing maintainer-owned tool_uses. D1–D5: neither new node is the item or a bare restatement of its conclusion, and the assembly still applies affine effectivity and reduction. E1–E7: checked flatness, affineness, qcqs and surjectivity at their actual uses, ring-map directions, scheme fibre products, and compatibility with the given datum. No mathematical correction was needed. The correction requested by the return is the two-node re-split itself, with the original proof retained below.

## Preserved returned proof and transfer map

The following paragraphs are the returned proof verbatim, retained as work instructions for future splitters. They are not proof fields of the new statement-only nodes.

### Old step 1 → Parent step 1

Use the property $\mathcal P(f)$ that $f$ is quasi-affine in the stated sense. It is invariant under isomorphism directly from the definition, and is stable under arbitrary base change by [lem-trf-quasi-affine-base-change]. This verifies condition (1) of the reduction lemma used in the last step.

Citations: def-nagata-quasi-affine-morphism, lem-trf-quasi-affine-base-change

### Old step 2 → Parent step 2

For a finite family $f_i:Y_i\to T_i$ with $\mathcal P$, let $T=\coprod_iT_i$. The component images are clopen by [lem-weil-pbc-scheme-coproduct-family]. If $H\subset T$ is affine open, $H_i=H\cap T_i$ is clopen in the affine scheme $H$, hence equals a principal open $D(e_i)$ by [lem-weil-pbc-spec-clopen-idempotent], and is affine by [lem-weil-pbc-principal-localization-open-immersion]. Thus $f_i^{-1}(H_i)$ is a quasi-compact open in some affine scheme $Z_i$, by quasi-affineness. Their finite disjoint union is a quasi-compact open in the affine scheme $\coprod_i Z_i$ by [lem-weil-pbc-affine-morphism-permanence](4); it is precisely the inverse image of $H$. For no components the source and target are empty, and the same assertion holds with $\operatorname{Spec}(0)$. This proves condition (2) of the reduction lemma.

Citations: lem-weil-pbc-scheme-coproduct-family, lem-weil-pbc-spec-clopen-idempotent, lem-weil-pbc-principal-localization-open-immersion, def-nagata-quasi-affine-morphism, lem-weil-pbc-affine-morphism-permanence, def-weil-affine-spectrum

### Old step 3 → Cover verification: parent step 3; envelope construction: canonical-affine-envelope-descent-datum

We prove condition (3) for an arbitrary flat surjective morphism $p:A=\operatorname{Spec}S\to B=\operatorname{Spec}R$ and the given quasi-affine $V\to A$. Affine schemes are qcqs by [lem-weil-pbc-affine-scheme-qcqs], so $p$ is quasi-compact by [lem-weil-pbc-qcqs-morphism-permanence](1). This singleton is an fpqc covering: for every affine open $H\subset B$, its inverse image is quasi-compact, so finitely many affine opens of it cover it, and their images cover $H$ by surjectivity, as required by [def-weil-pbc-fpqc-covering]. Since $A$ itself is affine, $V$ is a quasi-affine scheme. Put $C=\Gamma(V,\mathcal O_V)$ and $W=\operatorname{Spec}C$. By [lem-trf-quasi-affine-canonical-affine-embedding], $V$ is qcqs and $j:V\to W$ is an open immersion. The ring map $S\to C$ defines $W\to A$, and $j$ is over $A$ because both composites $V\to A$ correspond to that same ring map by [lem-weil-pbc-morphism-into-affine-scheme]. The morphism $W\to A$ is affine by [lem-weil-pbc-morphism-affine-schemes-affine].

Citations: lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence, def-weil-pbc-fpqc-covering, def-nagata-quasi-affine-morphism, lem-trf-quasi-affine-canonical-affine-embedding, lem-weil-pbc-morphism-into-affine-scheme, lem-weil-pbc-morphism-affine-schemes-affine

### Old step 4 → canonical-affine-envelope-descent-datum

Write $A_2=A\times_B A$, with projections $p_i$, and $V_i=V\times_{A,p_i}A_2$, $W_i=W\times_{A,p_i}A_2$, for $i=0,1$. These projections are flat by [lem-weil-pbc-flat-morphism-base-change], and $A_2$ is affine by [lem-weil-pbc-fibre-product-affine-spectra]. Apply [lem-weil-pbc-flat-base-change-global-sections-qcqs] with $X=V$, $S=A$, $S\prime=A_2$: its qcqs hypothesis is Step 3. If $S_2=\Gamma(A_2,\mathcal O)$, it gives isomorphisms $C\otimes_{S,p_i^\sharp}S_2\simeq\Gamma(V_i,\mathcal O)$ with formula $c\otimes t\mapsto c|_{V_i}\,t|_{V_i}$. The affine fibre-product formula therefore identifies $W_i$ canonically with $\operatorname{Spec}\Gamma(V_i,\mathcal O)$. Under this identification the base change $j_i:V_i\to W_i$ is the canonical map: both maps to the affine $W_i$ send $c\otimes t$ to $c|_{V_i}\,t|_{V_i}$, so equality follows from [lem-weil-pbc-morphism-into-affine-scheme].

Citations: lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-flat-base-change-global-sections-qcqs, lem-weil-pbc-morphism-into-affine-scheme

### Old step 5 → canonical-affine-envelope-descent-datum

The datum $\phi:V_0\simeq V_1$ over $A_2$ induces an $S_2$-algebra isomorphism $\phi^\sharp:\Gamma(V_1,\mathcal O)\simeq\Gamma(V_0,\mathcal O)$. Apply the contravariant affine-spectrum functor [def-weil-affine-spectrum] and conjugate by Step 4 to obtain $\psi:W_0\simeq W_1$ over $A_2$. It extends $\phi$: $\psi j_0=j_1\phi$, since these maps into the affine $W_1$ induce the same ring map $\phi^\sharp$ on global sections, by [lem-weil-pbc-morphism-into-affine-scheme].

Citations: def-weil-affine-spectrum, lem-weil-pbc-morphism-into-affine-scheme

### Old step 6 → canonical-affine-envelope-descent-datum

Check the cocycle on $A_3=A\times_B A\times_B A$. The maps $A_3\to A_2$ and $A_3\to A$ are flat by successive applications of [lem-weil-pbc-flat-morphism-base-change] (each forgets one or two factors of the flat map $p$), and their sources are affine by [lem-weil-pbc-fibre-product-affine-spectra]. The pullbacks of $V$ are qcqs by [lem-weil-pbc-qcqs-morphism-permanence], applied over the affine qcqs schemes using Step 3. Thus [lem-weil-pbc-flat-base-change-global-sections-qcqs] applies both from $A$ and from $A_2$. Its identifications commute with the ring maps induced by $\phi$: on each tensor generator $a\otimes t$ both orders send it to the pullback of $\phi^\sharp(a)$ times the pulled-back scalar $t$. The successive-base-change identifications also agree, since both send $(c\otimes s)\otimes t$ to the product of the three pulled-back sections. Consequently the pullback of $\psi$ along each $A_3\to A_2$ is the affine spectrum of the ring map induced by that pullback of $\phi$. Contravariant functoriality [def-weil-affine-spectrum] and the cocycle $\phi_{02}=\phi_{12}\phi_{01}$ give $\psi_{02}=\psi_{12}\psi_{01}$. Hence $(W,\psi)$ is a descent datum and $j$ is a morphism of descent data [def-pd-descent-datum].

Citations: lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-flat-base-change-global-sections-qcqs, def-weil-affine-spectrum, def-pd-descent-datum

### Old step 7 → Parent step 5

Apply [lem-galois-fpqc-affine-descent-effective] to the affine morphism $W\to A$ and datum $\psi$, using the fpqc singleton checked in Step 3. Obtain $W\simeq W\prime\times_B A$ compatibly with descent data, for a scheme $W\prime\to B$. Let $q:W\to W\prime$ be the projection. It is flat and surjective by [lem-weil-pbc-flat-morphism-base-change] and [lem-weil-pbc-surjective-base-change]; it is quasi-compact by [lem-weil-pbc-qcqs-morphism-permanence](3), since $p$ is quasi-compact. No affineness assertion about $W\prime$ is needed.

Citations: lem-galois-fpqc-affine-descent-effective, lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-surjective-base-change, lem-weil-pbc-qcqs-morphism-permanence

### Old step 8 → Invariant-open-image-pullback, with invariance verified in parent step 6

Let $O=j(V)\subset W$. Under the identification $W=W\prime\times_B A$, the two maps $r_0,r_1:W\times_{W\prime}W\to W$ correspond to the two pullbacks over $A_2$, with their identification given by $\psi$; this is the compatibility in Step 7 and the universal property [def-pc-fibre-product]. Since $\psi j_0=j_1\phi$ and $\phi$ is an isomorphism, $r_0^{-1}O=r_1^{-1}O$. Here the images of $j_i$ are the inverse images of $O$: pullbacks of open immersions are open immersions by [lem-weil-pbc-open-immersion-base-change], and the universal property identifies them with the inverse-image open subschemes [def-weil-open-immersion].

Citations: def-pc-fibre-product, lem-weil-pbc-open-immersion-base-change, def-weil-open-immersion

### Old step 9 → Invariant-open-image-pullback

The equality in Step 8 implies that $O$ is a union of fibres of $q$. Indeed, if $q(x)=q(y)=z$, the spectrum of $\kappa(x)\otimes_{\kappa(z)}\kappa(y)$ is nonempty: it is the base change of the surjection $\operatorname{Spec}\kappa(x)\to\operatorname{Spec}\kappa(z)$ to the one-point scheme $\operatorname{Spec}\kappa(y)$, so [lem-weil-pbc-surjective-base-change] and [lem-weil-pbc-fibre-product-affine-spectra] apply. By [lem-weil-pbc-fibre-product-points] a point of this spectrum gives $t\in W\times_{W\prime}W$ with $r_0(t)=x,r_1(t)=y$. Step 8 then gives $x\in O\iff y\in O$. Set $U=q(O)\subset W\prime$; hence $q^{-1}U=O$. Since $q$ is flat, quasi-compact and surjective (Step 7), [lem-weil-pbc-flat-qc-surjective-quotient-map] shows that $U$ is open.

Citations: def-weil-affine-spectrum, lem-weil-pbc-surjective-base-change, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-fibre-product-points, lem-weil-pbc-flat-qc-surjective-quotient-map

### Old step 10 → Open-model part: invariant-open-image-pullback; reduction: parent step 7

Give $U$ its open-subscheme structure in $W\prime$ and its composite map to $B$. Its base change to $A$ is the open subscheme $q^{-1}U=O$ of $W$, by [lem-weil-pbc-open-immersion-base-change] and the fibre-product universal property. The open immersion $j$ identifies $V$ with this open subscheme by [def-weil-open-immersion], giving $U\times_B A\simeq V$. On $A_2$ its canonical descent identification is the restriction of $\psi$, which by Step 5 is precisely $\phi$. Thus the isomorphism induces the specified datum [def-pd-descent-datum]. This proves condition (3). Finally apply [lem-galois-fpqc-descending-types-morphisms], with conditions (1), (2), (3) supplied by Steps 1, 2, 3–10. Its conclusion gives $V_0\to B$ and the required compatible isomorphism for the original, arbitrary singleton fpqc cover. None of the steps assumed local finite presentation.

Citations: lem-weil-pbc-open-immersion-base-change, def-pc-fibre-product, def-weil-open-immersion, def-pd-descent-datum, lem-galois-fpqc-descending-types-morphisms
