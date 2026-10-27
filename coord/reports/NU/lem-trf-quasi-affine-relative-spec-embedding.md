# Stage-1 repair: lem-trf-quasi-affine-relative-spec-embedding

## Files written

- dag/nodes/sec-trace-formula/lem-trf-quasi-affine-relative-spec-embedding.json: item, split; statement unchanged; 1842 characters of proof assembly.
- dag/nodes/sec-trace-formula/lem-trf-qcqs-relative-affinization-map.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-canonical-affine-charts-qc-open-immersion.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-qcqs-affine-preimage-criterion.json: statement-only Mathlib leaf, one declaration per clause.
- citations.json: every citation of every item step, with verbatim quoted statements.

## Attachments

None. The theorem in lean/Sheaf/AlgebraicGeometry/QuasiAffineRelativeSpecEmbedding.lean has `sorry`. Searches of lean/WeilConjectures by the blueprint tag and by the relative quasi-affine notion found no finished exact declaration. The absolute canonical immersion is already owned by lem-trf-quasi-affine-canonical-affine-embedding.

## WANTED

None; all sources are present.

## What was wrong and what was repaired

The returned proof carried six arguments totaling 5229 characters in one node. At session start the sandbox contained only dispatcher .brief files: no node, report, citations or searches. I copied the current shared-repository item as the mathematical baseline, retaining its statement, existing searches and source/blueprint/maintainer fields. This worker wrote only in the sandbox, ran no git command in the repository, and wrote no Lean or compiler/build input.

The two substantial unsplit tasks now are relative affinization for arbitrary qcqs morphisms (old steps 2-3, 2051 characters) and passage from canonical quasi-affine charts to a globally qc open immersion (old steps 4-5, 1477 characters). The initial diagonal-cover argument (old step 1, 927 characters) is subsumed by a general Mathlib affine-preimage criterion, delivered as a leaf, not left as another unacknowledged argument. The converse (old step 6) remains verbatim. Every old argument is preserved below and assigned its new owner. Nothing has been blurred into a shorter unsupported assertion. No statement dispute was found. The harmless O_X/O_S algebra-base typo in the proof of 01SM was already corrected in the unchanged item.

## Unfinished work

The two new unsplit lemmas intentionally have empty proof and proof_deps and null proof_origin; other workers can start their proofs independently. The relative-affinization lemma does not assume quasi-affineness or prove an embedding. The canonical-chart lemma assumes an existing map and chart identities and constructs neither the algebra nor the map. Thus neither restates the item or its forward implication.

## Review by NU

I read morphisms.tex Tag 01SM (lemma-characterize-quasi-affine), all implications and the full proof; constructions.tex Tag 01LY (lemma-canonical-morphism), statement and proof; and the preceding 01LX relative-spectrum properties. For the qcqs criterion I read schemes.tex Tags 01K4 (lemma-quasi-compact-affine) and 01KO (lemma-characterize-quasi-separated), with their proofs. I checked the tag-to-label table. For each new node its source is exactly the portion of these texts just described, with 01LY giving the full first lemma and the final part of 01SM giving the chart-to-global argument of the second. The third is the combination of 01K4 and 01KO, recognized directly in Mathlib.

Step 1 uses lem-trf-quasi-affine-canonical-affine-embedding for BOTH quasi-compactness and quasi-separatedness of every X_U; I opened its statement, which explicitly gives both. It then uses the new qcqs-affine-preimage-criterion, whose hypotheses are precisely those two properties on every affine inverse image. All affine opens are used, so neither compactness of S nor a finite affine base cover is needed. The old diagonal-cover proof is copied below, and the Mathlib criterion supplies its entire conclusion. I read Mathlib Morphisms/QuasiCompact.lean:97-98, Morphisms/Basic.lean:449-450,497 and Morphisms/QuasiSeparated.lean:107-110,133-135: they give one declaration per clause, including the actual inferred HasAffineProperty instance. The latter says QuasiSeparated is equivalent to QuasiSeparatedSpace of the source on each affine restriction, not that every map to an affine scheme is quasi-separated (one informal search-result description was wrong; its actual type and source were checked).

Step 2 uses only the statement of the new relative-affinization lemma. It explicitly supplies the quasi-coherent algebra, affine relative spectrum, c over S, and each chart identity h_U c_U = j_X_U. This is not a reference to its future proof. Its qcqs input is supplied in step 1. The direct-image algebra has its actual multiplication and structural map. No affine source, affine overlap, Noetherian or finite-type hypothesis is introduced. The old construction, compatible local maps, gluing, section calculation a_U^{-1}a_U = id and injectivity of the Hom-into-affine correspondence are preserved below for its future worker. I also opened pqf-lem-pushforward-qcoh, lem-weil-pbc-affine-morphism-relative-spec, lem-weil-pbc-affine-algebra-local-maps, lem-weil-pbc-scheme-morphism-gluing and lem-weil-pbc-morphism-into-affine-scheme: they state exactly the operations the preserved argument uses, and the local-maps theorem permits arbitrary source and nonaffine overlaps.

Step 3 uses the new canonical-chart lemma with the actual c and h_U of step 2. Its affine-pi, quasi-affine-X_U, and h_U c_U = j_X_U hypotheses have all been supplied before the application. Its conclusions include BOTH open immersion and relative quasi-compactness. I checked the old argument against the statements of lem-trf-quasi-affine-canonical-affine-embedding, def-weil-open-immersion, lem-weil-pbc-open-immersion-injective-local-source, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence and lem-pc-quasi-compact-local-on-target. The first identifies each j_X_U as an open immersion. Equality of two global images places both points in one X_U, proving injectivity before applying injective-local-source. Compactness is separately checked on the Y_U cover, using affine Y_U and compact X_U; the map's inverse image of Y_U is exactly X_U because pi c = f. No compactness of S or Y is used. This is a separate argument of comparable size to the first unsplit task, and not a clause merely renamed.

Step 4 is the unchanged elementary reverse implication. I opened each of its four cited statements. Relative-spec clause (2) makes Y_U affine; the open-immersion definition identifies restrictions with open subschemes; the finite-type-morphism definition explicitly defines quasi-compactness by inverse images of affine opens; the quasi-affine-morphism definition gives the conclusion, with the absolute meaning fixed in the item. All four quotes are verbatim in citations.json. No non-elementary assertion is hidden in that elementary step.

I checked delivery-errors B-E point by point. New nodes are self-contained statements with definitions of their notions inline or cited, ordinary TeX, precise Stacks tags/labels, no proof sketch, and no proof dependencies. Every actual Mathlib search is copied from searches.jsonl with its exact query and result digest; unavailable LeanSearch is labeled unavailable, never no match. Second semantic phrasings were tried and their hits read. The absolute Gamma-Spec map, the affine structure-algebra anti-equivalence, and the relative Proj section-algebra definition do not state the new lemmas. The whole-DAG, tag and blueprint searches found no exact duplicate; the same-tag neighbours are distinguished below. Every item citation uses a statement, not its proof or a definition misused as a theorem. New nodes do not depend on the item, and their statement dependencies only define their objects, so the extraction creates no cycle. All proof steps are below 2000 characters. No SGA source is used and the unit route is unchanged. The only off-unit statement still used directly is the existing generic relative-spectrum tool in the converse, declared in split_report.tool_uses; maintainer tool_uses were left untouched.

Small cases were checked: empty X has the zero direct-image algebra and empty relative spectrum; empty S forces X and Y empty and all chart assumptions are vacuous. An affine f gives an isomorphism as canonical map, allowed by the chart lemma. Punctured affine two-space gives an open non-surjective canonical map, also allowed. An infinite disjoint union of affine bases explains why absolute compactness cannot be assumed for S, X or Y, while every required map is still relatively quasi-compact. No finite-type, finite-presentation, Noetherian or separation hypothesis on S is used. None of the statements claims surjectivity of the embedding.

## Not duplicates

- lem-trf-canonical-affine-charts-qc-open-immersion vs lem-a1-quasi-affine-target-locality: the existing lemma tests relative quasi-affineness on a base cover, without a given c or canonical chart isomorphisms; the new lemma proves qc open immersion of a fixed c.
- lem-trf-canonical-affine-charts-qc-open-immersion vs lem-trf-quasi-affine-relative-spec-embedding: the new lemma starts with pi, c and h_U satisfying canonical chart identities and proves geometric properties of this fixed c; the item constructs these data and proves an equivalence. The new lemma supplies neither the algebra nor c.
- lem-trf-qcqs-affine-preimage-criterion vs def-weil-quasi-separated-morphism: the new Mathlib leaf infers relative qcqs from all affine inverse images; it defines a property using the diagonal; it does not prove the affine-preimage criterion.
- lem-trf-qcqs-affine-preimage-criterion vs lem-pc-field-extension-quasi-compact: the new Mathlib leaf infers relative qcqs from all affine inverse images; it proves compactness of a field-extension map, not the arbitrary-base qcqs criterion.
- lem-trf-qcqs-affine-preimage-criterion vs lem-weil-pbc-affine-scheme-qcqs: the new Mathlib leaf infers relative qcqs from all affine inverse images; it proves a single affine scheme qcqs, not a relative affine-preimage criterion.
- lem-trf-qcqs-affine-preimage-criterion vs lem-weil-pbc-etale-limit-tail-open-geometry: the new Mathlib leaf infers relative qcqs from all affine inverse images; it is an assertion about restricted inverse-system limits, not a criterion for arbitrary f.
- lem-trf-qcqs-affine-preimage-criterion vs lem-weil-pbc-finite-coproduct-lfp-qcqs: the new Mathlib leaf infers relative qcqs from all affine inverse images; it proves finite-coproduct permanence, not a relative affine-preimage criterion.
- lem-trf-qcqs-affine-preimage-criterion vs lem-weil-pbc-finite-presentation-hom-directed-colimit: the new Mathlib leaf infers relative qcqs from all affine inverse images; it concerns Hom from finitely presented modules commuting with colimits, not morphism qcqs.
- lem-trf-qcqs-affine-preimage-criterion vs lem-weil-pbc-qcqs-over-affine: the new Mathlib leaf infers relative qcqs from all affine inverse images; it derives absolute qcqs of X from a qcqs map to one affine Y, the opposite direction over a restricted base.
- lem-trf-qcqs-affine-preimage-criterion vs lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings: the new Mathlib leaf infers relative qcqs from all affine inverse images; it constructs cofinal finite covers of an already qcqs scheme, not a criterion for a scheme morphism.
- lem-trf-qcqs-affine-preimage-criterion vs lem-weil-pbc-quasi-compact-morphism-preimage-qc-open: the new Mathlib leaf infers relative qcqs from all affine inverse images; it starts with a qc map and extends the compact-inverse-image property to qc opens; it does not infer qcqs from affine inverse images.
- lem-trf-qcqs-affine-preimage-criterion vs lem-weil-pbc-quasi-separated-affine-cover-criterion: the new Mathlib leaf infers relative qcqs from all affine inverse images; it tests quasi-separatedness of a scheme by its affine intersections; it does not test relative qcqs of arbitrary f on inverse images of base affines.
- lem-trf-qcqs-relative-affinization-map vs def-fd-artin-schreier-function-cover: the existing statement concerns The function Artin–Schreier cover, its root, constants and induced fibre map; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs def-pur-rees-cone-normalization: the existing statement concerns Degree-one normalized comparison predicate; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-pur-conormal-cone-hom-ext: the existing statement concerns Degree-one uniqueness for maps to conormal spectra; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-pur-conormal-graded-algebra-hom-ext: the existing statement concerns Degree-one uniqueness for conormal algebra morphisms; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-pur-conormal-zero-section-pullback: the existing statement concerns The relative-Spec conormal zero section pulls back by augmentation; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-pur-rees-associated-graded-chart: the existing statement concerns Homogeneous chart for the extended Rees zero fibre; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-pur-rees-cone-normalized-existence: the existing statement concerns Homogeneous-normalized Rees cone comparison exists; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-affine-base-change-sections-induction: the existing statement concerns Generation of affine base-change sections; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-affine-basis-ring-action-gluing: the existing statement concerns Extension of compatible ring actions from affine opens; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-affine-morphism-relative-spec: the existing anti-equivalence constructs the relative spectrum from an algebra but gives morphisms only between affine S-schemes; the new lemma constructs the map from arbitrary qcqs X and identifies it on all base charts.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-affine-structure-algebra-fully-faithful: the new lemma constructs a canonical map from an arbitrary qcqs source into its relative affinization, with affine chart identities; the existing lemma is full faithfulness for sources already affine over S.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-balanced-action-affine-open: the existing statement concerns Unique balanced action on a single affine open; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-balanced-action-affine-sections: the existing statement concerns Balanced actions on affine sections of the direct-image algebra; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-balanced-action-direct-image-module: the existing statement concerns Extension of a balanced action to the direct-image structure algebra; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-balanced-action-quasicoherent-realization: the existing statement concerns Quasi-coherent realization of a balanced algebra action; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-graded-finiteness-cohomology: the existing statement concerns Cohomology of a finite type graded module over f^*B~ is a finite B-module; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-relative-spec-base-change: the existing statement concerns Relative Spec commutes with base change; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-relative-spec-morphism-chart: the existing statement concerns Relative spectrum morphism chart compatibility; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-relative-spectrum-affine-realization: the existing statement concerns Affine realization of a quasi-coherent algebra; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.
- lem-trf-qcqs-relative-affinization-map vs lem-weil-pbc-relative-spectrum-structure-algebra: the existing statement concerns Structure algebra from compatible affine spectral charts; it does not construct the relative-affinization map from arbitrary qcqs X with its canonical chart identities.

## Original arguments and their new owners

These are the exact original proof texts, retained as handoff material in this report, not as proof steps or proof sketches in the new statement-only nodes.

### Old step 1: lem-trf-qcqs-affine-preimage-criterion

Assume $f$ is quasi-affine. For every affine open $U\subseteq S$, put $X_U=f^{-1}(U)$. By [lem-trf-quasi-affine-canonical-affine-embedding], $X_U$ is quasi-compact and quasi-separated. Thus $f$ is quasi-compact by [def-weil-finite-type-morphism]. It is also quasi-separated: [lem-weil-pbc-qcqs-morphism-permanence](1) makes $f_U:X_U\to U$ quasi-separated since its source is quasi-separated. The open subschemes $V_U=X_U\times_U X_U$ cover $X\times_S X$: a pair over a point $s$ belongs to $V_U$ whenever $s\in U$. The inverse image of $V_U$ under $\Delta_f$ is $X_U$, and the restricted diagonal is $\Delta_{f_U}$, because both components are the identity on $X_U$. These restricted diagonals are quasi-compact by [def-weil-quasi-separated-morphism]. Apply [lem-pc-quasi-compact-local-on-target] to the cover $(V_U)_U$ and $\Delta_f$. It follows that $\Delta_f$ is quasi-compact, which is precisely quasi-separatedness of $f$.

Cited nodes: lem-trf-quasi-affine-canonical-affine-embedding, def-weil-finite-type-morphism, lem-weil-pbc-qcqs-morphism-permanence, def-weil-quasi-separated-morphism, lem-pc-quasi-compact-local-on-target.

Source: literature/stacks-project/morphisms.tex, Tag 01SM, lemma-characterize-quasi-affine, (2) implies (4): quasi-compactness and quasi-separatedness; Schemes Tags 01K4 and 01KO.

### Old step 2: lem-trf-qcqs-relative-affinization-map

Set $\mathcal A=f_*\mathcal O_X$. The structure sheaf is quasi-coherent: on an affine chart $\operatorname{Spec}R$ it is the associated sheaf $\widetilde R$, as in [pqf-def-coherent]. Step 1 supplies both hypotheses of [pqf-lem-pushforward-qcoh], so the underlying module of $\mathcal A$ is quasi-coherent. Its ring multiplication and its $\mathcal O_S$-algebra structure are those of the direct-image structure sheaf. Apply [lem-weil-pbc-affine-morphism-relative-spec](2). Obtain the affine morphism $\pi:Y=\underline{\operatorname{Spec}}_S(\mathcal A)\to S$ and an algebra isomorphism $a:\mathcal A\xrightarrow{\sim}\pi_*\mathcal O_Y$. For every affine open $U\subseteq S$, put $Y_U=\pi^{-1}(U)$; the chart $h_U:Y_U\xrightarrow{\sim}\operatorname{Spec}\mathcal A(U)$ has section map $a_U$.

Cited nodes: pqf-def-coherent, pqf-lem-pushforward-qcoh, lem-weil-pbc-affine-morphism-relative-spec.

Source: literature/stacks-project/morphisms.tex, Tag 01SM, lemma-characterize-quasi-affine, (2) implies (4): construction of the algebra and relative spectrum; Schemes Tag 01LC and Constructions Tag 01LX.

### Old step 3: lem-trf-qcqs-relative-affinization-map

Apply [lem-weil-pbc-affine-algebra-local-maps] with $g=\pi$ and the algebra map $a^{-1}:\pi_*\mathcal O_Y\to f_*\mathcal O_X$. This is allowed because $\pi$ is affine; no affineness of $X$ or of an overlap is required. It gives maps $k_U:X_U\to Y$ over $S$ agreeing on every overlap. By [lem-weil-pbc-scheme-morphism-gluing], they glue to $c:X\to Y$. Their composites with $\pi$ agree with $f$ on every $X_U$, so uniqueness in that same gluing theorem gives $\pi c=f$. Each $k_U$ factors through the open $Y_U$, since its composite to $S$ has image in $U$; denote the resulting map by $c_U:X_U\to Y_U$. This factorization simply restricts the continuous map and the sheaf map to the indicated open subscheme. The section formula in the local-maps node says that $c_U$ induces $a_U^{-1}:\Gamma(Y_U,\mathcal O_Y)\to\mathcal A(U)=\Gamma(X_U,\mathcal O_X)$. Hence $h_Uc_U:X_U\to\operatorname{Spec}\Gamma(X_U,\mathcal O_X)$ induces $a_U^{-1}a_U=\mathrm{id}$. Injectivity of the correspondence [lem-weil-pbc-morphism-into-affine-scheme] identifies this composite with the canonical map defined by the identity on global sections. This is the affine-restriction description of the canonical map in Constructions Tag 01LY, now constructed from existing DAG statements.

Cited nodes: lem-weil-pbc-affine-algebra-local-maps, lem-weil-pbc-scheme-morphism-gluing, lem-weil-pbc-affine-morphism-relative-spec, lem-weil-pbc-morphism-into-affine-scheme.

Source: literature/stacks-project/morphisms.tex, Tag 01SM, lemma-characterize-quasi-affine, (2) implies (4): canonical morphism; Constructions Tag 01LY, lemma-canonical-morphism, with Tag 01LT.

### Old step 4: lem-trf-canonical-affine-charts-qc-open-immersion

Every $X_U$ is quasi-affine, so [lem-trf-quasi-affine-canonical-affine-embedding] makes its canonical map to $\operatorname{Spec}\Gamma(X_U,\mathcal O_X)$ an open immersion. Step 3 identifies this with $h_Uc_U$; since $h_U$ is an isomorphism, $c_U$ is an open immersion. By [def-weil-open-immersion], composing with the inclusion of $Y_U$ into $Y$ is again an open immersion: the composite identifies $X_U$ with an open subset of the open subset $Y_U$ and its sheaf map is a composite of isomorphisms. Also $c$ is injective on points: if $c(x)=c(x')=y$, choose an affine open $U$ containing $\pi(y)$. Then $x,x'\in X_U$, and injectivity of $c_U$ gives $x=x'$. The opens $X_U$ cover $X$, and their maps into $Y$ are the just-checked open immersions. Therefore [lem-weil-pbc-open-immersion-injective-local-source] applies and makes $c$ an open immersion.

Cited nodes: lem-trf-quasi-affine-canonical-affine-embedding, def-weil-open-immersion, lem-weil-pbc-open-immersion-injective-local-source.

Source: literature/stacks-project/morphisms.tex, Tag 01SM, lemma-characterize-quasi-affine, (2) implies (4): canonical map is an open immersion, using Properties Tag 01P9.

### Old step 5: lem-trf-canonical-affine-charts-qc-open-immersion

The open immersion $c$ is quasi-compact as a morphism, even when $S$ itself is not quasi-compact. Indeed the affine opens $U\subseteq S$ give an open cover $(Y_U)_U$ of $Y$, and $c^{-1}(Y_U)=X_U$ by $\pi c=f$. The scheme $X_U$ is quasi-compact by step 1 and $Y_U$ is affine by [lem-weil-pbc-affine-morphism-relative-spec](2), hence quasi-separated by [lem-weil-pbc-affine-scheme-qcqs]. Apply [lem-weil-pbc-qcqs-morphism-permanence](1) to obtain quasi-compactness of $c_U:X_U\to Y_U$. Then [lem-pc-quasi-compact-local-on-target] makes $c$ quasi-compact. Taking $i=c$ proves the required factorization in the forward direction.

Cited nodes: lem-weil-pbc-affine-morphism-relative-spec, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence, lem-pc-quasi-compact-local-on-target.

Source: literature/stacks-project/morphisms.tex, Tag 01SM, lemma-characterize-quasi-affine, end of (2) implies (4): quasi-compactness of the canonical open immersion.

### Old step 6: unchanged elementary converse, item step 4

Conversely, suppose $\mathcal A,\pi:Y\to S,i:X\hookrightarrow Y$ satisfy the stated factorization. For any affine open $U\subseteq S$, [lem-weil-pbc-affine-morphism-relative-spec](2) identifies $Y_U=\pi^{-1}(U)$ with an affine scheme. The equation $\pi i=f$ gives $f^{-1}(U)=i^{-1}(Y_U)$. By [def-weil-open-immersion], restricting $i$ identifies this scheme with an open subscheme of $Y_U$. Because $Y_U$ is an affine open of $Y$, quasi-compactness of $i$, in [def-weil-finite-type-morphism], says exactly that $i^{-1}(Y_U)$ is quasi-compact. Thus $f^{-1}(U)$ is isomorphic to a quasi-compact open subscheme of an affine scheme. This holds for every affine open $U$, and hence $f$ is quasi-affine by [def-nagata-quasi-affine-morphism] with the meaning specified in the item.

Cited nodes: lem-weil-pbc-affine-morphism-relative-spec, def-weil-open-immersion, def-weil-finite-type-morphism, def-nagata-quasi-affine-morphism.

Source: literature/stacks-project/morphisms.tex, Tag 01SM, lemma-characterize-quasi-affine, (3) implies (1), using Constructions Tag 01LX.

## Validation

First required dry run exited with one metadata diagnostic: the Mathlib leaf needed a numeric mathlib_match.line field in addition to the verified line references in how. Added line = 97; source and statement unchanged. The second required dry run exited successfully: OK (not pushed) at 2b7a87b4619, preflight passed. Local JSON, statement-dependency, citation, unchanged-statement/converse, empty-proof-on-new-nodes and proof-length checks also passed. The assembly has 1842 characters; two new nodes remain unsplit and one is a Mathlib leaf.
